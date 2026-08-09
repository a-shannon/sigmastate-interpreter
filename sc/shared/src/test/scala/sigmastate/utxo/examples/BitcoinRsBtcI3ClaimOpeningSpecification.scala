package sigmastate.utxo.examples

import org.ergoplatform.ErgoBox.Token
import org.ergoplatform.ErgoBox.{NonMandatoryRegisterId, R4, R5, R6, R7, R8, R9}
import org.ergoplatform._
import scorex.crypto.hash.Blake2b256
import scorex.util.ModifierId
import scorex.util.encode.Base16
import sigma.Extensions.ArrayOps
import sigma.VersionContext
import sigma.VersionContext.V6SoftForkVersion
import sigma.ast.ErgoTree.ZeroHeader
import sigma.ast._
import sigma.ast.syntax._
import sigma.data.Digest32Coll
import sigma.interpreter.{ContextExtension, ProverResult}
import sigmastate._
import sigmastate.crypto.DLogProtocol.DLogProverInput
import sigmastate.crypto.SigmaProtocolPrivateInput
import sigmastate.helpers.TestingHelpers._
import sigmastate.helpers.{CompilerTestingCommons, ContextEnrichingTestProvingInterpreter, ErgoLikeContextTesting, ErgoLikeTestInterpreter}

import java.math.BigInteger
import java.nio.ByteBuffer
import scala.collection.compat.immutable.ArraySeq
import scala.util.Try

/** Phase-1 feasibility probe for the Base/PLAIN I-3 Claim-opening branch.
  *
  * The Claim target is provisional while C-1 remains uncomposed. No compiled
  * hash from this specification is a lifecycle ABI pin.
  */
class BitcoinRsBtcI3ClaimOpeningSpecification
  extends CompilerTestingCommons with CompilerCrossVersionProps {

  private implicit lazy val IR: TestingIRContext = new TestingIRContext

  private val stateValue = 100000000L
  private val stateFee = 1000000L
  private val claimReserveFloor = 10000000L
  private val collateralAmount = 1000L
  private val minSatoshis = 250000L
  private val maxCreationHeightLag = 2

  private val ExpectedRsBtcTokenIdHex = "1111111111111111111111111111111111111111111111111111111111111111"
  private val ExpectedFeePropositionHex =
    "1005040004000e36100204a00b08cd0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798ea02d192a39a8cc7a701730073011001020402d19683030193a38cc7b2a57300000193c2b2a57301007473027303830108cdeeac93b1a57304"
  private val ExpectedWrongFeeP2PkHex =
    "0008cd0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

  private val Phase1ProvisionalTreeSize = 1196
  private val Phase1ProvisionalTreeHash =
    "0168e8ca61fde3560f2c456b919f9826ad1471ac98cd6a56a328f7b7ddf3d285"
  private val Phase1ProvisionalCanonicalCost = 1218L
  private val Phase1ProvisionalExternalCost = 1237L
  private val ExpectedCanonicalNonSecretFingerprint =
    "2d5bbaad6efd7944e648dc69e91acb4416ef974698f485e417ca701bfe9bfc8e"

  private val d1 = 780
  private val responseMin = 100
  private val responseMax = 200
  private val currentHeight = 800
  private val d2 = currentHeight + responseMin + 1

  private val rsBtcTokenIdBytes = Array.fill(32)(0x11.toByte)
  private val rsBtcTokenId = Digest32Coll @@ rsBtcTokenIdBytes.toColl
  private val originNftId = Digest32Coll @@ Array.fill(32)(0x22.toByte).toColl
  private val alternateRsBtcTokenIdBytes = Array.fill(32)(0x33.toByte)
  private val alternateRsBtcTokenId = Digest32Coll @@ alternateRsBtcTokenIdBytes.toColl
  private val insuredDealTokens = ArraySeq(
    (originNftId, 1L): Token,
    (rsBtcTokenId, collateralAmount): Token)

  private val outpoint = Array.tabulate(36)(i => (i + 1).toByte)
  private val scriptHash = Array.tabulate(32)(i => (i + 41).toByte)

  private val buyerPayoutInput = DLogProverInput(BigInteger.valueOf(1L))
  private val sellerPayoutInput = DLogProverInput(BigInteger.valueOf(2L))
  private val buyerAuthorizationInput = DLogProverInput(BigInteger.valueOf(3L))
  private val sellerAuthorizationInput = DLogProverInput(BigInteger.valueOf(4L))
  private val alternateAuthorizationInput = DLogProverInput(BigInteger.valueOf(5L))

  private lazy val provisionalClaimTree = compileV6("{ sigmaProp(HEIGHT < 0) }")
  private lazy val provisionalClaimHash = Blake2b256.hash(provisionalClaimTree.bytes)
  private lazy val insuredDealTree = compileV6(insuredDealScript)
  private lazy val feeTree = ErgoTreePredef.feeProposition()
  private lazy val wrongFeeP2PkTree = ErgoTree.fromSigmaBoolean(
    ErgoTree.headerWithVersion(ZeroHeader, 0),
    buyerPayoutInput.publicImage)

  property("I-3 canonical Claim opening reduces to true") {
    val result = evaluateI3()

    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("I-3 F2C-4 uses a canonical wrong P2PK fee proposition") {
    Base16.encode(wrongFeeP2PkTree.bytes) shouldBe ExpectedWrongFeeP2PkHex
    Base16.encode(ErgoTree.fromBytes(wrongFeeP2PkTree.bytes).bytes) shouldBe
      ExpectedWrongFeeP2PkHex
    ExpectedWrongFeeP2PkHex should not be ExpectedFeePropositionHex

    assertContractTrue("canonical fee proposition", evaluateI3())
    assertContractFalse(
      "canonical wrong P2PK fee proposition",
      evaluateI3(feeTreeOverride = wrongFeeP2PkTree, directVerification = true))
  }

  property("I-3 F2C-1 uses a collision-free family-token mismatch") {
    val alternateTokenHex = Base16.encode(alternateRsBtcTokenIdBytes)
    val alternateTokens = ArraySeq(
      (originNftId, 1L): Token,
      (alternateRsBtcTokenId, collateralAmount): Token)
    val alternateFamilyTree = compileI3Mutant(
      s"""fromBase16("$ExpectedRsBtcTokenIdHex")""",
      s"""fromBase16("$alternateTokenHex")""")

    (alternateRsBtcTokenId == originNftId) shouldBe false
    (alternateRsBtcTokenId == rsBtcTokenId) shouldBe false
    assertContractTrue("canonical family parent", evaluateI3())
    assertContractFalse(
      "fixture token differs from the compiled family token",
      evaluateI3(
        inputTokens = alternateTokens,
        claimTokens = alternateTokens,
        directVerification = true))
    assertContractTrue(
      "matched alternate family control",
      evaluateI3(
        inputTokens = alternateTokens,
        claimTokens = alternateTokens,
        contractTreeOverride = Some(alternateFamilyTree)))
  }

  property("I-3 F2C topology rows pin their reduction channels") {
    val inputCountMutant = compileI3Mutant(
      "val inputCountOk = INPUTS.size == 1 || INPUTS.size == 2",
      "val inputCountOk = true")
    assertContractTrue("one-input parent", evaluateI3())
    assertContractFalse(
      "three-input synthetic reduction",
      evaluateI3(
        externalInputValue = Some(1000000L),
        includeThirdInput = true,
        directVerification = true))
    assertContractTrue(
      "three-input guard mutant",
      evaluateI3(
        externalInputValue = Some(1000000L),
        includeThirdInput = true,
        contractTreeOverride = Some(inputCountMutant)))

    assertEvaluationFailure(
      "fee and Claim outputs swapped",
      evaluateI3(swapPrimaryOutputs = true, directVerification = true),
      classOf[NoSuchElementException])

    assertContractTrue(
      "executor-absent external parent",
      evaluateI3(
        externalInputValue = Some(4000000L),
        feeValue = stateFee + 1000000L,
        claimValue = stateValue,
        changeValue = Some(2000000L)))
    assertContractFalse(
      "executor-present value-conserving child",
      evaluateI3(
        externalInputValue = Some(4000000L),
        feeValue = stateFee + 1000000L,
        claimValue = stateValue,
        changeValue = Some(1000000L),
        appendExtraOutput = true,
        directVerification = true))

    val changeIndexMutant = compileI3Mutant(
      "val changeOut = OUTPUTS.getOrElse(2, SELF)",
      "val changeOut = OUTPUTS.getOrElse(3, SELF)")
    val changeIndexParent = evaluateI3(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      claimValue = stateValue,
      changeValue = Some(1000000L))
    assertContractTrue("change-index parent", changeIndexParent)
    assertContractFalse(
      "change-index family mutant",
      evaluateI3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        claimValue = stateValue,
        changeValue = Some(1000000L),
        directVerification = true,
        contractTreeOverride = Some(changeIndexMutant)))
  }

  property("I-3 F2C numeric bindings use executable boundary controls") {
    val alternateStateFeeFamilyTree =
      compileInsuredDealFamily(stateFee - 1L, compileV6)
    assertContractTrue("state-fee parent", evaluateI3())
    assertContractFalse(
      "lower compiled state fee",
      evaluateI3(
        directVerification = true,
        contractTreeOverride = Some(alternateStateFeeFamilyTree)))

    val reserveMutant = compileI3Mutant(
      s"val claimReserveFloor = ${claimReserveFloor}L",
      s"val claimReserveFloor = ${claimReserveFloor + 1L}L")
    assertContractTrue(
      "reserve-floor boundary parent",
      evaluateI3(
        inputValue = stateFee + claimReserveFloor,
        claimValue = claimReserveFloor))
    assertContractFalse(
      "reserve-floor family mutant",
      evaluateI3(
        inputValue = stateFee + claimReserveFloor,
        claimValue = claimReserveFloor,
        directVerification = true,
        contractTreeOverride = Some(reserveMutant)))
  }

  property("Base/PLAIN I-3 emitter rejects excessive state deduction before source or tree emission") {
    val acceptedSource = Try(emitInsuredDealScript(stateFee))
    acceptedSource.isSuccess shouldBe true
    acceptedSource.get shouldBe insuredDealScript

    var compilerInvoked = false
    val acceptedTree = compileInsuredDealFamily(stateFee, { source =>
      compilerInvoked = true
      compileV6(source)
    })
    compilerInvoked shouldBe true
    acceptedTree.bytes shouldBe insuredDealTree.bytes

    val excessiveStateFee = stateFee + 1L
    val rejectedSource = Try(emitInsuredDealScript(excessiveStateFee))
    assertFamilyEmissionFailure("excessive I-3 source", rejectedSource)
    rejectedSource.toOption shouldBe None

    compilerInvoked = false
    val rejectedTree = Try(compileInsuredDealFamily(excessiveStateFee, { source =>
      compilerInvoked = true
      compileV6(source)
    }))
    assertFamilyEmissionFailure("excessive I-3 tree", rejectedTree)
    rejectedTree.toOption shouldBe None
    compilerInvoked shouldBe false

    Base16.encode(rsBtcTokenIdBytes) shouldBe ExpectedRsBtcTokenIdHex
    Base16.encode(feeTree.bytes) shouldBe ExpectedFeePropositionHex
  }

  property("I-3 pins D1 and the inclusive response-window boundaries") {
    val minD2 = currentHeight + responseMin + 1
    val maxD2 = currentHeight + responseMax + 1

    minD2.toLong - currentHeight.toLong - 1L shouldBe responseMin.toLong
    maxD2.toLong - currentHeight.toLong - 1L shouldBe responseMax.toLong

    assertContractTrue("D1", evaluateI3(evaluationHeight = d1, claimD2 = d1 + responseMin + 1))
    assertContractFalse(
      "D1 - 1",
      evaluateI3(evaluationHeight = d1 - 1, directVerification = true))
    assertContractTrue("minimum D2", evaluateI3(claimD2 = minD2))
    assertContractTrue("maximum D2", evaluateI3(claimD2 = maxD2))
    assertContractFalse(
      "below minimum D2",
      evaluateI3(claimD2 = minD2 - 1, directVerification = true))
    assertContractFalse(
      "above maximum D2",
      evaluateI3(claimD2 = maxD2 + 1, directVerification = true))
  }

  property("I-3 fixes state position, input count, data inputs, and Fe-zero outputs") {
    assertContractFalse(
      "state at input 1",
      evaluateI3(
        stateAtInputOne = true,
        changeValue = Some(1000000L),
        directVerification = true))
    assertContractFalse(
      "third input",
      evaluateI3(
        externalInputValue = Some(1000000L),
        includeThirdInput = true,
        directVerification = true))
    assertContractFalse(
      "data input",
      evaluateI3(includeDataInput = true, directVerification = true))
    assertContractFalse(
      "executor or extra output",
      evaluateI3(appendExtraOutput = true, directVerification = true))
    assertContractFalse(
      "change without external input",
      evaluateI3(changeValue = Some(1L), directVerification = true))
  }

  property("I-3 requires the complete InsuredDeal schema") {
    val collidingRoles = canonicalInsuredDealRegisters.updated(
      R7,
      roleRegister(buyerAuthorizationInput, buyerPayoutInput))
    val coinbaseSentinel = Array.fill(32)(0.toByte) ++ Array.fill(4)(0xff.toByte)
    // Removing the final register isolates absence while preserving dense-box serialization.
    val missingClaimCommitment = canonicalInsuredDealRegisters - R9

    assertSingleMapCoordinateRemoval(
      "missing R9 fixture",
      canonicalInsuredDealRegisters,
      missingClaimCommitment,
      R9)
    assertContractTrue(
      "R9 presence control",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters))
    assertEvaluationFailure(
      "missing R9 Claim commitment",
      evaluateI3(inputRegisters = missingClaimCommitment),
      classOf[NoSuchElementException])
    assertEvaluationFailure(
      "wrong-typed R8",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(R8, IntConstant(d1))),
      classOf[sigma.exceptions.InvalidType],
      "Cannot getReg[Coll[Int]](8): invalid type")
    assertContractFalse(
      "outpoint size",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R4,
        paymentRegister(outpointBytes = outpoint.drop(1))),
        directVerification = true))
    assertContractFalse(
      "script hash size",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R4,
        paymentRegister(scriptHashBytes = scriptHash.drop(1))),
        directVerification = true))
    assertContractFalse(
      "minimum satoshis",
      evaluateI3(
        inputRegisters = canonicalInsuredDealRegisters.updated(R5, LongConstant(0L)),
        directVerification = true))
    assertContractFalse(
      "satoshi supply bound",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R5,
        LongConstant(2100000000000001L)),
        directVerification = true))
    assertContractFalse(
      "coinbase outpoint",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R4,
        paymentRegister(outpointBytes = coinbaseSentinel)),
        directVerification = true))
    assertContractFalse(
      "cross-party role collision",
      evaluateI3(inputRegisters = collidingRoles, directVerification = true))
    assertContractFalse(
      "negative D1",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R8,
        IntArrayConstant(Array(-1, responseMin, responseMax))),
        directVerification = true))
    assertContractFalse(
      "zero response minimum",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R8,
        IntArrayConstant(Array(d1, 0, responseMax))),
        directVerification = true))
    assertContractFalse(
      "inverted response range",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R8,
        IntArrayConstant(Array(d1, responseMax, responseMin))),
        directVerification = true))
    assertContractFalse(
      "response ceiling",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R8,
        IntArrayConstant(Array(d1, responseMin, 501))),
        directVerification = true))
    assertContractFalse(
      "wrong Claim commitment",
      evaluateI3(inputRegisters = canonicalInsuredDealRegisters.updated(
        R9,
        ByteArrayConstant(Array.fill(32)(0x7f.toByte))),
        directVerification = true))
  }

  property("I-3 requires the exact InsuredDeal token vector") {
    val alternateTokenId = Digest32Coll @@ Array.fill(32)(0x55.toByte).toColl

    assertContractFalse(
      "wrong origin quantity",
      evaluateI3(inputTokens = ArraySeq(
        (originNftId, 2L): Token,
        (rsBtcTokenId, collateralAmount): Token),
        directVerification = true))
    assertContractFalse(
      "wrong collateral id",
      evaluateI3(inputTokens = ArraySeq(
        (originNftId, 1L): Token,
        (alternateTokenId, collateralAmount): Token),
        directVerification = true))
    assertContractFalse(
      "wrong collateral amount",
      evaluateI3(inputTokens = ArraySeq(
        (originNftId, 1L): Token,
        (rsBtcTokenId, 0L): Token),
        directVerification = true))
    assertContractFalse(
      "extra token",
      evaluateI3(inputTokens = ArraySeq(
        (originNftId, 1L): Token,
        (rsBtcTokenId, collateralAmount): Token,
        (alternateTokenId, 1L): Token),
        directVerification = true))
  }

  property("I-3 pins every Claim successor field and token") {
    assertContractFalse(
      "wrong Claim proposition",
      evaluateI3(claimTreeOverride = TrueTree, directVerification = true))
    assertContractFalse(
      "wrong payment",
      evaluateI3(claimRegistersOverride = Some(canonicalClaimRegisters.updated(
        R4,
        paymentRegister(scriptHashBytes = Array.fill(32)(0x7e.toByte)))),
        directVerification = true))
    assertContractFalse(
      "wrong minimum satoshis",
      evaluateI3(claimRegistersOverride = Some(
        canonicalClaimRegisters.updated(R5, LongConstant(minSatoshis + 1L))),
        directVerification = true))
    assertContractFalse(
      "wrong payout keys",
      evaluateI3(claimRegistersOverride = Some(canonicalClaimRegisters.updated(
        R6,
        roleRegister(buyerPayoutInput, alternateAuthorizationInput))),
        directVerification = true))
    assertContractFalse(
      "wrong authorization keys",
      evaluateI3(claimRegistersOverride = Some(canonicalClaimRegisters.updated(
        R7,
        roleRegister(buyerAuthorizationInput, alternateAuthorizationInput))),
        directVerification = true))
    assertEvaluationFailure(
      "wrong-typed D2",
      evaluateI3(claimRegistersOverride = Some(
        canonicalClaimRegisters.updated(R8, LongConstant(d2.toLong)))),
      classOf[sigma.exceptions.InvalidType],
      "Cannot getReg[Int](8): invalid type")
    assertContractFalse(
      "unexpected R9",
      evaluateI3(claimRegistersOverride = Some(
        canonicalClaimRegisters.updated(R9, ByteArrayConstant(Array[Byte](1)))),
        directVerification = true))
    assertEvaluationFailure(
      "wrong-typed unexpected R9",
      evaluateI3(claimRegistersOverride = Some(
        canonicalClaimRegisters.updated(R9, IntConstant(1)))),
      classOf[sigma.exceptions.InvalidType],
      "Cannot getReg[Coll[Byte]](9): invalid type")
    assertContractFalse(
      "wrong origin NFT",
      evaluateI3(claimTokens = ArraySeq(
        (Digest32Coll @@ Array.fill(32)(0x44.toByte).toColl, 1L): Token,
        (rsBtcTokenId, collateralAmount): Token),
        directVerification = true))
    assertContractFalse(
      "wrong collateral amount",
      evaluateI3(claimTokens = ArraySeq(
        (originNftId, 1L): Token,
        (rsBtcTokenId, collateralAmount - 1L): Token),
        directVerification = true))
    assertContractFalse(
      "wrong collateral id",
      evaluateI3(claimTokens = ArraySeq(
        (originNftId, 1L): Token,
        (Digest32Coll @@ Array.fill(32)(0x66.toByte).toColl, collateralAmount): Token),
        directVerification = true))
  }

  property("I-3 enforces fresh Claim creation height") {
    assertContractTrue(
      "freshness floor",
      evaluateI3(claimCreationHeight = Some(currentHeight - maxCreationHeightLag)))
    assertContractFalse(
      "below freshness floor",
      evaluateI3(
        claimCreationHeight = Some(currentHeight - maxCreationHeightLag - 1),
        directVerification = true))
    assertContractFalse(
      "future creation height",
      evaluateI3(
        claimCreationHeight = Some(currentHeight + 1),
        directVerification = true))
  }

  property("I-3 conserves state value and isolates external funding") {
    assertContractFalse(
      "successor below state-funded baseline",
      evaluateI3(
        claimValue = stateValue - stateFee - 1L,
        directVerification = true))
    assertContractFalse(
      "below reserve floor",
      evaluateI3(
        inputValue = stateFee + claimReserveFloor - 1L,
        claimValue = claimReserveFloor - 1L,
        directVerification = true))
    assertContractFalse(
      "wrong fee proposition",
      evaluateI3(feeTreeOverride = TrueTree, directVerification = true))
    assertContractFalse(
      "fee below state contribution",
      evaluateI3(feeValue = stateFee - 1L, directVerification = true))
    assertContractFalse(
      "unfunded fee uplift",
      evaluateI3(feeValue = stateFee + 1L, directVerification = true))
    assertContractFalse(
      "unfunded Claim top-up",
      evaluateI3(claimValue = stateValue, directVerification = true))

    assertContractTrue(
      "external fee, top-up, and change",
      evaluateI3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        claimValue = stateValue,
        changeValue = Some(1000000L)))
    assertContractFalse(
      "external equation drift",
      evaluateI3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        claimValue = stateValue,
        changeValue = Some(1000001L),
        directVerification = true))
    assertContractFalse(
      "tokenized external input",
      evaluateI3(
        externalInputValue = Some(1000000L),
        changeValue = Some(1000000L),
        externalInputTokens = ArraySeq((rsBtcTokenId, 1L): Token),
        directVerification = true))
    assertContractFalse(
      "tokenized change",
      evaluateI3(
        externalInputValue = Some(1000000L),
        changeValue = Some(1000000L),
        changeTokens = ArraySeq((rsBtcTokenId, 1L): Token),
        directVerification = true))
  }

  property("I-3 requires buyer authorization and a closed branch tag") {
    val canonicalExtension = Map[Byte, EvaluatedValue[_ <: SType]](
      0.toByte -> ByteConstant(2.toByte))
    val missingBranchExtension = Map.empty[Byte, EvaluatedValue[_ <: SType]]

    assertContractTrue(
      "buyer authorization accepting control",
      evaluateI3(expectedNonSecretFingerprint = Some(ExpectedCanonicalNonSecretFingerprint)))
    assertProofFailure(
      "missing buyer proof",
      evaluateI3(
        authorizationSecrets = Seq.empty,
        expectedNonSecretFingerprint = Some(ExpectedCanonicalNonSecretFingerprint)))
    assertProofFailure(
      "wrong buyer proof",
      evaluateI3(
        authorizationSecrets = Seq(alternateAuthorizationInput),
        expectedNonSecretFingerprint = Some(ExpectedCanonicalNonSecretFingerprint)))

    assertSingleMapCoordinateRemoval(
      "missing var 0 fixture",
      canonicalExtension,
      missingBranchExtension,
      0.toByte)
    assertContractTrue(
      "branch tag presence control",
      evaluateI3(extensionValuesOverride = Some(canonicalExtension)))
    assertEvaluationFailure(
      "missing branch tag",
      evaluateI3(extensionValuesOverride = Some(missingBranchExtension)),
      classOf[NoSuchElementException])
    assertEvaluationFailure(
      "wrong-typed branch tag",
      evaluateI3(extensionValuesOverride = Some(Map(0.toByte -> IntConstant(2)))),
      classOf[sigma.exceptions.InvalidType],
      "Cannot getVar[Byte](0): invalid type")
    assertContractFalse(
      "I-1 remains closed",
      evaluateI3(branch = 0.toByte, directVerification = true))
    assertContractFalse(
      "I-2 remains closed",
      evaluateI3(branch = 1.toByte, directVerification = true))
    assertContractFalse(
      "unknown branch",
      evaluateI3(branch = 3.toByte, directVerification = true))
  }

  property("I-3 does not read Bitcoin vars 1 through 6") {
    val unrelated = Map[Byte, EvaluatedValue[_ <: SType]](
      1.toByte -> IntConstant(1),
      2.toByte -> LongConstant(2L),
      3.toByte -> ByteArrayConstant(Array[Byte](3)),
      4.toByte -> IntConstant(4),
      5.toByte -> LongConstant(5L),
      6.toByte -> ByteConstant(6.toByte))

    assertContractTrue("wrong-typed vars 1-6", evaluateI3(extraContextVars = unrelated))
  }

  property("I-3 load-bearing guards have isolated mutation regressions") {
    val d2LowerBoundMutant = compileI3Mutant(
      "minD2 <= successorD2Long",
      "true")
    val belowMinD2 = currentHeight + responseMin
    assertContractFalse(
      "D2 lower-bound control",
      evaluateI3(claimD2 = belowMinD2, directVerification = true))
    assertContractTrue(
      "D2 lower-bound mutant",
      evaluateI3(
        claimD2 = belowMinD2,
        contractTreeOverride = Some(d2LowerBoundMutant)))

    val propositionMutant = compileI3Mutant(
      "blake2b256(successor.propositionBytes) == expectedClaimHash",
      "true")
    assertContractFalse(
      "Claim proposition control",
      evaluateI3(claimTreeOverride = TrueTree, directVerification = true))
    assertContractTrue(
      "Claim proposition mutant",
      evaluateI3(
        claimTreeOverride = TrueTree,
        contractTreeOverride = Some(propositionMutant)))

    val externalValueMutant = compileI3Mutant(
      "externalValue - feeUplift - successorTopUp == changeValue",
      "true")
    val driftingValue = evaluateI3(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      claimValue = stateValue,
      changeValue = Some(1000001L),
      directVerification = true)
    assertContractFalse("external-value control", driftingValue)
    assertContractTrue(
      "external-value mutant",
      evaluateI3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        claimValue = stateValue,
        changeValue = Some(1000001L),
        contractTreeOverride = Some(externalValueMutant)))

    val buyerAuthorizationMutant = compileI3Mutant(
      "proveDlog(authorizationKeys._1)",
      "sigmaProp(true)")
    assertProofFailure(
      "buyer authorization control",
      evaluateI3(authorizationSecrets = Seq.empty))
    assertContractTrue(
      "buyer authorization mutant",
      evaluateI3(
        authorizationSecrets = Seq.empty,
        contractTreeOverride = Some(buyerAuthorizationMutant)))
  }

  property("I-3 pins provisional Phase-1 tree bytes and full-branch costs") {
    val canonical = evaluateI3().get
    val external = evaluateI3(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      claimValue = stateValue,
      changeValue = Some(1000000L)).get
    canonical._1 shouldBe true
    external._1 shouldBe true
    insuredDealTree.bytes.length shouldBe Phase1ProvisionalTreeSize
    Base16.encode(Blake2b256.hash(insuredDealTree.bytes)) shouldBe
      Phase1ProvisionalTreeHash
    canonical._2 shouldBe Phase1ProvisionalCanonicalCost
    external._2 shouldBe Phase1ProvisionalExternalCost
  }

  private def evaluateI3(
      evaluationHeight: Int = currentHeight,
      inputRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] =
        canonicalInsuredDealRegisters,
      inputValue: Long = stateValue,
      inputTokens: ArraySeq[Token] = insuredDealTokens,
      claimD2: Int = d2,
      claimValue: Long = stateValue - stateFee,
      claimTreeOverride: ErgoTree = provisionalClaimTree,
      claimCreationHeight: Option[Int] = None,
      claimTokens: ArraySeq[Token] = insuredDealTokens,
      claimRegistersOverride:
        Option[Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]]] = None,
      feeValue: Long = stateFee,
      feeTreeOverride: ErgoTree = feeTree,
      feeTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      externalInputValue: Option[Long] = None,
      externalInputTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      changeValue: Option[Long] = None,
      changeTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      appendExtraOutput: Boolean = false,
      swapPrimaryOutputs: Boolean = false,
      includeThirdInput: Boolean = false,
      includeDataInput: Boolean = false,
      branch: Byte = 2.toByte,
      extraContextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty,
      extensionValuesOverride:
        Option[Map[Byte, EvaluatedValue[_ <: SType]]] = None,
      authorizationSecrets: Seq[DLogProverInput] = Seq(buyerAuthorizationInput),
      stateAtInputOne: Boolean = false,
      directVerification: Boolean = false,
      contractTreeOverride: Option[ErgoTree] = None,
      expectedNonSecretFingerprint: Option[String] = None): Try[(Boolean, Long)] = {
    val contractTree = contractTreeOverride.getOrElse(insuredDealTree)
    val stateInput = testBox(
      inputValue,
      contractTree,
      creationHeight = 0,
      additionalTokens = inputTokens,
      additionalRegisters = inputRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](1))),
      boxIndex = 0)
    val claimOutput = testBox(
      claimValue,
      claimTreeOverride,
      creationHeight = claimCreationHeight.getOrElse(evaluationHeight),
      additionalTokens = claimTokens,
      additionalRegisters = claimRegistersOverride.getOrElse(
        canonicalClaimRegistersFor(claimD2)),
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](2))),
      boxIndex = 0).toCandidate
    val feeOutput = testBox(
      feeValue,
      feeTreeOverride,
      creationHeight = evaluationHeight,
      additionalTokens = feeTokens,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](3))),
      boxIndex = 1).toCandidate

    val externalInput = testBox(
      externalInputValue.getOrElse(1000000L),
      TrueTree,
      creationHeight = evaluationHeight,
      additionalTokens = externalInputTokens,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](4))),
      boxIndex = 0)
    val thirdInput = testBox(
      1000000L,
      TrueTree,
      creationHeight = evaluationHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](5))),
      boxIndex = 0)
    val changeOutput = changeValue.map { value =>
      testBox(
        value,
        TrueTree,
        creationHeight = evaluationHeight,
        additionalTokens = changeTokens,
        transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](6))),
        boxIndex = 2).toCandidate
    }
    val extraOutput = testBox(
      1000000L,
      TrueTree,
      creationHeight = evaluationHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](7))),
      boxIndex = 3).toCandidate
    val dataBox = testBox(
      1000000L,
      TrueTree,
      creationHeight = evaluationHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](8))),
      boxIndex = 0)

    val defaultExtensionValues = extraContextVars ++ Map(
      0.toByte -> ByteConstant(branch))
    val extensionValues = extensionValuesOverride.getOrElse(defaultExtensionValues)
    val extension = ContextExtension(extensionValues)
    val stateInputRef = Input(
      stateInput.id,
      ProverResult(Array.emptyByteArray, extension))
    val externalInputRef = Input(
      externalInput.id,
      ProverResult(Array.emptyByteArray, ContextExtension.empty))
    val thirdInputRef = Input(
      thirdInput.id,
      ProverResult(Array.emptyByteArray, ContextExtension.empty))
    val orderedInputs = if (stateAtInputOne) {
      IndexedSeq(externalInputRef, stateInputRef)
    } else {
      IndexedSeq(stateInputRef) ++ externalInputValue.map(_ => externalInputRef) ++
        (if (includeThirdInput) IndexedSeq(thirdInputRef) else IndexedSeq.empty)
    }
    val boxesToSpend = if (stateAtInputOne) {
      IndexedSeq(externalInput, stateInput)
    } else {
      IndexedSeq(stateInput) ++ externalInputValue.map(_ => externalInput) ++
        (if (includeThirdInput) IndexedSeq(thirdInput) else IndexedSeq.empty)
    }
    val primaryOutputs = if (swapPrimaryOutputs) {
      IndexedSeq(feeOutput, claimOutput)
    } else {
      IndexedSeq(claimOutput, feeOutput)
    }
    val outputs = primaryOutputs ++ changeOutput ++
      (if (appendExtraOutput) IndexedSeq(extraOutput) else IndexedSeq.empty)
    val dataInputs = if (includeDataInput) IndexedSeq(DataInput(dataBox.id)) else IndexedSeq.empty
    val dataBoxes = if (includeDataInput) IndexedSeq(dataBox) else IndexedSeq.empty
    val tx = new ErgoLikeTransaction(
      orderedInputs,
      dataInputs,
      outputs)
    val selfIndex = if (stateAtInputOne) 1 else 0
    val context = ErgoLikeContextTesting(
      currentHeight = evaluationHeight,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = dataBoxes,
      boxesToSpend = boxesToSpend,
      spendingTransaction = tx,
      selfIndex = selfIndex,
      activatedVersion = V6SoftForkVersion)

    expectedNonSecretFingerprint.foreach { expected =>
      val actual = nonSecretFixtureFingerprint(
        contractTree,
        tx,
        boxesToSpend,
        dataBoxes,
        evaluationHeight,
        selfIndex)
      withClue("non-secret fixture fingerprint") {
        actual shouldBe expected
      }
    }

    if (directVerification) {
      return new ErgoLikeTestInterpreter().verify(
        contractTree,
        context.withExtension(extension),
        ProverResult(Array.emptyByteArray, extension),
        Array.fill(32)(0.toByte))
    }

    val prover = new ContextEnrichingTestProvingInterpreter {
      override lazy val secrets: Seq[SigmaProtocolPrivateInput[_]] =
        authorizationSecrets
      override lazy val contextExtenders: Map[Byte, EvaluatedValue[_ <: SType]] =
        extensionValues
    }
    val verifier = new ErgoLikeTestInterpreter
    val message = Array.fill(32)(0.toByte)

    prover.prove(contractTree, context, message).flatMap { proof =>
      verifier.verify(
        contractTree,
        context.withExtension(proof.extension),
        proof,
        message)
      }
  }

  private def assertContractTrue(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isSuccess shouldBe true
      result.get._1 shouldBe true
    }

  private def assertContractFalse(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isSuccess shouldBe true
      result.get._1 shouldBe false
    }

  private def assertEvaluationFailure(
      label: String,
      result: Try[(Boolean, Long)],
      expectedCause: Class[_ <: Throwable],
      expectedMessagePrefix: String = ""): Unit =
    withClue(label) {
      result.isFailure shouldBe true
      val cause = rootCause(result.failed.get)
      cause.getClass shouldBe expectedCause
      if (expectedMessagePrefix.nonEmpty) {
        Option(cause.getMessage).getOrElse("") should startWith (expectedMessagePrefix)
      }
    }

  private def assertProofFailure(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isFailure shouldBe true
      val cause = rootCause(result.failed.get)
      cause shouldBe a[AssertionError]
      cause.getMessage should startWith ("assertion failed: Tree root should be real")
      cause.getMessage should include (buyerAuthorizationInput.publicImage.toString)
    }

  private def assertFamilyEmissionFailure(label: String, result: Try[_]): Unit =
    withClue(label) {
      result.isFailure shouldBe true
      val cause = rootCause(result.failed.get)
      cause.getClass shouldBe classOf[IllegalArgumentException]
      cause.getMessage shouldBe
        "requirement failed: The state-funded miner fee exceeds the family deduction cap"
    }

  private def assertSingleMapCoordinateRemoval[K, V](
      label: String,
      baseline: Map[K, V],
      candidate: Map[K, V],
      removed: K): Unit =
    withClue(label) {
      baseline.contains(removed) shouldBe true
      candidate shouldBe (baseline - removed)
    }

  private def nonSecretFixtureFingerprint(
      contractTree: ErgoTree,
      tx: ErgoLikeTransaction,
      boxesToSpend: IndexedSeq[ErgoBox],
      dataBoxes: IndexedSeq[ErgoBox],
      evaluationHeight: Int,
      selfIndex: Int): String = {
    val components = IndexedSeq(
      contractTree.bytes,
      ErgoLikeTransactionSerializer.toBytes(tx),
      intBytes(evaluationHeight),
      intBytes(selfIndex),
      intBytes(V6SoftForkVersion.toInt)) ++
      boxesToSpend.map(_.bytes) ++ dataBoxes.map(_.bytes)
    val framed = components.foldLeft(Array.emptyByteArray) { (acc, bytes) =>
      acc ++ intBytes(bytes.length) ++ bytes
    }
    Base16.encode(Blake2b256.hash(framed))
  }

  private def intBytes(value: Int): Array[Byte] =
    ByteBuffer.allocate(4).putInt(value).array()

  private def pairConstant(
      first: SType#WrappedType,
      second: SType#WrappedType,
      firstType: SType,
      secondType: SType): EvaluatedValue[_ <: SType] =
    Constant(
      (first, second).asInstanceOf[SType#WrappedType],
      STuple(firstType, secondType))

  private def paymentRegister(
      outpointBytes: Array[Byte] = outpoint,
      scriptHashBytes: Array[Byte] = scriptHash): EvaluatedValue[_ <: SType] =
    pairConstant(
      ByteArrayConstant(outpointBytes).value,
      ByteArrayConstant(scriptHashBytes).value,
      SCollection(SByte),
      SCollection(SByte))

  private def roleRegister(
      first: DLogProverInput,
      second: DLogProverInput): EvaluatedValue[_ <: SType] =
    pairConstant(
      GroupElementConstant(first.publicImage.value).value,
      GroupElementConstant(second.publicImage.value).value,
      SGroupElement,
      SGroupElement)

  private val payoutKeysRegister = roleRegister(buyerPayoutInput, sellerPayoutInput)
  private val authorizationKeysRegister = roleRegister(
    buyerAuthorizationInput,
    sellerAuthorizationInput)

  private def canonicalInsuredDealRegisters:
      Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map(
    R4 -> paymentRegister(),
    R5 -> LongConstant(minSatoshis),
    R6 -> payoutKeysRegister,
    R7 -> authorizationKeysRegister,
    R8 -> IntArrayConstant(Array(d1, responseMin, responseMax)),
    R9 -> ByteArrayConstant(provisionalClaimHash))

  private def canonicalClaimRegistersFor(deadline: Int):
      Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map(
    R4 -> paymentRegister(),
    R5 -> LongConstant(minSatoshis),
    R6 -> payoutKeysRegister,
    R7 -> authorizationKeysRegister,
    R8 -> IntConstant(deadline))

  private def canonicalClaimRegisters:
      Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] =
    canonicalClaimRegistersFor(d2)

  private def compileV6(script: String): ErgoTree =
    VersionContext.withVersions(V6SoftForkVersion, V6SoftForkVersion) {
      ErgoTree.fromProposition(
        ErgoTree.headerWithVersion(ZeroHeader, V6SoftForkVersion),
        compile(Map.empty, script).asBoolValue.toSigmaProp)
    }

  private def compileI3Mutant(target: String, replacement: String): ErgoTree = {
    val first = insuredDealScript.indexOf(target)
    require(first >= 0, s"Mutation target not found: $target")
    require(
      insuredDealScript.indexOf(target, first + target.length) < 0,
      s"Mutation target is not unique: $target")
    compileV6(
      insuredDealScript.substring(0, first) ++ replacement ++
        insuredDealScript.substring(first + target.length))
  }

  private def emitInsuredDealScript(stateFeeValue: Long): String = {
    BitcoinRsBtcBasePlainFamilyPolicy.requireValidStateDeduction(stateFeeValue)
    s"""{
      |  val branch = getVar[Byte](0).get
      |  val rsBtcTokenId = fromBase16("${Base16.encode(rsBtcTokenIdBytes)}")
      |  val expectedClaimHash = fromBase16("${Base16.encode(provisionalClaimHash)}")
      |  val feePropositionBytes = fromBase16("${Base16.encode(feeTree.bytes)}")
      |  val stateFee = ${stateFeeValue}L
      |  val claimReserveFloor = ${claimReserveFloor}L
      |  val maxCreationHeightLag = $maxCreationHeightLag
      |  val protocolResponseFloor = 50
      |  val protocolResponseCeiling = 500
      |
      |  val payment = SELF.R4[(Coll[Byte], Coll[Byte])].get
      |  val outpoint = payment._1
      |  val scriptHash = payment._2
      |  val minSatoshis = SELF.R5[Long].get
      |  val payoutKeys = SELF.R6[(GroupElement, GroupElement)].get
      |  val authorizationKeys = SELF.R7[(GroupElement, GroupElement)].get
      |  val timing = SELF.R8[Coll[Int]].get
      |  val claimHash = SELF.R9[Coll[Byte]].get
      |  val d1 = timing.getOrElse(0, -1)
      |  val responseMin = timing.getOrElse(1, -1)
      |  val responseMax = timing.getOrElse(2, -1)
      |  val zeroHash = fromBase16("0000000000000000000000000000000000000000000000000000000000000000")
      |  val coinbaseIndex = fromBase16("ffffffff")
      |  val coinbaseSentinel = outpoint.size == 36 &&
      |                         outpoint.slice(0, 32) == zeroHash &&
      |                         outpoint.slice(32, 36) == coinbaseIndex
      |  val identity = groupGenerator.exp(0.toBigInt)
      |  val roleKeysNonIdentity = payoutKeys._1 != identity &&
      |                            payoutKeys._2 != identity &&
      |                            authorizationKeys._1 != identity &&
      |                            authorizationKeys._2 != identity
      |  val roleSeparationOk = payoutKeys._1 != payoutKeys._2 &&
      |                         payoutKeys._1 != authorizationKeys._2 &&
      |                         authorizationKeys._1 != payoutKeys._2 &&
      |                         authorizationKeys._1 != authorizationKeys._2
      |  val selfTokens = SELF.tokens
      |  val origin = selfTokens.getOrElse(0, (rsBtcTokenId, 0L))
      |  val collateral = selfTokens.getOrElse(1, (rsBtcTokenId, 0L))
      |  val tokenIdentityOk = origin._1 != rsBtcTokenId &&
      |                        origin._1 != SELF.id &&
      |                        rsBtcTokenId != SELF.id
      |  val stateSchemaOk = outpoint.size == 36 &&
      |                      !coinbaseSentinel &&
      |                      scriptHash.size == 32 &&
      |                      minSatoshis > 0L &&
      |                      minSatoshis <= 2100000000000000L &&
      |                      roleKeysNonIdentity &&
      |                      roleSeparationOk &&
      |                      timing.size == 3 &&
      |                      d1 >= 0 &&
      |                      protocolResponseFloor <= responseMin &&
      |                      responseMin <= responseMax &&
      |                      responseMax <= protocolResponseCeiling &&
      |                      claimHash == expectedClaimHash &&
      |                      selfTokens.size == 2 &&
      |                      origin._2 == 1L &&
      |                      collateral._1 == rsBtcTokenId &&
      |                      collateral._2 > 0L &&
      |                      tokenIdentityOk &&
      |                      SELF.value >= stateFee &&
      |                      SELF.value - stateFee >= claimReserveFloor
      |
      |  if (branch == 2) {
      |    val inputCountOk = INPUTS.size == 1 || INPUTS.size == 2
      |    val stateIsFirst = INPUTS.size > 0 && INPUTS(0).id == SELF.id
      |    val hasExternalInput = INPUTS.size == 2
      |    val externalInput = INPUTS.getOrElse(1, SELF)
      |    val externalInputOk = !hasExternalInput || externalInput.tokens.size == 0
      |    val outputCountOk = if (hasExternalInput) {
      |      OUTPUTS.size == 2 || OUTPUTS.size == 3
      |    } else {
      |      OUTPUTS.size == 2
      |    }
      |    val topologyOk = inputCountOk && stateIsFirst && externalInputOk &&
      |                     CONTEXT.dataInputs.size == 0 && outputCountOk
      |
      |    sigmaProp(stateSchemaOk && topologyOk && HEIGHT >= d1 && {
      |      val successor = OUTPUTS(0)
      |      val feeOut = OUTPUTS(1)
      |      val hasChange = OUTPUTS.size == 3
      |      val changeOut = OUTPUTS.getOrElse(2, SELF)
      |      val successorPayment = successor.R4[(Coll[Byte], Coll[Byte])].get
      |      val successorMinSatoshis = successor.R5[Long].get
      |      val successorPayoutKeys = successor.R6[(GroupElement, GroupElement)].get
      |      val successorAuthorizationKeys = successor.R7[(GroupElement, GroupElement)].get
      |      val successorD2 = successor.R8[Int].get
      |      val successorD2Long = successorD2.toLong
      |      val minD2 = HEIGHT.toLong + responseMin.toLong + 1L
      |      val maxD2 = HEIGHT.toLong + responseMax.toLong + 1L
      |      val d2Ok = successorD2 >= 0 &&
      |                 minD2 <= successorD2Long &&
      |                 successorD2Long <= maxD2
      |      val successorOrigin = successor.tokens.getOrElse(0, (rsBtcTokenId, 0L))
      |      val successorCollateral = successor.tokens.getOrElse(1, (rsBtcTokenId, 0L))
      |      val creationHeightFloor = if (HEIGHT > maxCreationHeightLag) {
      |        HEIGHT - maxCreationHeightLag
      |      } else {
      |        0
      |      }
      |      val successorPropositionOk =
      |        blake2b256(successor.propositionBytes) == expectedClaimHash
      |      val successorFieldsOk = successorPropositionOk &&
      |                              successorPayment == payment &&
      |                              successorMinSatoshis == minSatoshis &&
      |                              successorPayoutKeys == payoutKeys &&
      |                              successorAuthorizationKeys == authorizationKeys &&
      |                              d2Ok &&
      |                              successor.R9[Coll[Byte]].isEmpty &&
      |                              successor.creationInfo._1 >= creationHeightFloor &&
      |                              successor.creationInfo._1 <= HEIGHT
      |      val successorTokensOk = successor.tokens.size == 2 &&
      |                              successorOrigin == origin &&
      |                              successorCollateral == collateral
      |      val feeOutOk = feeOut.propositionBytes == feePropositionBytes &&
      |                     feeOut.value >= stateFee &&
      |                     feeOut.tokens.size == 0
      |      val changeOutOk = !hasChange || (
      |        changeOut.value > 0L &&
      |        changeOut.tokens.size == 0)
      |
      |      val successorBase = SELF.value - stateFee
      |      val successorValueOk = successor.value >= successorBase &&
      |                             successor.value >= claimReserveFloor
      |      val externalValue = if (hasExternalInput) externalInput.value else 0L
      |      val changeValue = if (hasChange) changeOut.value else 0L
      |      val feeUplift = feeOut.value - stateFee
      |      val successorTopUp = successor.value - successorBase
      |      val externalValueOk = successorValueOk &&
      |                            externalValue >= feeUplift &&
      |                            externalValue - feeUplift >= successorTopUp &&
      |                            externalValue - feeUplift - successorTopUp == changeValue
      |
      |      successorFieldsOk && successorTokensOk && feeOutOk &&
      |        changeOutOk && externalValueOk
      |    }) && proveDlog(authorizationKeys._1)
      |  } else {
      |    sigmaProp(false)
      |  }
      |}""".stripMargin.replace("\r\n", "\n")
  }

  private def compileInsuredDealFamily(
      stateFeeValue: Long,
      compiler: String => ErgoTree): ErgoTree =
    compiler(emitInsuredDealScript(stateFeeValue))

  private lazy val insuredDealScript: String = emitInsuredDealScript(stateFee)
}
