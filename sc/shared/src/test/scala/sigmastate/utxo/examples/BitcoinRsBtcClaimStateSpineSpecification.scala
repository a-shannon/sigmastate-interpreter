package sigmastate.utxo.examples

import org.ergoplatform.ErgoBox.Token
import org.ergoplatform.ErgoBox.{NonMandatoryRegisterId, R4, R5, R6, R7, R8}
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
import scala.collection.compat.immutable.ArraySeq
import scala.util.Try

/** Phase-1 state-spine probe for the Base/PLAIN Claim contract.
  *
  * C-1 remains disabled until the complete Bitcoin proof predicate is composed.
  * This specification therefore does not produce a successor-consumable Claim
  * hash.
  */
class BitcoinRsBtcClaimStateSpineSpecification
  extends CompilerTestingCommons with CompilerCrossVersionProps {

  private implicit lazy val IR: TestingIRContext = new TestingIRContext

  private val stateValue = 100000000L
  private val stateFee = 1000000L
  private val singlePayoutFloor = 1000000L
  private val mutualPayoutFloor = 1000000L
  private val maxCreationHeightLag = 2
  private val collateralAmount = 1000L
  private val minSatoshis = 250000L
  private val d2 = 900

  private val StateSpineTreeSize = 1517
  private val StateSpineTreeHash =
    "24ed963ae59eec23d4add20517f804a9d0393fc75bea1173affa4fc5b17c84a5"
  private val StateSpineC2Cost = 629L
  private val StateSpineC2ExternalCost = 648L
  private val StateSpineC3Cost = 1527L
  private val StateSpineC3ZeroFullCost = 1517L
  private val StateSpineC3ExternalCost = 1547L
  private val ExpectedWrongFeeP2PkHex =
    "0008cd0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

  private val rsBtcTokenIdBytes = Array.fill(32)(0x11.toByte)
  private val rsBtcTokenId = Digest32Coll @@ rsBtcTokenIdBytes.toColl
  private val originNftId = Digest32Coll @@ Array.fill(32)(0x22.toByte).toColl
  private val alternateTokenId = Digest32Coll @@ Array.fill(32)(0x33.toByte).toColl
  private val claimTokens = ArraySeq(
    (originNftId, 1L): Token,
    (rsBtcTokenId, collateralAmount): Token)

  private val outpoint = Array.tabulate(36)(i => (i + 1).toByte)
  private val scriptHash = Array.tabulate(32)(i => (i + 41).toByte)

  private val buyerPayoutInput = DLogProverInput(BigInteger.valueOf(1L))
  private val sellerPayoutInput = DLogProverInput(BigInteger.valueOf(2L))
  private val buyerAuthorizationInput = DLogProverInput(BigInteger.valueOf(3L))
  private val sellerAuthorizationInput = DLogProverInput(BigInteger.valueOf(4L))
  private val alternateAuthorizationInput = DLogProverInput(BigInteger.valueOf(5L))
  private val identityAuthorizationInput = DLogProverInput(BigInteger.ZERO)

  private lazy val claimTree = compileV6(claimScript)
  private lazy val feeTree = ErgoTreePredef.feeProposition()
  private lazy val alternatePayoutTree = ErgoTree.fromSigmaBoolean(
    ErgoTree.headerWithVersion(ZeroHeader, 0),
    sellerPayoutInput.publicImage)
  private lazy val buyerPayoutTree = ErgoTree.fromSigmaBoolean(
    ErgoTree.headerWithVersion(ZeroHeader, 0),
    buyerPayoutInput.publicImage)
  private lazy val sellerPayoutTree = ErgoTree.fromSigmaBoolean(
    ErgoTree.headerWithVersion(ZeroHeader, 0),
    sellerPayoutInput.publicImage)
  private lazy val wrongFeeP2PkTree = buyerPayoutTree
  private lazy val v6BuyerPayoutTree = ErgoTree.fromSigmaBoolean(
    ErgoTree.headerWithVersion(ZeroHeader, V6SoftForkVersion),
    buyerPayoutInput.publicImage)

  property("Claim C-2 canonical buyer payout reduces to true") {
    val result = evaluateC2()

    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("Claim C-2 F2C-4 uses a canonical wrong P2PK fee proposition") {
    Base16.encode(wrongFeeP2PkTree.bytes) shouldBe ExpectedWrongFeeP2PkHex
    Base16.encode(ErgoTree.fromBytes(wrongFeeP2PkTree.bytes).bytes) shouldBe
      ExpectedWrongFeeP2PkHex
    ExpectedWrongFeeP2PkHex should not be Base16.encode(feeTree.bytes)

    assertContractTrue("canonical fee proposition", evaluateC2())
    assertContractFalse(
      "canonical wrong P2PK fee proposition",
      evaluateC2(feeTreeOverride = wrongFeeP2PkTree))
  }

  property("Claim C-2 pins the canonical P2PK proposition encoding") {
    assertContractTrue("zero-header P2PK", evaluateC2())
    assertContractFalse(
      "V6-header P2PK has different proposition bytes",
      evaluateC2(buyerTree = v6BuyerPayoutTree))
  }

  property("Claim C-2 switches exactly at D2") {
    assertContractFalse("D2 - 1", evaluateC2(currentHeight = d2 - 1))
    assertContractTrue("D2", evaluateC2(currentHeight = d2))
    assertContractTrue("D2 + 1", evaluateC2(currentHeight = d2 + 1))
  }

  property("Claim C-2 closes branch, input, data-input, and output topology") {
    assertContractFalse("C-1 disabled", evaluateC2(branch = 0.toByte))
    assertContractFalse(
      "C-1 disabled before D2",
      evaluateC2(currentHeight = d2 - 1, branch = 0.toByte))
    assertContractFalse("C-3 not selected", evaluateC2(branch = 2.toByte))
    assertContractFalse("unknown branch", evaluateC2(branch = 3.toByte))
    assertContractFalse("state at input 1", evaluateC2(stateAtInputOne = true))
    assertContractFalse(
      "second Claim cannot share the first Claim payout",
      evaluateC2(stateAtInputOne = true, prefixInputIsClaim = true))
    assertContractFalse(
      "three inputs",
      evaluateC2(externalInputValue = Some(1000000L), includeThirdInput = true))
    assertContractFalse("data input", evaluateC2(includeDataInput = true))
    assertContractFalse("extra output", evaluateC2(appendExtraOutput = true))
    assertContractFalse(
      "token-bearing external input",
      evaluateC2(
        externalInputValue = Some(1000000L),
        externalInputTokens = ArraySeq((alternateTokenId, 1L): Token)))
    assertContractFalse("change without external input", evaluateC2(changeValue = Some(1L)))

    assertEvaluationFailure(
      "missing branch",
      evaluateC2(extensionValuesOverride = Some(Map.empty)))
    assertEvaluationFailure(
      "wrong-typed branch",
      evaluateC2(extensionValuesOverride = Some(Map(0.toByte -> IntConstant(1)))))
  }

  property("Claim C-2 does not evaluate Bitcoin proof vars 1-6") {
    val unrelated = (1 to 6).map(id => id.toByte -> IntConstant(id)).toMap

    assertContractTrue("wrong-typed vars 1-6", evaluateC2(extraContextVars = unrelated))
  }

  property("Claim C-2 fixes buyer, collateral, fee, and change shapes") {
    assertContractFalse("wrong buyer", evaluateC2(buyerTree = alternatePayoutTree))
    assertContractFalse("missing collateral", evaluateC2(buyerTokens = ArraySeq.empty[Token]))
    assertContractFalse(
      "wrong collateral id",
      evaluateC2(buyerTokens = ArraySeq((alternateTokenId, collateralAmount): Token)))
    assertContractFalse(
      "payout collateral amount differs from Claim commitment",
      evaluateC2(buyerTokens = ArraySeq((rsBtcTokenId, collateralAmount - 1L): Token)))
    assertContractFalse(
      "extra payout token",
      evaluateC2(buyerTokens = ArraySeq(
        (rsBtcTokenId, collateralAmount): Token,
        (alternateTokenId, 1L): Token)))
    assertContractFalse(
      "origin NFT preserved on terminal payout",
      evaluateC2(buyerTokens = ArraySeq(
        (rsBtcTokenId, collateralAmount): Token,
        (originNftId, 1L): Token)))
    val currentIdTokens: ErgoBox => ArraySeq[Token] = (box: ErgoBox) => ArraySeq(
      (rsBtcTokenId, collateralAmount): Token,
      (Digest32Coll @@ box.id.toArray.toColl, 1L): Token)
    assertContractFalse(
      "current Claim id reissued on terminal payout",
      evaluateC2(buyerTokensBuilder = Some(currentIdTokens)))
    assertContractFalse("wrong fee proposition", evaluateC2(feeTreeOverride = TrueTree))
    assertContractFalse(
      "fee carries token",
      evaluateC2(feeTokens = ArraySeq((originNftId, 1L): Token)))
    assertContractFalse(
      "change carries token",
      evaluateC2(
        externalInputValue = Some(1L),
        changeValue = Some(1L),
        changeTokens = ArraySeq((originNftId, 1L): Token)))
  }

  property("Claim C-2 accepts the payout freshness boundary and rejects one block older") {
    assertContractTrue(
      "oldest permitted creation height",
      evaluateC2(buyerCreationHeight = Some(d2 - maxCreationHeightLag)))
    assertContractFalse(
      "one block too old",
      evaluateC2(buyerCreationHeight = Some(d2 - maxCreationHeightLag - 1)))
  }

  property("Claim C-2 supports exact external fee and payout top-ups") {
    assertContractTrue(
      "fee uplift, payout top-up, and change",
      evaluateC2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = stateValue,
        changeValue = Some(1000000L)))
    assertContractTrue(
      "all external value consumed",
      evaluateC2(
        externalInputValue = Some(2000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = stateValue))
  }

  property("Claim C-2 rejects every unfunded or drifting value assignment") {
    assertContractFalse("fee below state contribution", evaluateC2(feeValue = stateFee - 1L))
    assertContractFalse("unfunded fee uplift", evaluateC2(feeValue = stateFee + 1L))
    assertContractFalse("unfunded payout top-up", evaluateC2(buyerValue = stateValue))
    assertContractFalse("underpaid beneficiary", evaluateC2(buyerValue = stateValue - stateFee - 1L))
    assertContractFalse(
      "external equation one nanoERG short",
      evaluateC2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = stateValue,
        changeValue = Some(999999L)))
    assertContractFalse(
      "external equation one nanoERG long",
      evaluateC2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = stateValue,
        changeValue = Some(1000001L)))
  }

  property("Claim C-2 enforces the single-beneficiary state-value floor") {
    assertContractTrue(
      "exact floor",
      evaluateC2(
        inputValue = stateFee + singlePayoutFloor,
        buyerValue = singlePayoutFloor))
    assertContractFalse(
      "one below floor",
      evaluateC2(
        inputValue = stateFee + singlePayoutFloor - 1L,
        buyerValue = singlePayoutFloor - 1L))
  }

  property("Claim state enforces payment-field sizes and numeric bounds") {
    assertContractFalse(
      "short outpoint",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R4,
        paymentRegister(outpointBytes = outpoint.take(35)))))
    assertContractFalse(
      "long outpoint",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R4,
        paymentRegister(outpointBytes = outpoint :+ 0.toByte))))
    assertContractFalse(
      "short script hash",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R4,
        paymentRegister(scriptHashBytes = scriptHash.take(31)))))
    assertContractFalse(
      "long script hash",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R4,
        paymentRegister(scriptHashBytes = scriptHash :+ 0.toByte))))
    assertContractFalse(
      "zero minimum",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(R5, LongConstant(0L))))
    assertContractFalse(
      "minimum above Bitcoin supply",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R5,
        LongConstant(2100000000000001L))))
    assertContractFalse(
      "negative D2",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(R8, IntConstant(-1))))
  }

  property("Claim state rejects missing or wrong-typed mandatory registers") {
    val registers = canonicalClaimRegisters
    assertEvaluationFailure("missing R4", evaluateC2(inputRegisters = Map.empty))
    assertEvaluationFailure(
      "missing R5",
      evaluateC2(inputRegisters = Map(R4 -> registers(R4))))
    assertEvaluationFailure(
      "missing R6",
      evaluateC2(inputRegisters = Map(R4 -> registers(R4), R5 -> registers(R5))))
    assertEvaluationFailure(
      "missing R7",
      evaluateC2(inputRegisters = Map(
        R4 -> registers(R4),
        R5 -> registers(R5),
        R6 -> registers(R6))))
    assertEvaluationFailure(
      "missing R8",
      evaluateC2(inputRegisters = registers - R8))
    assertEvaluationFailure(
      "wrong-typed R4",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(R4, IntConstant(1))))
    assertEvaluationFailure(
      "wrong-typed R8",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(R8, LongConstant(d2.toLong))))
  }

  property("Claim state fixes role identity and cross-party separation") {
    assertContractFalse(
      "buyer payout identity",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R6,
        roleRegister(identityAuthorizationInput, sellerPayoutInput))))
    assertContractFalse(
      "seller payout identity",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R6,
        roleRegister(buyerPayoutInput, identityAuthorizationInput))))
    assertContractFalse(
      "buyer authorization identity",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(identityAuthorizationInput, sellerAuthorizationInput))))
    assertContractFalse(
      "seller authorization identity",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(buyerAuthorizationInput, identityAuthorizationInput))))

    assertContractFalse(
      "buyer and seller payout collide",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R6,
        roleRegister(buyerPayoutInput, buyerPayoutInput))))
    assertContractFalse(
      "buyer payout and seller authorization collide",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(buyerAuthorizationInput, buyerPayoutInput))))
    assertContractFalse(
      "buyer authorization and seller payout collide",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(sellerPayoutInput, sellerAuthorizationInput))))
    assertContractFalse(
      "buyer and seller authorization collide",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(buyerAuthorizationInput, buyerAuthorizationInput))))

    assertContractTrue(
      "same-party payout and authorization reuse",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(buyerPayoutInput, sellerPayoutInput))))
    assertContractTrue(
      "independent alternate authorization keys",
      evaluateC2(inputRegisters = canonicalClaimRegisters.updated(
        R7,
        roleRegister(alternateAuthorizationInput, sellerAuthorizationInput))))
  }

  property("Claim state enforces the origin-NFT and rsBTC collateral vector shape") {
    assertContractFalse(
      "missing origin NFT",
      evaluateC2(inputTokens = ArraySeq((rsBtcTokenId, collateralAmount): Token)))
    assertContractFalse(
      "missing collateral",
      evaluateC2(inputTokens = ArraySeq((originNftId, 1L): Token)))
    assertContractFalse(
      "reordered tokens",
      evaluateC2(inputTokens = ArraySeq(
        (rsBtcTokenId, collateralAmount): Token,
        (originNftId, 1L): Token)))
    assertContractFalse(
      "wrong NFT quantity",
      evaluateC2(inputTokens = ArraySeq(
        (originNftId, 2L): Token,
        (rsBtcTokenId, collateralAmount): Token)))
    assertContractFalse(
      "wrong collateral id",
      evaluateC2(inputTokens = ArraySeq(
        (originNftId, 1L): Token,
        (alternateTokenId, collateralAmount): Token)))
    val alternateCollateralAmount = collateralAmount - 1L
    assertContractTrue(
      "positive collateral amount is defined by Claim state",
      evaluateC2(
        inputTokens = ArraySeq(
          (originNftId, 1L): Token,
          (rsBtcTokenId, alternateCollateralAmount): Token),
        buyerTokens = ArraySeq((rsBtcTokenId, alternateCollateralAmount): Token)))
    assertContractFalse(
      "extra state token",
      evaluateC2(inputTokens = ArraySeq(
        (originNftId, 1L): Token,
        (rsBtcTokenId, collateralAmount): Token,
        (alternateTokenId, 1L): Token)))
  }

  property("Claim C-3 canonical mutual split proves and verifies") {
    val result = evaluateC3()

    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("Claim C-3 requires both committed authorization proofs") {
    assertProofFailure(
      "missing buyer proof",
      evaluateC3(authorizationSecrets = Seq(sellerAuthorizationInput)))
    assertProofFailure(
      "missing seller proof",
      evaluateC3(authorizationSecrets = Seq(buyerAuthorizationInput)))
    assertProofFailure(
      "missing both proofs",
      evaluateC3(authorizationSecrets = Seq.empty))

    val differentMessage = fakeMessage.updated(0, (fakeMessage(0) ^ 1).toByte)
    assertContractFalse(
      "proof bound to transaction message",
      evaluateC3(verifyMessage = differentMessage))
  }

  property("Claim C-3 accepts only complete collateral partitions") {
    assertContractTrue(
      "positive-positive split",
      evaluateC3())
    assertContractTrue(
      "zero-full split",
      evaluateC3(
        buyerTokens = ArraySeq.empty[Token],
        sellerTokens = ArraySeq((rsBtcTokenId, collateralAmount): Token)))
    assertContractTrue(
      "full-zero split",
      evaluateC3(
        buyerTokens = ArraySeq((rsBtcTokenId, collateralAmount): Token),
        sellerTokens = ArraySeq.empty[Token]))
    assertRejected(
      "collateral omitted",
      evaluateC3(
        buyerTokens = ArraySeq.empty[Token],
        sellerTokens = ArraySeq.empty[Token]))
    assertRejected(
      "partition sum short",
      evaluateC3(
        buyerTokens = ArraySeq((rsBtcTokenId, 400L): Token),
        sellerTokens = ArraySeq((rsBtcTokenId, 599L): Token)))
    assertRejected(
      "partition sum long",
      evaluateC3(
        buyerTokens = ArraySeq((rsBtcTokenId, 400L): Token),
        sellerTokens = ArraySeq((rsBtcTokenId, 601L): Token)))
    assertRejected(
      "wrong partition token id",
      evaluateC3(
        buyerTokens = ArraySeq((alternateTokenId, 400L): Token),
        sellerTokens = ArraySeq((rsBtcTokenId, 600L): Token)))
    assertRejected(
      "extra partition token",
      evaluateC3(buyerTokens = ArraySeq(
        (rsBtcTokenId, 400L): Token,
        (alternateTokenId, 1L): Token)))
    assertRejected(
      "zero-valued token entry",
      Try(evaluateC3(
        buyerTokens = ArraySeq((rsBtcTokenId, 0L): Token),
        sellerTokens = ArraySeq((rsBtcTokenId, collateralAmount): Token))).flatten)
    assertRejected(
      "duplicate token entry",
      Try(evaluateC3(buyerTokens = ArraySeq(
        (rsBtcTokenId, 200L): Token,
        (rsBtcTokenId, 200L): Token))).flatten)
  }

  property("Claim C-3 is available at any height and enforces fresh payouts") {
    assertContractTrue("before D2", evaluateC3(currentHeight = d2 - 1))
    assertContractTrue("at D2", evaluateC3(currentHeight = d2))
    assertContractTrue("after D2", evaluateC3(currentHeight = d2 + 1))
    assertContractTrue(
      "oldest buyer and seller payout heights",
      evaluateC3(
        currentHeight = d2,
        buyerCreationHeight = Some(d2 - maxCreationHeightLag),
        sellerCreationHeight = Some(d2 - maxCreationHeightLag)))
    assertRejected(
      "buyer payout one block too old",
      evaluateC3(
        currentHeight = d2,
        buyerCreationHeight = Some(d2 - maxCreationHeightLag - 1)))
    assertRejected(
      "seller payout one block too old",
      evaluateC3(
        currentHeight = d2,
        sellerCreationHeight = Some(d2 - maxCreationHeightLag - 1)))
  }

  property("Claim C-3 closes topology and ignores Bitcoin proof vars 1-6") {
    assertRejected("state at input 1", evaluateC3(stateAtInputOne = true))
    assertRejected(
      "three inputs",
      evaluateC3(externalInputValue = Some(1000000L), includeThirdInput = true))
    assertRejected("data input", evaluateC3(includeDataInput = true))
    assertRejected("extra output", evaluateC3(appendExtraOutput = true))
    assertRejected(
      "token-bearing external input",
      evaluateC3(
        externalInputValue = Some(1000000L),
        externalInputTokens = ArraySeq((alternateTokenId, 1L): Token)))
    assertRejected("change without external input", evaluateC3(changeValue = Some(1L)))

    val unrelated = (1 to 6).map(id => id.toByte -> IntConstant(id)).toMap
    assertContractTrue("wrong-typed vars 1-6", evaluateC3(extraContextVars = unrelated))
  }

  property("Claim C-3 fixes payout and auxiliary output shapes") {
    assertRejected("wrong buyer", evaluateC3(buyerTree = alternatePayoutTree))
    assertRejected("wrong seller", evaluateC3(sellerTree = buyerPayoutTree))
    assertRejected("wrong fee proposition", evaluateC3(feeTreeOverride = TrueTree))
    assertRejected(
      "fee carries token",
      evaluateC3(feeTokens = ArraySeq((originNftId, 1L): Token)))
    assertRejected(
      "change carries token",
      evaluateC3(
        externalInputValue = Some(1L),
        changeValue = Some(1L),
        changeTokens = ArraySeq((originNftId, 1L): Token)))
  }

  property("Claim C-3 supports exact external fee and payout top-ups") {
    val canonicalHalf = (stateValue - stateFee) / 2L
    assertContractTrue(
      "fee uplift, payout top-up, and change",
      evaluateC3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = canonicalHalf + 1000000L,
        changeValue = Some(1000000L)))
    assertContractTrue(
      "all external value consumed",
      evaluateC3(
        externalInputValue = Some(2000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = canonicalHalf + 1000000L))
    assertContractTrue(
      "buyer output covers state baseline",
      evaluateC3(
        externalInputValue = Some(mutualPayoutFloor),
        buyerValue = stateValue - stateFee,
        sellerValue = mutualPayoutFloor))
  }

  property("Claim C-3 rejects unfunded value and enforces both payout floors") {
    val canonicalHalf = (stateValue - stateFee) / 2L
    assertRejected("fee below state contribution", evaluateC3(feeValue = stateFee - 1L))
    assertRejected("unfunded fee uplift", evaluateC3(feeValue = stateFee + 1L))
    assertRejected("unfunded payout top-up", evaluateC3(buyerValue = canonicalHalf + 1L))
    assertRejected(
      "external equation one nanoERG short",
      evaluateC3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = canonicalHalf + 1000000L,
        changeValue = Some(999999L)))
    assertRejected(
      "external equation one nanoERG long",
      evaluateC3(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = canonicalHalf + 1000000L,
        changeValue = Some(1000001L)))
    assertRejected(
      "buyer below mutual floor",
      evaluateC3(
        buyerValue = mutualPayoutFloor - 1L,
        sellerValue = stateValue - stateFee - mutualPayoutFloor + 1L))
    assertRejected(
      "seller below mutual floor",
      evaluateC3(
        buyerValue = stateValue - stateFee - mutualPayoutFloor + 1L,
        sellerValue = mutualPayoutFloor - 1L))
    assertContractTrue(
      "exact state floor",
      evaluateC3(
        inputValue = stateFee + 2L * mutualPayoutFloor,
        buyerValue = mutualPayoutFloor,
        sellerValue = mutualPayoutFloor))
    assertRejected(
      "state one below mutual floor",
      evaluateC3(
        inputValue = stateFee + 2L * mutualPayoutFloor - 1L,
        buyerValue = mutualPayoutFloor,
        sellerValue = mutualPayoutFloor - 1L))
  }

  property("Claim C-2 mutation checks isolate terminal release invariants") {
    val inputCountMutant = compileClaimMutant(
      "val inputCountOk = INPUTS.size == 1 || INPUTS.size == 2",
      "val inputCountOk = true")
    assertContractFalse(
      "input-count control",
      evaluateC2(externalInputValue = Some(1000000L), includeThirdInput = true))
    assertContractTrue(
      "input-count mutant",
      evaluateC2(
        externalInputValue = Some(1000000L),
        includeThirdInput = true,
        contractTreeOverride = Some(inputCountMutant)))

    val deadlineMutant = compileClaimMutant("HEIGHT >= d2", "true")
    assertContractFalse("deadline control", evaluateC2(currentHeight = d2 - 1))
    assertContractTrue(
      "deadline mutant",
      evaluateC2(currentHeight = d2 - 1, contractTreeOverride = Some(deadlineMutant)))

    val payoutMutant = compileClaimMutant(
      "buyerOut.propositionBytes == proveDlog(payoutKeys._1).propBytes",
      "true")
    assertContractFalse("buyer control", evaluateC2(buyerTree = alternatePayoutTree))
    assertContractTrue(
      "buyer mutant",
      evaluateC2(
        buyerTree = alternatePayoutTree,
        contractTreeOverride = Some(payoutMutant)))

    val collateralMutant = compileClaimMutant(
      "buyerToken._2 == collateral._2",
      "true")
    val wrongCollateral = ArraySeq((rsBtcTokenId, collateralAmount - 1L): Token)
    assertContractFalse("collateral control", evaluateC2(buyerTokens = wrongCollateral))
    assertContractTrue(
      "collateral mutant",
      evaluateC2(
        buyerTokens = wrongCollateral,
        contractTreeOverride = Some(collateralMutant)))

    val valueMutant = compileClaimMutant(
      "externalValue - feeUplift - buyerTopUp == changeValue",
      "true")
    val driftingValue = evaluateC2(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      buyerValue = stateValue,
      changeValue = Some(999999L))
    assertContractFalse("external value control", driftingValue)
    assertContractTrue(
      "external value mutant",
      evaluateC2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        buyerValue = stateValue,
        changeValue = Some(999999L),
        contractTreeOverride = Some(valueMutant)))

    val feeTokenMutant = compileClaimMutantAtOccurrence(
      "feeOut.tokens.size == 0",
      "true",
      occurrence = 0,
      expectedOccurrences = 2)
    val originToken = ArraySeq((originNftId, 1L): Token)
    assertContractFalse("fee-token control", evaluateC2(feeTokens = originToken))
    assertContractTrue(
      "fee-token mutant permits origin-NFT escape",
      evaluateC2(feeTokens = originToken, contractTreeOverride = Some(feeTokenMutant)))

    val changeTokenMutant = compileClaimMutantAtOccurrence(
      "changeOut.tokens.size == 0",
      "true",
      occurrence = 0,
      expectedOccurrences = 2)
    assertContractFalse(
      "change-token control",
      evaluateC2(
        externalInputValue = Some(1L),
        changeValue = Some(1L),
        changeTokens = originToken))
    assertContractTrue(
      "change-token mutant permits origin-NFT escape",
      evaluateC2(
        externalInputValue = Some(1L),
        changeValue = Some(1L),
        changeTokens = originToken,
        contractTreeOverride = Some(changeTokenMutant)))
  }

  property("Claim state mutation checks isolate key and token-vector invariants") {
    val authorizationSeparationMutant = compileClaimMutant(
      "authorizationKeys._1 != authorizationKeys._2",
      "true")
    val collidingAuthorization = canonicalClaimRegisters.updated(
      R7,
      roleRegister(buyerAuthorizationInput, buyerAuthorizationInput))
    assertContractFalse(
      "authorization separation control",
      evaluateC2(inputRegisters = collidingAuthorization))
    assertContractTrue(
      "authorization separation mutant",
      evaluateC2(
        inputRegisters = collidingAuthorization,
        contractTreeOverride = Some(authorizationSeparationMutant)))

    val tokenVectorMutant = compileClaimMutant("selfTokens.size == 2", "true")
    val extraStateToken = ArraySeq(
      (originNftId, 1L): Token,
      (rsBtcTokenId, collateralAmount): Token,
      (alternateTokenId, 1L): Token)
    assertContractFalse("token-vector control", evaluateC2(inputTokens = extraStateToken))
    assertContractTrue(
      "token-vector mutant",
      evaluateC2(
        inputTokens = extraStateToken,
        contractTreeOverride = Some(tokenVectorMutant)))
  }

  property("Claim C-3 mutation checks isolate split and authorization invariants") {
    val originToken = ArraySeq((originNftId, 1L): Token)
    val feeTokenMutant = compileClaimMutantAtOccurrence(
      "feeOut.tokens.size == 0",
      "true",
      occurrence = 1,
      expectedOccurrences = 2)
    assertRejected("fee-token control", evaluateC3(feeTokens = originToken))
    assertContractTrue(
      "fee-token mutant permits origin-NFT escape",
      evaluateC3(feeTokens = originToken, contractTreeOverride = Some(feeTokenMutant)))

    val changeTokenMutant = compileClaimMutantAtOccurrence(
      "changeOut.tokens.size == 0",
      "true",
      occurrence = 1,
      expectedOccurrences = 2)
    assertRejected(
      "change-token control",
      evaluateC3(
        externalInputValue = Some(1L),
        changeValue = Some(1L),
        changeTokens = originToken))
    assertContractTrue(
      "change-token mutant permits origin-NFT escape",
      evaluateC3(
        externalInputValue = Some(1L),
        changeValue = Some(1L),
        changeTokens = originToken,
        contractTreeOverride = Some(changeTokenMutant)))

    val partitionMutant = compileClaimMutant(
      "sellerAmount == collateral._2 - buyerAmount",
      "true")
    val shortSellerTokens = ArraySeq((rsBtcTokenId, 599L): Token)
    assertRejected(
      "partition control",
      evaluateC3(sellerTokens = shortSellerTokens))
    assertContractTrue(
      "partition mutant",
      evaluateC3(
        sellerTokens = shortSellerTokens,
        contractTreeOverride = Some(partitionMutant)))

    val buyerAuthorizationMutant = compileClaimMutant(
      "proveDlog(authorizationKeys._1) && proveDlog(authorizationKeys._2)",
      "sigmaProp(true) && proveDlog(authorizationKeys._2)")
    assertProofFailure(
      "buyer authorization control",
      evaluateC3(authorizationSecrets = Seq(sellerAuthorizationInput)))
    assertContractTrue(
      "buyer authorization mutant",
      evaluateC3(
        authorizationSecrets = Seq(sellerAuthorizationInput),
        contractTreeOverride = Some(buyerAuthorizationMutant)))

    val sellerAuthorizationMutant = compileClaimMutant(
      "proveDlog(authorizationKeys._1) && proveDlog(authorizationKeys._2)",
      "proveDlog(authorizationKeys._1) && sigmaProp(true)")
    assertProofFailure(
      "seller authorization control",
      evaluateC3(authorizationSecrets = Seq(buyerAuthorizationInput)))
    assertContractTrue(
      "seller authorization mutant",
      evaluateC3(
        authorizationSecrets = Seq(buyerAuthorizationInput),
        contractTreeOverride = Some(sellerAuthorizationMutant)))

    val sellerFloorMutant = compileClaimMutant(
      "sellerOut.value >= mutualPayoutFloor",
      "true")
    val buyerValue = stateValue - stateFee - mutualPayoutFloor + 1L
    val sellerValue = mutualPayoutFloor - 1L
    assertRejected(
      "seller floor control",
      evaluateC3(buyerValue = buyerValue, sellerValue = sellerValue))
    assertContractTrue(
      "seller floor mutant",
      evaluateC3(
        buyerValue = buyerValue,
        sellerValue = sellerValue,
        contractTreeOverride = Some(sellerFloorMutant)))
  }

  property("Claim pins provisional state-spine bytes and full-branch costs") {
    val c2 = evaluateC2().get
    val c2External = evaluateC2(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      buyerValue = stateValue,
      changeValue = Some(1000000L)).get
    val c3 = evaluateC3().get
    val c3ZeroFull = evaluateC3(
      buyerTokens = ArraySeq.empty[Token],
      sellerTokens = ArraySeq((rsBtcTokenId, collateralAmount): Token)).get
    val c3External = evaluateC3(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      buyerValue = (stateValue - stateFee) / 2L + 1000000L,
      changeValue = Some(1000000L)).get

    c2._1 shouldBe true
    c2External._1 shouldBe true
    c3._1 shouldBe true
    c3ZeroFull._1 shouldBe true
    c3External._1 shouldBe true
    claimTree.bytes.length shouldBe StateSpineTreeSize
    Base16.encode(Blake2b256.hash(claimTree.bytes)) shouldBe StateSpineTreeHash
    c2._2 shouldBe StateSpineC2Cost
    c2External._2 shouldBe StateSpineC2ExternalCost
    c3._2 shouldBe StateSpineC3Cost
    c3ZeroFull._2 shouldBe StateSpineC3ZeroFullCost
    c3External._2 shouldBe StateSpineC3ExternalCost
  }

  private def evaluateC3(
      currentHeight: Int = d2 - 50,
      inputRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] =
        canonicalClaimRegisters,
      inputValue: Long = stateValue,
      inputTokens: ArraySeq[Token] = claimTokens,
      inputCreationHeight: Int = 0,
      buyerValue: Long = (stateValue - stateFee) / 2L,
      sellerValue: Long = (stateValue - stateFee) / 2L,
      buyerTokens: ArraySeq[Token] = ArraySeq((rsBtcTokenId, 400L): Token),
      sellerTokens: ArraySeq[Token] = ArraySeq((rsBtcTokenId, 600L): Token),
      buyerTree: ErgoTree = buyerPayoutTree,
      sellerTree: ErgoTree = sellerPayoutTree,
      buyerCreationHeight: Option[Int] = None,
      sellerCreationHeight: Option[Int] = None,
      buyerRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      sellerRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      feeValue: Long = stateFee,
      feeTreeOverride: ErgoTree = feeTree,
      feeTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      feeRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      externalInputValue: Option[Long] = None,
      externalInputTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      changeValue: Option[Long] = None,
      changeTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      changeRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      appendExtraOutput: Boolean = false,
      includeThirdInput: Boolean = false,
      includeDataInput: Boolean = false,
      branch: Byte = 2.toByte,
      extraContextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty,
      extensionValuesOverride: Option[Map[Byte, EvaluatedValue[_ <: SType]]] = None,
      authorizationSecrets: Seq[DLogProverInput] = Seq(
        buyerAuthorizationInput,
        sellerAuthorizationInput),
      proofMessage: Array[Byte] = fakeMessage,
      verifyMessage: Array[Byte] = fakeMessage,
      contractTreeOverride: Option[ErgoTree] = None,
      stateAtInputOne: Boolean = false): Try[(Boolean, Long)] = {
    val contractTree = contractTreeOverride.getOrElse(claimTree)
    val stateInput = testBox(
      inputValue,
      contractTree,
      creationHeight = inputCreationHeight,
      additionalTokens = inputTokens,
      additionalRegisters = inputRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](30))),
      boxIndex = 0)
    val buyerOutput = testBox(
      buyerValue,
      buyerTree,
      creationHeight = buyerCreationHeight.getOrElse(currentHeight),
      additionalTokens = buyerTokens,
      additionalRegisters = buyerRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](31))),
      boxIndex = 0).toCandidate
    val sellerOutput = testBox(
      sellerValue,
      sellerTree,
      creationHeight = sellerCreationHeight.getOrElse(currentHeight),
      additionalTokens = sellerTokens,
      additionalRegisters = sellerRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](32))),
      boxIndex = 1).toCandidate
    val feeOutput = testBox(
      feeValue,
      feeTreeOverride,
      creationHeight = currentHeight,
      additionalTokens = feeTokens,
      additionalRegisters = feeRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](33))),
      boxIndex = 2).toCandidate

    val externalInput = testBox(
      externalInputValue.getOrElse(1000000L),
      TrueTree,
      creationHeight = currentHeight,
      additionalTokens = externalInputTokens,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](34))),
      boxIndex = 0)
    val changeOutput = changeValue.map { value =>
      testBox(
        value,
        TrueTree,
        creationHeight = currentHeight,
        additionalTokens = changeTokens,
        additionalRegisters = changeRegisters,
        transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](35))),
        boxIndex = 3).toCandidate
    }
    val extraOutput = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](36))),
      boxIndex = 4).toCandidate
    val dataBox = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](37))),
      boxIndex = 0)
    val thirdInput = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](38))),
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
    val outputs = IndexedSeq(buyerOutput, sellerOutput, feeOutput) ++ changeOutput ++
      (if (appendExtraOutput) IndexedSeq(extraOutput) else IndexedSeq.empty)
    val dataInputs = if (includeDataInput) IndexedSeq(DataInput(dataBox.id)) else IndexedSeq.empty
    val dataBoxes = if (includeDataInput) IndexedSeq(dataBox) else IndexedSeq.empty
    val tx = new ErgoLikeTransaction(
      orderedInputs,
      dataInputs,
      outputs)
    val selfIndex = if (stateAtInputOne) 1 else 0
    val context = ErgoLikeContextTesting(
      currentHeight = currentHeight,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = dataBoxes,
      boxesToSpend = boxesToSpend,
      spendingTransaction = tx,
      selfIndex = selfIndex,
      activatedVersion = V6SoftForkVersion)
    val prover = new ContextEnrichingTestProvingInterpreter {
      override lazy val secrets: Seq[SigmaProtocolPrivateInput[_]] = authorizationSecrets
      override lazy val contextExtenders: Map[Byte, EvaluatedValue[_ <: SType]] = extensionValues
    }
    val verifier = new ErgoLikeTestInterpreter

    prover.prove(contractTree, context, proofMessage).flatMap { proof =>
      verifier.verify(
        contractTree,
        context.withExtension(proof.extension),
        proof,
        verifyMessage)
    }
  }

  private def evaluateC2(
      currentHeight: Int = d2,
      inputRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] =
        canonicalClaimRegisters,
      inputValue: Long = stateValue,
      inputTokens: ArraySeq[Token] = claimTokens,
      inputCreationHeight: Int = 0,
      buyerValue: Long = stateValue - stateFee,
      buyerTokens: ArraySeq[Token] = ArraySeq(
        (rsBtcTokenId, collateralAmount): Token),
      buyerTokensBuilder: Option[ErgoBox => ArraySeq[Token]] = None,
      buyerTree: ErgoTree = buyerPayoutTree,
      buyerCreationHeight: Option[Int] = None,
      buyerRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      feeValue: Long = stateFee,
      feeTreeOverride: ErgoTree = feeTree,
      feeTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      feeRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      externalInputValue: Option[Long] = None,
      externalInputTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      changeValue: Option[Long] = None,
      changeTokens: ArraySeq[Token] = ArraySeq.empty[Token],
      changeRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map.empty,
      appendExtraOutput: Boolean = false,
      includeThirdInput: Boolean = false,
      includeDataInput: Boolean = false,
      branch: Byte = 1.toByte,
      extraContextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty,
      extensionValuesOverride: Option[Map[Byte, EvaluatedValue[_ <: SType]]] = None,
      contractTreeOverride: Option[ErgoTree] = None,
      stateAtInputOne: Boolean = false,
      prefixInputIsClaim: Boolean = false): Try[(Boolean, Long)] = {
    val contractTree = contractTreeOverride.getOrElse(claimTree)
    val stateInput = testBox(
      inputValue,
      contractTree,
      creationHeight = inputCreationHeight,
      additionalTokens = inputTokens,
      additionalRegisters = inputRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](20))),
      boxIndex = 0)
    val resolvedBuyerTokens = buyerTokensBuilder.map(_(stateInput)).getOrElse(buyerTokens)
    val buyerOutput = testBox(
      buyerValue,
      buyerTree,
      creationHeight = buyerCreationHeight.getOrElse(currentHeight),
      additionalTokens = resolvedBuyerTokens,
      additionalRegisters = buyerRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](21))),
      boxIndex = 0).toCandidate
    val feeOutput = testBox(
      feeValue,
      feeTreeOverride,
      creationHeight = currentHeight,
      additionalTokens = feeTokens,
      additionalRegisters = feeRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](22))),
      boxIndex = 1).toCandidate

    val externalInput = testBox(
      externalInputValue.getOrElse(1000000L),
      if (prefixInputIsClaim) contractTree else TrueTree,
      creationHeight = currentHeight,
      additionalTokens = if (prefixInputIsClaim) claimTokens else externalInputTokens,
      additionalRegisters = if (prefixInputIsClaim) canonicalClaimRegisters else Map.empty,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](23))),
      boxIndex = 0)
    val changeOutput = changeValue.map { value =>
      testBox(
        value,
        TrueTree,
        creationHeight = currentHeight,
        additionalTokens = changeTokens,
        additionalRegisters = changeRegisters,
        transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](24))),
        boxIndex = 2).toCandidate
    }
    val extraOutput = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](25))),
      boxIndex = 3).toCandidate
    val dataBox = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](26))),
      boxIndex = 0)
    val thirdInput = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](27))),
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
    val outputs = IndexedSeq(buyerOutput, feeOutput) ++ changeOutput ++
      (if (appendExtraOutput) IndexedSeq(extraOutput) else IndexedSeq.empty)
    val dataInputs = if (includeDataInput) IndexedSeq(DataInput(dataBox.id)) else IndexedSeq.empty
    val dataBoxes = if (includeDataInput) IndexedSeq(dataBox) else IndexedSeq.empty
    val tx = new ErgoLikeTransaction(
      orderedInputs,
      dataInputs,
      outputs)
    val selfIndex = if (stateAtInputOne) 1 else 0
    val context = ErgoLikeContextTesting(
      currentHeight = currentHeight,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = dataBoxes,
      boxesToSpend = boxesToSpend,
      spendingTransaction = tx,
      selfIndex = selfIndex,
      activatedVersion = V6SoftForkVersion)

    new ErgoLikeTestInterpreter().verify(
      contractTree,
      context.withExtension(extension),
      ProverResult(Array.emptyByteArray, extension),
      fakeMessage)
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

  private def assertEvaluationFailure(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isFailure shouldBe true
    }

  private def assertProofFailure(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isFailure shouldBe true
    }

  private def assertRejected(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isFailure || !result.get._1 shouldBe true
    }

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

  private def canonicalClaimRegisters:
      Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map(
    R4 -> paymentRegister(),
    R5 -> LongConstant(minSatoshis),
    R6 -> payoutKeysRegister,
    R7 -> authorizationKeysRegister,
    R8 -> IntConstant(d2))

  private def compileV6(script: String): ErgoTree =
    VersionContext.withVersions(V6SoftForkVersion, V6SoftForkVersion) {
      ErgoTree.fromProposition(
        ErgoTree.headerWithVersion(ZeroHeader, V6SoftForkVersion),
        compile(Map.empty, script).asBoolValue.toSigmaProp)
    }

  private def compileClaimMutant(target: String, replacement: String): ErgoTree = {
    val first = claimScript.indexOf(target)
    require(first >= 0, s"Mutation target not found: $target")
    require(
      claimScript.indexOf(target, first + target.length) < 0,
      s"Mutation target is not unique: $target")
    compileV6(
      claimScript.substring(0, first) ++ replacement ++
        claimScript.substring(first + target.length))
  }

  private def compileClaimMutantAtOccurrence(
      target: String,
      replacement: String,
      occurrence: Int,
      expectedOccurrences: Int): ErgoTree = {
    val matches = scala.collection.mutable.ArrayBuffer.empty[Int]
    var from = 0
    var next = claimScript.indexOf(target, from)
    while (next >= 0) {
      matches += next
      from = next + target.length
      next = claimScript.indexOf(target, from)
    }
    require(
      matches.size == expectedOccurrences,
      s"Expected $expectedOccurrences mutation targets but found ${matches.size}: $target")
    require(
      occurrence >= 0 && occurrence < matches.size,
      s"Mutation occurrence $occurrence is out of range for: $target")
    val index = matches(occurrence)
    compileV6(
      claimScript.substring(0, index) ++ replacement ++
        claimScript.substring(index + target.length))
  }

  private lazy val claimScript: String = {
    BitcoinRsBtcBasePlainFamilyPolicy.requireValidStateDeduction(stateFee)
    s"""{
       |  // Context var 0: 0 = C-1, 1 = C-2, 2 = C-3.
       |  val branch = getVar[Byte](0).get
       |  val rsBtcTokenId = fromBase16("${Base16.encode(rsBtcTokenIdBytes)}")
       |  val feePropositionBytes = fromBase16("${Base16.encode(feeTree.bytes)}")
       |  val stateFee = ${stateFee}L
       |  val singlePayoutFloor = ${singlePayoutFloor}L
       |  val mutualPayoutFloor = ${mutualPayoutFloor}L
       |  val maxCreationHeightLag = $maxCreationHeightLag
       |
       |  val payment = SELF.R4[(Coll[Byte], Coll[Byte])].get
       |  val outpoint = payment._1
       |  val scriptHash = payment._2
       |  val minSatoshis = SELF.R5[Long].get
       |  val payoutKeys = SELF.R6[(GroupElement, GroupElement)].get
       |  val authorizationKeys = SELF.R7[(GroupElement, GroupElement)].get
       |  val d2 = SELF.R8[Int].get
       |  val identity = groupGenerator.exp(0.toBigInt)
       |
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
       |                      scriptHash.size == 32 &&
       |                      minSatoshis > 0L &&
       |                      minSatoshis <= 2100000000000000L &&
       |                      roleKeysNonIdentity &&
       |                      roleSeparationOk &&
       |                      d2 >= 0 &&
       |                      selfTokens.size == 2 &&
       |                      origin._2 == 1L &&
       |                      collateral._1 == rsBtcTokenId &&
       |                      collateral._2 > 0L &&
       |                      tokenIdentityOk &&
       |                      SELF.value >= stateFee &&
       |                      SELF.value - stateFee >= singlePayoutFloor
       |
       |  val inputCountOk = INPUTS.size == 1 || INPUTS.size == 2
       |  val stateIsFirst = INPUTS.size > 0 && INPUTS(0).id == SELF.id
       |  val hasExternalInput = INPUTS.size == 2
       |  val externalInput = INPUTS.getOrElse(1, SELF)
       |  val externalInputOk = !hasExternalInput || externalInput.tokens.size == 0
       |  val commonTopologyOk = inputCountOk && stateIsFirst && externalInputOk
       |
       |  if (branch == 0) {
       |    sigmaProp(false)
       |  } else if (branch == 1) {
       |    val outputCountOk = if (hasExternalInput) {
       |      OUTPUTS.size == 2 || OUTPUTS.size == 3
       |    } else {
       |      OUTPUTS.size == 2
       |    }
       |    val topologyOk = commonTopologyOk &&
       |                     CONTEXT.dataInputs.size == 0 &&
       |                     outputCountOk
       |
       |    sigmaProp(stateSchemaOk && topologyOk && HEIGHT >= d2 && {
       |      val buyerOut = OUTPUTS(0)
       |      val feeOut = OUTPUTS(1)
       |      val hasChange = OUTPUTS.size == 3
       |      val changeOut = OUTPUTS.getOrElse(2, SELF)
       |      val buyerToken = buyerOut.tokens.getOrElse(0, (rsBtcTokenId, 0L))
       |      val creationHeightFloor = if (HEIGHT > maxCreationHeightLag) {
       |        HEIGHT - maxCreationHeightLag
       |      } else {
       |        0
       |      }
       |
       |      val buyerOutOk = buyerOut.propositionBytes == proveDlog(payoutKeys._1).propBytes &&
       |                       buyerOut.tokens.size == 1 &&
       |                       buyerToken._1 == rsBtcTokenId &&
       |                       buyerToken._2 == collateral._2 &&
       |                       buyerOut.creationInfo._1 >= creationHeightFloor &&
       |                       buyerOut.value >= singlePayoutFloor
       |      val feeOutOk = feeOut.propositionBytes == feePropositionBytes &&
       |                     feeOut.value >= stateFee &&
       |                     feeOut.tokens.size == 0
       |      val changeOutOk = !hasChange || (
       |        changeOut.value > 0L &&
       |        changeOut.tokens.size == 0)
       |
       |      val stateFundedBuyerValue = SELF.value - stateFee
       |      val buyerValueOk = buyerOut.value >= stateFundedBuyerValue
       |      val externalValue = if (hasExternalInput) externalInput.value else 0L
       |      val changeValue = if (hasChange) changeOut.value else 0L
       |      val feeUplift = feeOut.value - stateFee
       |      val buyerTopUp = buyerOut.value - stateFundedBuyerValue
       |      val externalValueOk = buyerValueOk &&
       |                            externalValue >= feeUplift &&
       |                            externalValue - feeUplift >= buyerTopUp &&
       |                            externalValue - feeUplift - buyerTopUp == changeValue
       |
       |      buyerOutOk && feeOutOk && changeOutOk && externalValueOk
       |    })
       |  } else if (branch == 2) {
       |    val outputCountOk = if (hasExternalInput) {
       |      OUTPUTS.size == 3 || OUTPUTS.size == 4
       |    } else {
       |      OUTPUTS.size == 3
       |    }
       |    val topologyOk = commonTopologyOk &&
       |                     CONTEXT.dataInputs.size == 0 &&
       |                     outputCountOk
       |
       |    sigmaProp(stateSchemaOk && topologyOk &&
       |      SELF.value - stateFee >= 2L * mutualPayoutFloor && {
       |      val buyerOut = OUTPUTS(0)
       |      val sellerOut = OUTPUTS(1)
       |      val feeOut = OUTPUTS(2)
       |      val hasChange = OUTPUTS.size == 4
       |      val changeOut = OUTPUTS.getOrElse(3, SELF)
       |      val buyerToken = buyerOut.tokens.getOrElse(0, (rsBtcTokenId, 0L))
       |      val sellerToken = sellerOut.tokens.getOrElse(0, (rsBtcTokenId, 0L))
       |      val buyerHasToken = buyerOut.tokens.size == 1
       |      val sellerHasToken = sellerOut.tokens.size == 1
       |      val buyerTokenShapeOk = buyerOut.tokens.size == 0 || (
       |        buyerHasToken &&
       |        buyerToken._1 == rsBtcTokenId &&
       |        buyerToken._2 > 0L)
       |      val sellerTokenShapeOk = sellerOut.tokens.size == 0 || (
       |        sellerHasToken &&
       |        sellerToken._1 == rsBtcTokenId &&
       |        sellerToken._2 > 0L)
       |      val buyerAmount = if (buyerHasToken) buyerToken._2 else 0L
       |      val sellerAmount = if (sellerHasToken) sellerToken._2 else 0L
       |      val tokenPartitionOk = buyerTokenShapeOk && sellerTokenShapeOk &&
       |                             buyerAmount <= collateral._2 &&
       |                             sellerAmount == collateral._2 - buyerAmount
       |      val creationHeightFloor = if (HEIGHT > maxCreationHeightLag) {
       |        HEIGHT - maxCreationHeightLag
       |      } else {
       |        0
       |      }
       |      val payoutShapeOk = buyerOut.propositionBytes ==
       |                            proveDlog(payoutKeys._1).propBytes &&
       |                          sellerOut.propositionBytes ==
       |                            proveDlog(payoutKeys._2).propBytes &&
       |                          buyerOut.value >= mutualPayoutFloor &&
       |                          sellerOut.value >= mutualPayoutFloor &&
       |                          buyerOut.creationInfo._1 >= creationHeightFloor &&
       |                          sellerOut.creationInfo._1 >= creationHeightFloor &&
       |                          tokenPartitionOk
       |      val feeOutOk = feeOut.propositionBytes == feePropositionBytes &&
       |                     feeOut.value >= stateFee &&
       |                     feeOut.tokens.size == 0
       |      val changeOutOk = !hasChange || (
       |        changeOut.value > 0L &&
       |        changeOut.tokens.size == 0)
       |
       |      val stateFundedPayout = SELF.value - stateFee
       |      val buyerCoversState = buyerOut.value >= stateFundedPayout
       |      val sellerStateRemainder = if (buyerCoversState) {
       |        0L
       |      } else {
       |        stateFundedPayout - buyerOut.value
       |      }
       |      val payoutValueOk = buyerCoversState || sellerOut.value >= sellerStateRemainder
       |      val buyerTopUp = if (buyerCoversState) {
       |        buyerOut.value - stateFundedPayout
       |      } else {
       |        0L
       |      }
       |      val sellerTopUp = if (buyerCoversState) {
       |        sellerOut.value
       |      } else {
       |        sellerOut.value - sellerStateRemainder
       |      }
       |      val externalValue = if (hasExternalInput) externalInput.value else 0L
       |      val changeValue = if (hasChange) changeOut.value else 0L
       |      val feeUplift = feeOut.value - stateFee
       |      val externalValueOk = payoutValueOk &&
       |                            externalValue >= feeUplift &&
       |                            externalValue - feeUplift >= buyerTopUp &&
       |                            externalValue - feeUplift - buyerTopUp >= sellerTopUp &&
       |                            externalValue - feeUplift - buyerTopUp - sellerTopUp ==
       |                              changeValue
       |
       |      payoutShapeOk && feeOutOk && changeOutOk && externalValueOk
       |    }) && proveDlog(authorizationKeys._1) && proveDlog(authorizationKeys._2)
       |  } else {
       |    sigmaProp(false)
       |  }
       |}""".stripMargin.replace("\r\n", "\n")
  }
}
