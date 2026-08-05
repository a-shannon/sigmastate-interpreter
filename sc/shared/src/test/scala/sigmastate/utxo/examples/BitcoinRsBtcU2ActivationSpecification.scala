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
import sigma.crypto.{BigIntegers, CryptoConstants, EcPointType}
import sigma.data.Digest32Coll
import sigma.interpreter.{ContextExtension, ProverResult}
import sigmastate._
import sigmastate.crypto.DLogProtocol.DLogProverInput
import sigmastate.crypto.SigmaProtocolPrivateInput
import sigmastate.helpers.TestingHelpers._
import sigmastate.helpers.{CompilerTestingCommons, ErgoLikeContextTesting, ErgoLikeTestInterpreter, ErgoLikeTestProvingInterpreter}
import sigmastate.interpreter.HintsBag

import java.math.BigInteger
import scala.collection.compat.immutable.ArraySeq
import scala.util.Try

/** Phase-1 composition probe for the complete U-2 activation predicate.
  *
  * This specification pins one explicit feasibility profile. It is not the
  * final lifecycle ABI or a wallet-support claim.
  */
class BitcoinRsBtcU2ActivationSpecification
  extends CompilerTestingCommons with CompilerCrossVersionProps {

  private implicit lazy val IR: TestingIRContext = new TestingIRContext

  private val CapabilityDomainHex = "4552472d525342544301000001"
  private val capabilityDomain = Base16.decode(CapabilityDomainHex).get

  private val stateValue = 100000000L
  private val stateFee = 1000000L
  private val insuredDealReserveFloor = 10000000L
  private val collateralAmount = 1000L
  private val minSatoshis = 250000L

  private val activationCutoff = 700
  private val recoveryHeight = 720
  private val d1 = 780
  private val responseMin = 100
  private val responseMax = 200

  private val nonOverlapMargin = 10
  private val minActivePaymentWindow = 50
  private val maxActivePaymentWindow = 100
  private val maxSupportedOfferAge = 1000
  private val protocolResponseFloor = 50
  private val protocolResponseCeiling = 500
  private val maxCreationHeightLag = 2

  private val Phase1TreeSize = 1494
  private val Phase1TreeHash =
    "e6ba0c08b1026cf73220b6265daaa967e04e6e80b8f8a6055d33fc3ab06ea508"
  private val Phase1CanonicalCost = 1149L
  private val Phase1ExternalCost = 1168L

  private val rsBtcTokenIdBytes = Array.fill(32)(0x11.toByte)
  private val rsBtcTokenId = Digest32Coll @@ rsBtcTokenIdBytes.toColl
  private val alternateTokenId = Digest32Coll @@ Array.fill(32)(0x33.toByte).toColl
  private val unactivatedTokens = ArraySeq(
    (rsBtcTokenId, collateralAmount): Token)

  private val outpoint = Array.tabulate(36)(i => (i + 1).toByte)
  private val scriptHash = Array.tabulate(32)(i => (i + 41).toByte)

  private val buyerPayoutInput = DLogProverInput(BigInteger.valueOf(1L))
  private val sellerPayoutInput = DLogProverInput(BigInteger.valueOf(2L))
  private val buyerAuthorizationInput = DLogProverInput(BigInteger.valueOf(3L))
  private val sellerAuthorizationInput = DLogProverInput(BigInteger.valueOf(4L))
  private val alternateAuthorizationInput = DLogProverInput(BigInteger.valueOf(5L))
  private val identityAuthorizationInput = DLogProverInput(BigInteger.ZERO)

  private val sellerCapabilityProver = new ErgoLikeTestProvingInterpreter {
    override lazy val secrets: Seq[SigmaProtocolPrivateInput[_]] =
      Seq(sellerAuthorizationInput)
  }

  private lazy val claimTargetTree = compileV6("{ sigmaProp(HEIGHT < 0) }")
  private lazy val claimTargetHash = Blake2b256.hash(claimTargetTree.bytes)
  private lazy val insuredDealTargetTree = compileV6("{ sigmaProp(HEIGHT < 1) }")
  private lazy val insuredDealTargetHash = Blake2b256.hash(insuredDealTargetTree.bytes)
  private lazy val unactivatedVaultTree = compileV6(unactivatedVaultScript)
  private lazy val feeTree = ErgoTreePredef.feeProposition()

  property("U-2 canonical activation reduces to true") {
    val result = evaluateU2()

    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("U-2 accepts both effective activation-height endpoints and rejects outside them") {
    val lower = d1 - maxActivePaymentWindow

    assertContractTrue("lower endpoint", evaluateU2(currentHeight = lower))
    assertContractTrue("upper endpoint", evaluateU2(currentHeight = activationCutoff))
    assertContractFalse("below lower endpoint", evaluateU2(currentHeight = lower - 1))
    assertContractFalse("above upper endpoint", evaluateU2(currentHeight = activationCutoff + 1))
  }

  property("U-2 supports one token-free external fee and successor top-up exactly") {
    assertContractTrue(
      "fee uplift, successor top-up, and change",
      evaluateU2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        successorValue = stateValue,
        changeValue = Some(1000000L)))
    assertContractTrue(
      "all external value consumed without change",
      evaluateU2(
        externalInputValue = Some(2000000L),
        feeValue = stateFee + 1000000L,
        successorValue = stateValue))
  }

  property("U-2 closes branch, input, data-input, and output topology") {
    assertContractFalse("state at input 1", evaluateU2(stateAtInputOne = true))
    assertContractFalse(
      "three inputs",
      evaluateU2(externalInputValue = Some(1000000L), includeThirdInput = true))
    assertContractFalse("data input", evaluateU2(includeDataInput = true))
    assertContractFalse("extra output", evaluateU2(appendExtraOutput = true))
    assertContractFalse(
      "change without external input",
      evaluateU2(changeValue = Some(1000000L)))

    val unknownWithoutCapability = evaluateU2(
      extensionValuesOverride = Some(Map(0.toByte -> ByteConstant(2.toByte))))
    assertContractFalse("unknown branch", unknownWithoutCapability)
    assertContractFalse(
      "disabled U-1 does not read the U-2 capability",
      evaluateU2(extensionValuesOverride = Some(Map(
        0.toByte -> ByteConstant(0.toByte)))))

    assertEvaluationFailure(
      "missing branch",
      evaluateU2(extensionValuesOverride = Some(Map(
        7.toByte -> ByteArrayConstant(Array.fill(56)(0.toByte))))))
    assertEvaluationFailure(
      "wrong-typed branch",
      evaluateU2(extensionValuesOverride = Some(Map(
        0.toByte -> IntConstant(1),
        7.toByte -> ByteArrayConstant(Array.fill(56)(0.toByte))))))
    assertEvaluationFailure(
      "missing capability",
      evaluateU2(extensionValuesOverride = Some(Map(
        0.toByte -> ByteConstant(1.toByte)))))
    assertEvaluationFailure(
      "wrong-typed capability",
      evaluateU2(extensionValuesOverride = Some(Map(
        0.toByte -> ByteConstant(1.toByte),
        7.toByte -> IntConstant(1)))))
  }

  property("U-2 ignores Bitcoin proof vars 1-6") {
    val unrelated = (1 to 6).map(id => id.toByte -> IntConstant(id)).toMap

    assertContractTrue("wrong-typed vars 1-6", evaluateU2(extraContextVars = unrelated))
  }

  property("U-2 rejects malformed, replayed, or wrong-key capability envelopes") {
    val malformedBuilders: Seq[(String, ErgoBox => Array[Byte])] = Seq(
      "short" -> ((box: ErgoBox) => signCapability(box).take(55)),
      "trailing" -> ((box: ErgoBox) => signCapability(box) :+ 0.toByte),
      "altered challenge" -> ((box: ErgoBox) => {
        val proof = signCapability(box)
        proof.updated(0, (proof(0) ^ 1).toByte)
      }),
      "zero challenge" -> ((box: ErgoBox) =>
        Array.fill(24)(0.toByte) ++ signCapability(box).drop(24)),
      "zero response" -> ((box: ErgoBox) =>
        signCapability(box).take(24) ++ Array.fill(32)(0.toByte)),
      "response at group order" -> ((box: ErgoBox) =>
        signCapability(box).take(24) ++
          BigIntegers.asUnsignedByteArray(32, CryptoConstants.groupOrder)),
      "wrong domain" -> ((box: ErgoBox) =>
        signCapabilityFor(box, sellerAuthorizationInput, capabilityDomain.updated(0, 0.toByte))),
      "wrong origin id" -> ((_: ErgoBox) =>
        signMessage(
          sellerAuthorizationInput,
          capabilityDomain ++ Array.fill(32)(0x7f.toByte))),
      "wrong signer" -> ((box: ErgoBox) =>
        signCapabilityFor(box, alternateAuthorizationInput, capabilityDomain)))

    malformedBuilders.foreach { case (label, builder) =>
      assertContractFalse(label, evaluateU2(capabilityBuilder = Some(builder)))
    }
  }

  property("U-2 enforces the complete UnactivatedVault field schema") {
    val coinbaseSentinel = Array.fill(32)(0.toByte) ++ Array.fill(4)(0xff.toByte)
    val timingCases = Seq(
      "short timing" -> Array(activationCutoff, recoveryHeight, d1, responseMin),
      "negative cutoff" -> Array(-1, recoveryHeight, d1, responseMin, responseMax),
      "overlap" -> Array(activationCutoff, activationCutoff, d1, responseMin, responseMax),
      "short non-overlap" -> Array(
        activationCutoff,
        activationCutoff + nonOverlapMargin - 1,
        d1,
        responseMin,
        responseMax),
      "active window below minimum" -> Array(
        activationCutoff,
        recoveryHeight,
        activationCutoff + minActivePaymentWindow - 1,
        responseMin,
        responseMax),
      "active window above maximum" -> Array(
        activationCutoff,
        recoveryHeight,
        activationCutoff + maxActivePaymentWindow + 1,
        responseMin,
        responseMax),
      "offer horizon" -> Array(
        activationCutoff,
        maxSupportedOfferAge + 1,
        d1,
        responseMin,
        responseMax),
      "response below floor" -> Array(
        activationCutoff,
        recoveryHeight,
        d1,
        protocolResponseFloor - 1,
        responseMax),
      "reversed response" -> Array(
        activationCutoff,
        recoveryHeight,
        d1,
        responseMax,
        responseMin),
      "response above ceiling" -> Array(
        activationCutoff,
        recoveryHeight,
        d1,
        responseMin,
        protocolResponseCeiling + 1))
    def paymentCase(
        label: String,
        payment: EvaluatedValue[_ <: SType]) = (
      label,
      canonicalUnactivatedRegisters.updated(R4, payment),
      canonicalInsuredDealRegisters.updated(R4, payment))
    def minimumCase(label: String, amount: Long) = (
      label,
      canonicalUnactivatedRegisters.updated(R5, LongConstant(amount)),
      canonicalInsuredDealRegisters.updated(R5, LongConstant(amount)))
    val fieldCases = Seq(
      paymentCase("short outpoint", paymentRegister(outpoint.take(35), scriptHash)),
      paymentCase("coinbase outpoint", paymentRegister(coinbaseSentinel, scriptHash)),
      paymentCase("short script hash", paymentRegister(outpoint, scriptHash.take(31))),
      minimumCase("zero minimum", 0L),
      minimumCase("minimum above supply", 2100000000000001L),
      (
        "wrong InsuredDeal hash",
        canonicalUnactivatedRegisters.updated(
          R9, ByteArrayConstant(Array.fill(32)(0.toByte))),
        canonicalInsuredDealRegisters)) ++ timingCases.map { case (label, timing) =>
      val successorTiming = IntArrayConstant(Array(
        timing.lift(2).getOrElse(-1),
        timing.lift(3).getOrElse(-1),
        timing.lift(4).getOrElse(-1)))
      (
        label,
        canonicalUnactivatedRegisters.updated(R8, IntArrayConstant(timing)),
        canonicalInsuredDealRegisters.updated(R8, successorTiming))
    }

    fieldCases.foreach { case (label, registers, successorRegisters) =>
      assertContractFalse(
        label,
        evaluateU2(
          inputRegisters = registers,
          successorRegisters = successorRegisters))
    }

    assertContractFalse("missing collateral", evaluateU2(inputTokens = ArraySeq.empty[Token]))
    assertContractFalse(
      "zero collateral",
      evaluateU2(inputTokens = ArraySeq((rsBtcTokenId, 0L): Token)))
    assertContractFalse(
      "wrong collateral id",
      evaluateU2(inputTokens = ArraySeq((alternateTokenId, collateralAmount): Token)))
    assertContractFalse(
      "ancillary token",
      evaluateU2(inputTokens = ArraySeq(
        (rsBtcTokenId, collateralAmount): Token,
        (alternateTokenId, 1L): Token)))
  }

  property("U-2 classifies missing or wrong-typed UnactivatedVault registers as evaluation failures") {
    Seq(R4, R5, R6, R7, R8, R9).foreach { register =>
      val number = register.number
      val truncatedRegisters = canonicalUnactivatedRegisters.filter {
        case (id, _) => id.number < number
      }
      assertEvaluationFailure(
        s"missing input R$number",
        evaluateU2(inputRegisters = truncatedRegisters))
      assertEvaluationFailure(
        s"wrong-typed input R$number",
        evaluateU2(inputRegisters = canonicalUnactivatedRegisters.updated(
          register, IntConstant(number))))
    }
  }

  property("U-2 enforces role separation but permits same-party key reuse") {
    val buyerPayout = buyerPayoutInput.publicImage.value
    val sellerPayout = sellerPayoutInput.publicImage.value
    val buyerAuthorization = buyerAuthorizationInput.publicImage.value
    val sellerAuthorization = sellerAuthorizationInput.publicImage.value
    val identity = identityAuthorizationInput.publicImage.value

    val invalidCases: Seq[(String, EvaluatedValue[_ <: SType],
      EvaluatedValue[_ <: SType], Option[ErgoBox => Array[Byte]])] = Seq(
      ("identity buyer payout",
        roleRegister(identity, sellerPayout),
        roleRegister(buyerAuthorization, sellerAuthorization),
        None),
      ("identity seller payout",
        roleRegister(buyerPayout, identity),
        roleRegister(buyerAuthorization, sellerAuthorization),
        None),
      ("identity buyer authorization",
        roleRegister(buyerPayout, sellerPayout),
        roleRegister(identity, sellerAuthorization),
        None),
      ("identity seller authorization",
        roleRegister(buyerPayout, sellerPayout),
        roleRegister(buyerAuthorization, identity),
        Some((box: ErgoBox) => signCapabilityFor(
          box, identityAuthorizationInput, capabilityDomain))),
      ("same payout key",
        roleRegister(buyerPayout, buyerPayout),
        roleRegister(buyerAuthorization, sellerAuthorization),
        None),
      ("buyer payout is seller authorization",
        roleRegister(buyerPayout, sellerPayout),
        roleRegister(buyerAuthorization, buyerPayout),
        Some((box: ErgoBox) => signCapabilityFor(
          box, buyerPayoutInput, capabilityDomain))),
      ("buyer authorization is seller payout",
        roleRegister(buyerPayout, sellerPayout),
        roleRegister(sellerPayout, sellerAuthorization),
        None),
      ("same authorization key",
        roleRegister(buyerPayout, sellerPayout),
        roleRegister(sellerAuthorization, sellerAuthorization),
        None))

    invalidCases.foreach { case (label, payoutRegister, authorizationRegister, builder) =>
      val registers = canonicalUnactivatedRegisters ++ Map(
        R6 -> payoutRegister,
        R7 -> authorizationRegister)
      val successorRegisters = canonicalInsuredDealRegisters ++ Map(
        R6 -> payoutRegister,
        R7 -> authorizationRegister)
      assertContractFalse(
        label,
        evaluateU2(
          inputRegisters = registers,
          successorRegisters = successorRegisters,
          capabilityBuilder = builder))
    }

    val samePartyRegisters = canonicalUnactivatedRegisters ++ Map(
      R7 -> roleRegister(buyerPayout, sellerPayout))
    val samePartySuccessorRegisters = canonicalInsuredDealRegisters ++ Map(
      R7 -> roleRegister(buyerPayout, sellerPayout))
    assertContractTrue(
      "same-party payout and authorization keys",
      evaluateU2(
        inputRegisters = samePartyRegisters,
        successorRegisters = samePartySuccessorRegisters,
        capabilityBuilder = Some((box: ErgoBox) =>
          signCapabilityFor(box, sellerPayoutInput, capabilityDomain))))

    val alternateAuthorization = roleRegister(
      buyerAuthorization,
      alternateAuthorizationInput.publicImage.value)
    assertContractTrue(
      "alternate committed seller authorization key",
      evaluateU2(
        inputRegisters = canonicalUnactivatedRegisters.updated(
          R7, alternateAuthorization),
        successorRegisters = canonicalInsuredDealRegisters.updated(
          R7, alternateAuthorization),
        capabilityBuilder = Some((box: ErgoBox) =>
          signCapabilityFor(box, alternateAuthorizationInput, capabilityDomain))))
  }

  property("U-2 preserves every InsuredDeal field and its proposition") {
    val alternate = alternateAuthorizationInput.publicImage.value
    val successorCases = Seq(
      "payment outpoint" -> canonicalInsuredDealRegisters.updated(
        R4, paymentRegister(outpoint.updated(0, 0x7f.toByte), scriptHash)),
      "payment script hash" -> canonicalInsuredDealRegisters.updated(
        R4, paymentRegister(outpoint, scriptHash.updated(0, 0x7f.toByte))),
      "minimum satoshis" -> canonicalInsuredDealRegisters.updated(
        R5, LongConstant(minSatoshis + 1L)),
      "payout keys" -> canonicalInsuredDealRegisters.updated(
        R6, roleRegister(buyerPayoutInput.publicImage.value, alternate)),
      "authorization keys" -> canonicalInsuredDealRegisters.updated(
        R7, roleRegister(buyerAuthorizationInput.publicImage.value, alternate)),
      "timing" -> canonicalInsuredDealRegisters.updated(
        R8, IntArrayConstant(Array(d1 + 1, responseMin, responseMax))),
      "Claim hash" -> canonicalInsuredDealRegisters.updated(
        R9, ByteArrayConstant(Array.fill(32)(0x7f.toByte))))

    successorCases.foreach { case (label, registers) =>
      assertContractFalse(label, evaluateU2(successorRegisters = registers))
    }
    assertContractFalse(
      "InsuredDeal proposition",
      evaluateU2(successorTree = TrueTree))

    Seq(R4, R5, R6, R7, R8, R9).foreach { register =>
      val number = register.number
      val truncatedRegisters = canonicalInsuredDealRegisters.filter {
        case (id, _) => id.number < number
      }
      assertEvaluationFailure(
        s"missing successor R$number",
        evaluateU2(successorRegisters = truncatedRegisters))
      assertEvaluationFailure(
        s"wrong-typed successor R$number",
        evaluateU2(successorRegisters = canonicalInsuredDealRegisters.updated(
          register, IntConstant(number))))
    }
  }

  property("U-2 pins the origin NFT and rsBTC collateral exactly") {
    def tokens(
        originId: Digest32Coll,
        originAmount: Long,
        collateralId: Digest32Coll,
        amount: Long,
        appended: Option[Token] = None): ArraySeq[Token] =
      appended match {
        case Some(token) => ArraySeq(
          (originId, originAmount): Token,
          (collateralId, amount): Token,
          token)
        case None => ArraySeq(
          (originId, originAmount): Token,
          (collateralId, amount): Token)
      }

    def actualOrigin(stateInput: ErgoBox): Digest32Coll =
      Digest32Coll @@ stateInput.id.toArray.toColl

    val cases: Seq[(String, ErgoBox => ArraySeq[Token])] = Seq(
      "wrong origin id" -> ((_: ErgoBox) =>
        tokens(alternateTokenId, 1L, rsBtcTokenId, collateralAmount)),
      "zero origin amount" -> ((box: ErgoBox) =>
        tokens(actualOrigin(box), 0L, rsBtcTokenId, collateralAmount)),
      "two origin tokens" -> ((box: ErgoBox) =>
        tokens(actualOrigin(box), 2L, rsBtcTokenId, collateralAmount)),
      "wrong collateral id" -> ((box: ErgoBox) =>
        tokens(actualOrigin(box), 1L, alternateTokenId, collateralAmount)),
      "wrong collateral amount" -> ((box: ErgoBox) =>
        tokens(actualOrigin(box), 1L, rsBtcTokenId, collateralAmount - 1L)),
      "ancillary token" -> ((box: ErgoBox) =>
        tokens(
          actualOrigin(box),
          1L,
          rsBtcTokenId,
          collateralAmount,
          Some((alternateTokenId, 1L): Token))),
      "reversed token order" -> ((box: ErgoBox) => ArraySeq(
        (rsBtcTokenId, collateralAmount): Token,
        (actualOrigin(box), 1L): Token)),
      "missing origin" -> ((_: ErgoBox) =>
        ArraySeq((rsBtcTokenId, collateralAmount): Token)),
      "missing collateral" -> ((box: ErgoBox) =>
        ArraySeq((actualOrigin(box), 1L): Token)))

    cases.foreach { case (label, builder) =>
      assertContractFalse(
        label,
        evaluateU2(successorTokensBuilder = Some(builder)))
    }
  }

  property("U-2 bounds successor creation height") {
    val floor = 690 - maxCreationHeightLag

    assertContractTrue(
      "creation-height floor",
      evaluateU2(successorCreationHeight = Some(floor)))
    assertContractTrue(
      "current creation height",
      evaluateU2(successorCreationHeight = Some(690)))
    assertContractFalse(
      "stale creation height",
      evaluateU2(successorCreationHeight = Some(floor - 1)))
    assertContractFalse(
      "future creation height",
      evaluateU2(successorCreationHeight = Some(691)))
  }

  property("U-2 enforces state-funded fee, reserve, and external-value conservation") {
    val markerRegister = Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]](
      R4 -> ByteArrayConstant(Array(1.toByte)))

    assertContractFalse(
      "input below fee",
      evaluateU2(inputValue = stateFee - 1L, successorValue = 0L))
    assertContractFalse(
      "input below post-fee reserve",
      evaluateU2(
        inputValue = stateFee + insuredDealReserveFloor - 1L,
        successorValue = insuredDealReserveFloor - 1L))
    assertContractFalse(
      "one-nanoERG successor drain",
      evaluateU2(successorValue = stateValue - stateFee - 1L))
    assertContractFalse(
      "successor below reserve",
      evaluateU2(
        inputValue = stateFee + insuredDealReserveFloor,
        successorValue = insuredDealReserveFloor - 1L))

    assertContractFalse("wrong fee proposition", evaluateU2(feeTreeOverride = TrueTree))
    assertContractFalse("fee below state contribution", evaluateU2(feeValue = stateFee - 1L))
    assertContractFalse(
      "token-bearing fee output",
      evaluateU2(feeTokens = ArraySeq((alternateTokenId, 1L): Token)))
    assertContractTrue(
      "fee-output metadata is not value authority",
      evaluateU2(feeRegisters = markerRegister))
    assertContractFalse(
      "token-bearing external input",
      evaluateU2(
        externalInputValue = Some(1000000L),
        externalInputTokens = ArraySeq((alternateTokenId, 1L): Token),
        successorValue = stateValue))
    assertContractFalse(
      "token-bearing change",
      evaluateU2(
        externalInputValue = Some(1000000L),
        changeValue = Some(1000000L),
        changeTokens = ArraySeq((alternateTokenId, 1L): Token)))
    assertContractTrue(
      "change metadata is not value authority",
      evaluateU2(
        externalInputValue = Some(1000000L),
        changeValue = Some(1000000L),
        changeRegisters = markerRegister))
    assertContractFalse(
      "external equation one below",
      evaluateU2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        successorValue = stateValue,
        changeValue = Some(999999L)))
    assertContractFalse(
      "external equation one above",
      evaluateU2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        successorValue = stateValue,
        changeValue = Some(1000001L)))
  }

  property("U-2 capability-length rejection dominates nested cryptographic evaluation") {
    val probeTree = compileU2Mutant(
      "val canonicalInputs = response < groupOrder && holder != identity",
      "val canonicalInputs = getVar[Int](8).get == 1 && " +
        "response < groupOrder && holder != identity")
    val short = evaluateU2(
      capabilityBuilder = Some((box: ErgoBox) => signCapability(box).take(55)),
      contractTreeOverride = Some(probeTree))
    val exact = evaluateU2(contractTreeOverride = Some(probeTree))

    assertContractFalse("short envelope", short)
    assertEvaluationFailure("exact envelope reaches nested probe", exact)
  }

  property("U-2 load-bearing guards have isolated mutation regressions") {
    val belowWindow = d1 - maxActivePaymentWindow - 1
    val heightMutant = compileU2Mutant(
      "d1.toLong <= HEIGHT.toLong + maxActivePaymentWindow",
      "true")
    assertContractFalse("height control", evaluateU2(currentHeight = belowWindow))
    assertContractTrue(
      "height mutant",
      evaluateU2(currentHeight = belowWindow, contractTreeOverride = Some(heightMutant)))

    val originMutant = compileU2Mutant("successorOrigin._1 == SELF.id", "true")
    val wrongOrigin: ErgoBox => ArraySeq[Token] = (_: ErgoBox) => ArraySeq(
      (alternateTokenId, 1L): Token,
      (rsBtcTokenId, collateralAmount): Token)
    assertContractFalse(
      "origin control",
      evaluateU2(successorTokensBuilder = Some(wrongOrigin)))
    assertContractTrue(
      "origin mutant",
      evaluateU2(
        successorTokensBuilder = Some(wrongOrigin),
        contractTreeOverride = Some(originMutant)))

    val valueMutant = compileU2Mutant(
      "externalValue - feeUplift - successorTopUp == changeValue",
      "true")
    assertContractFalse(
      "value control",
      evaluateU2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        successorValue = stateValue,
        changeValue = Some(999999L)))
    assertContractTrue(
      "value mutant",
      evaluateU2(
        externalInputValue = Some(3000000L),
        feeValue = stateFee + 1000000L,
        successorValue = stateValue,
        changeValue = Some(999999L),
        contractTreeOverride = Some(valueMutant)))

    val challengeMutant = compileU2Mutant(
      "expectedChallenge == challengeBytes",
      "true")
    val alteredChallenge: ErgoBox => Array[Byte] = (box: ErgoBox) => {
      val proof = signCapability(box)
      proof.updated(0, (proof(0) ^ 1).toByte)
    }
    assertContractFalse(
      "challenge control",
      evaluateU2(capabilityBuilder = Some(alteredChallenge)))
    assertContractTrue(
      "challenge mutant",
      evaluateU2(
        capabilityBuilder = Some(alteredChallenge),
        contractTreeOverride = Some(challengeMutant)))
  }

  property("U-2 pins the provisional composed tree and full-branch costs") {
    val canonical = evaluateU2().get
    val external = evaluateU2(
      externalInputValue = Some(3000000L),
      feeValue = stateFee + 1000000L,
      successorValue = stateValue,
      changeValue = Some(1000000L)).get

    canonical._1 shouldBe true
    external._1 shouldBe true
    unactivatedVaultTree.bytes.length shouldBe Phase1TreeSize
    Base16.encode(Blake2b256.hash(unactivatedVaultTree.bytes)) shouldBe Phase1TreeHash
    canonical._2 shouldBe Phase1CanonicalCost
    external._2 shouldBe Phase1ExternalCost
  }

  private def evaluateU2(
      currentHeight: Int = 690,
      inputRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] =
        canonicalUnactivatedRegisters,
      inputValue: Long = stateValue,
      inputTokens: ArraySeq[Token] = unactivatedTokens,
      inputCreationHeight: Int = 0,
      successorRegisters: Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] =
        canonicalInsuredDealRegisters,
      successorTokensOverride: Option[ArraySeq[Token]] = None,
      successorTokensBuilder: Option[ErgoBox => ArraySeq[Token]] = None,
      successorValue: Long = stateValue - stateFee,
      successorCreationHeight: Option[Int] = None,
      successorTree: ErgoTree = insuredDealTargetTree,
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
      capabilityOverride: Option[Array[Byte]] = None,
      capabilityBuilder: Option[ErgoBox => Array[Byte]] = None,
      extraContextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty,
      extensionValuesOverride: Option[Map[Byte, EvaluatedValue[_ <: SType]]] = None,
      contractTreeOverride: Option[ErgoTree] = None,
      stateAtInputOne: Boolean = false): Try[(Boolean, Long)] = {
    val contractTree = contractTreeOverride.getOrElse(unactivatedVaultTree)
    val stateInput = testBox(
      inputValue,
      contractTree,
      creationHeight = inputCreationHeight,
      additionalTokens = inputTokens,
      additionalRegisters = inputRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](10))),
      boxIndex = 0)

    val externalInput = testBox(
      externalInputValue.getOrElse(1000000L),
      TrueTree,
      creationHeight = currentHeight,
      additionalTokens = externalInputTokens,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](11))),
      boxIndex = 0)

    val successorTokens = successorTokensBuilder.map(_(stateInput))
      .orElse(successorTokensOverride)
      .getOrElse(ArraySeq(
        (Digest32Coll @@ stateInput.id.toArray.toColl, 1L): Token,
        (rsBtcTokenId, collateralAmount): Token))
    val successor = testBox(
      successorValue,
      successorTree,
      creationHeight = successorCreationHeight.getOrElse(currentHeight),
      additionalTokens = successorTokens,
      additionalRegisters = successorRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](12))),
      boxIndex = 0).toCandidate
    val feeOutput = testBox(
      feeValue,
      feeTreeOverride,
      creationHeight = currentHeight,
      additionalTokens = feeTokens,
      additionalRegisters = feeRegisters,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](13))),
      boxIndex = 1).toCandidate
    val changeOutput = changeValue.map { value =>
      testBox(
        value,
        TrueTree,
        creationHeight = currentHeight,
        additionalTokens = changeTokens,
        additionalRegisters = changeRegisters,
        transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](14))),
        boxIndex = 2).toCandidate
    }

    val dataBox = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](15))),
      boxIndex = 0)
    val dataInputs = if (includeDataInput) IndexedSeq(DataInput(dataBox.id)) else IndexedSeq.empty
    val dataBoxes = if (includeDataInput) IndexedSeq(dataBox) else IndexedSeq.empty

    val capability = capabilityOverride.getOrElse(
      capabilityBuilder.map(_(stateInput)).getOrElse(signCapability(stateInput)))
    val defaultExtensionValues = extraContextVars ++ Map(
      0.toByte -> ByteConstant(branch),
      7.toByte -> ByteArrayConstant(capability))
    val extensionValues = extensionValuesOverride.getOrElse(defaultExtensionValues)
    val extension = ContextExtension(extensionValues)
    val stateInputRef = Input(
      stateInput.id,
      ProverResult(Array.emptyByteArray, extension))
    val externalInputRef = Input(
      externalInput.id,
      ProverResult(Array.emptyByteArray, ContextExtension.empty))
    val thirdInput = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](16))),
      boxIndex = 0)
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
    val extraOutput = testBox(
      1000000L,
      TrueTree,
      creationHeight = currentHeight,
      transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(Array[Byte](17))),
      boxIndex = 3).toCandidate
    val outputs = IndexedSeq(successor, feeOutput) ++ changeOutput ++
      (if (appendExtraOutput) IndexedSeq(extraOutput) else IndexedSeq.empty)
    val tx = new ErgoLikeTransaction(orderedInputs, dataInputs, outputs)
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

  private def signCapability(input: ErgoBox): Array[Byte] =
    sellerCapabilityProver.signMessage(
      sellerAuthorizationInput.publicImage,
      capabilityDomain ++ input.id,
      HintsBag.empty).get

  private def signCapabilityFor(
      input: ErgoBox,
      signerInput: DLogProverInput,
      domain: Array[Byte]): Array[Byte] =
    signMessage(signerInput, domain ++ input.id)

  private def signMessage(
      signerInput: DLogProverInput,
      message: Array[Byte]): Array[Byte] = {
    val prover = new ErgoLikeTestProvingInterpreter {
      override lazy val secrets: Seq[SigmaProtocolPrivateInput[_]] = Seq(signerInput)
    }
    prover.signMessage(signerInput.publicImage, message, HintsBag.empty).get
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
      first: EcPointType,
      second: EcPointType): EvaluatedValue[_ <: SType] =
    pairConstant(
      GroupElementConstant(first).value,
      GroupElementConstant(second).value,
      SGroupElement,
      SGroupElement)

  private val payoutKeysRegister = pairConstant(
    GroupElementConstant(buyerPayoutInput.publicImage.value).value,
    GroupElementConstant(sellerPayoutInput.publicImage.value).value,
    SGroupElement,
    SGroupElement)
  private val authorizationKeysRegister = pairConstant(
    GroupElementConstant(buyerAuthorizationInput.publicImage.value).value,
    GroupElementConstant(sellerAuthorizationInput.publicImage.value).value,
    SGroupElement,
    SGroupElement)

  private def canonicalUnactivatedRegisters:
      Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map(
    R4 -> paymentRegister(),
    R5 -> LongConstant(minSatoshis),
    R6 -> payoutKeysRegister,
    R7 -> authorizationKeysRegister,
    R8 -> IntArrayConstant(Array(
      activationCutoff,
      recoveryHeight,
      d1,
      responseMin,
      responseMax)),
    R9 -> ByteArrayConstant(insuredDealTargetHash))

  private def canonicalInsuredDealRegisters:
      Map[NonMandatoryRegisterId, EvaluatedValue[_ <: SType]] = Map(
    R4 -> paymentRegister(),
    R5 -> LongConstant(minSatoshis),
    R6 -> payoutKeysRegister,
    R7 -> authorizationKeysRegister,
    R8 -> IntArrayConstant(Array(d1, responseMin, responseMax)),
    R9 -> ByteArrayConstant(claimTargetHash))

  private def compileV6(script: String): ErgoTree =
    VersionContext.withVersions(V6SoftForkVersion, V6SoftForkVersion) {
      ErgoTree.fromProposition(
        ErgoTree.headerWithVersion(ZeroHeader, V6SoftForkVersion),
        compile(Map.empty, script).asBoolValue.toSigmaProp)
    }

  private def compileU2Mutant(target: String, replacement: String): ErgoTree = {
    val first = unactivatedVaultScript.indexOf(target)
    require(first >= 0, s"Mutation target not found: $target")
    require(
      unactivatedVaultScript.indexOf(target, first + target.length) < 0,
      s"Mutation target is not unique: $target")
    compileV6(
      unactivatedVaultScript.substring(0, first) ++ replacement ++
        unactivatedVaultScript.substring(first + target.length))
  }

  private lazy val unactivatedVaultScript: String = {
    BitcoinRsBtcBasePlainFamilyPolicy.requireValidStateDeduction(stateFee)
    s"""{
      |  // Context var 0: 0 = U-1, 1 = U-2. This Phase-1 slice enables U-2.
      |  val branch = getVar[Byte](0).get
      |  val rsBtcTokenId = fromBase16("${Base16.encode(rsBtcTokenIdBytes)}")
      |  val expectedInsuredDealHash = fromBase16("${Base16.encode(insuredDealTargetHash)}")
      |  val expectedClaimHash = fromBase16("${Base16.encode(claimTargetHash)}")
      |  val feePropositionBytes = fromBase16("${Base16.encode(feeTree.bytes)}")
      |  val stateFee = ${stateFee}L
      |  val insuredDealReserveFloor = ${insuredDealReserveFloor}L
      |  val maxCreationHeightLag = $maxCreationHeightLag
      |  val nonOverlapMargin = ${nonOverlapMargin}L
      |  val minActivePaymentWindow = ${minActivePaymentWindow}L
      |  val maxActivePaymentWindow = ${maxActivePaymentWindow}L
      |  val maxSupportedOfferAge = ${maxSupportedOfferAge}L
      |  val protocolResponseFloor = $protocolResponseFloor
      |  val protocolResponseCeiling = $protocolResponseCeiling
      |
      |  val payment = SELF.R4[(Coll[Byte], Coll[Byte])].get
      |  val outpoint = payment._1
      |  val scriptHash = payment._2
      |  val minSatoshis = SELF.R5[Long].get
      |  val payoutKeys = SELF.R6[(GroupElement, GroupElement)].get
      |  val authorizationKeys = SELF.R7[(GroupElement, GroupElement)].get
      |  val timing = SELF.R8[Coll[Int]].get
      |  val insuredDealHash = SELF.R9[Coll[Byte]].get
      |
      |  val activationCutoff = timing.getOrElse(0, -1)
      |  val recoveryHeight = timing.getOrElse(1, -1)
      |  val d1 = timing.getOrElse(2, -1)
      |  val responseMin = timing.getOrElse(3, -1)
      |  val responseMax = timing.getOrElse(4, -1)
      |  val activeWindow = d1.toLong - activationCutoff.toLong
      |  val timingOk = timing.size == 5 &&
      |                 activationCutoff >= 0 &&
      |                 activationCutoff < recoveryHeight &&
      |                 recoveryHeight.toLong - activationCutoff.toLong >= nonOverlapMargin &&
      |                 activeWindow >= minActivePaymentWindow &&
      |                 activeWindow <= maxActivePaymentWindow &&
      |                 recoveryHeight.toLong <=
      |                   SELF.creationInfo._1.toLong + maxSupportedOfferAge &&
      |                 protocolResponseFloor <= responseMin &&
      |                 responseMin <= responseMax &&
      |                 responseMax <= protocolResponseCeiling
      |
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
      |  val collateral = selfTokens.getOrElse(0, (rsBtcTokenId, 0L))
      |  val stateSchemaOk = outpoint.size == 36 &&
      |                      !coinbaseSentinel &&
      |                      scriptHash.size == 32 &&
      |                      minSatoshis > 0L &&
      |                      minSatoshis <= 2100000000000000L &&
      |                      roleKeysNonIdentity &&
      |                      roleSeparationOk &&
      |                      timingOk &&
      |                      insuredDealHash == expectedInsuredDealHash &&
      |                      selfTokens.size == 1 &&
      |                      collateral._1 == rsBtcTokenId &&
      |                      collateral._2 > 0L &&
      |                      SELF.value >= stateFee &&
      |                      SELF.value - stateFee >= insuredDealReserveFloor
      |
      |  if (branch == 1) {
      |    val capability = getVar[Coll[Byte]](7).get
      |    val capabilityLengthOk = capability.size == 56
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
      |    val activationHeightOk = HEIGHT <= activationCutoff &&
      |                             d1.toLong <= HEIGHT.toLong + maxActivePaymentWindow
      |
      |    sigmaProp(capabilityLengthOk && stateSchemaOk && topologyOk && activationHeightOk && {
      |      val successor = OUTPUTS(0)
      |      val feeOut = OUTPUTS(1)
      |      val hasChange = OUTPUTS.size == 3
      |      val changeOut = OUTPUTS.getOrElse(2, SELF)
      |
      |      val successorPayment = successor.R4[(Coll[Byte], Coll[Byte])].get
      |      val successorMinSatoshis = successor.R5[Long].get
      |      val successorPayoutKeys = successor.R6[(GroupElement, GroupElement)].get
      |      val successorAuthorizationKeys = successor.R7[(GroupElement, GroupElement)].get
      |      val successorTiming = successor.R8[Coll[Int]].get
      |      val successorClaimHash = successor.R9[Coll[Byte]].get
      |      val successorOrigin = successor.tokens.getOrElse(0, (rsBtcTokenId, 0L))
      |      val successorCollateral = successor.tokens.getOrElse(1, (rsBtcTokenId, 0L))
      |      val successorHeight = successor.creationInfo._1
      |      val creationHeightFloor = if (HEIGHT > maxCreationHeightLag) {
      |        HEIGHT - maxCreationHeightLag
      |      } else {
      |        0
      |      }
      |      val successorHeightOk = successorHeight >= creationHeightFloor &&
      |                              successorHeight <= HEIGHT
      |      val successorFieldsOk = blake2b256(successor.propositionBytes) ==
      |                                expectedInsuredDealHash &&
      |                              successorPayment == payment &&
      |                              successorMinSatoshis == minSatoshis &&
      |                              successorPayoutKeys == payoutKeys &&
      |                              successorAuthorizationKeys == authorizationKeys &&
      |                              successorTiming == Coll[Int](d1, responseMin, responseMax) &&
      |                              successorClaimHash == expectedClaimHash &&
      |                              successorHeightOk
      |      val successorTokensOk = successor.tokens.size == 2 &&
      |                              successorOrigin._1 == SELF.id &&
      |                              successorOrigin._2 == 1L &&
      |                              successorCollateral._1 == rsBtcTokenId &&
      |                              successorCollateral._2 == collateral._2
      |      val feeOutOk = feeOut.propositionBytes == feePropositionBytes &&
      |                     feeOut.value >= stateFee &&
      |                     feeOut.tokens.size == 0
      |      val changeOutOk = !hasChange || (
      |        changeOut.value > 0L &&
      |        changeOut.tokens.size == 0)
      |
      |      val successorBase = SELF.value - stateFee
      |      val successorValueOk = successor.value >= successorBase &&
      |                             successor.value >= insuredDealReserveFloor
      |      val externalValue = if (hasExternalInput) externalInput.value else 0L
      |      val changeValue = if (hasChange) changeOut.value else 0L
      |      val feeUplift = feeOut.value - stateFee
      |      val successorTopUp = successor.value - successorBase
      |      val externalValueOk = successorValueOk &&
      |                            externalValue >= feeUplift &&
      |                            externalValue - feeUplift >= successorTopUp &&
      |                            externalValue - feeUplift - successorTopUp == changeValue
      |      val outputShapeOk = successorFieldsOk && successorTokensOk &&
      |                          feeOutOk && changeOutOk && externalValueOk
      |
      |      outputShapeOk && {
      |        val challengeBytes = capability.slice(0, 24)
      |        val responseBytes = capability.slice(24, 56)
      |        val challenge = Global.fromBigEndianBytes[UnsignedBigInt](challengeBytes)
      |        val response = Global.fromBigEndianBytes[UnsignedBigInt](responseBytes)
      |        val groupOrder = unsignedBigInt("${CryptoConstants.groupOrder}")
      |        val holder = authorizationKeys._2
      |        val canonicalInputs = response < groupOrder && holder != identity
      |
      |        canonicalInputs && {
      |          val commitment = groupGenerator.expUnsigned(response)
      |            .multiply(holder.expUnsigned(challenge).negate)
      |          val fiatShamirBytes = fromBase16("010027100108cd") ++
      |            holder.getEncoded ++ fromBase16("73000021") ++ commitment.getEncoded
      |          val message = fromBase16("$CapabilityDomainHex") ++ SELF.id
      |          val expectedChallenge = blake2b256(fiatShamirBytes ++ message).slice(0, 24)
      |          expectedChallenge == challengeBytes
      |        }
      |      }
      |    })
      |  } else {
      |    sigmaProp(false)
      |  }
      |}""".stripMargin.replace("\r\n", "\n")
  }
}
