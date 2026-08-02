package sigmastate.utxo.examples

import org.ergoplatform.ErgoBox.R4
import org.ergoplatform._
import scorex.crypto.hash.{Blake2b256, Sha256}
import scorex.util.ModifierId
import scorex.util.encode.Base16
import sigma.VersionContext
import sigma.VersionContext.V6SoftForkVersion
import sigma.ast.ErgoTree.ZeroHeader
import sigma.ast._
import sigma.ast.syntax._
import sigma.crypto.{BigIntegers, CryptoConstants, CryptoContext, EcPointType}
import sigma.data.ProveDlog
import sigma.interpreter.{ContextExtension, ProverResult}
import sigma.serialization.GroupElementSerializer
import sigmastate._
import sigmastate.crypto.DLogProtocol.{DLogProverInput, FirstDLogProverMessage}
import sigmastate.crypto.{CryptoFunctions, SigmaProtocolPrivateInput}
import sigmastate.helpers.TestingHelpers._
import sigmastate.helpers.{CompilerTestingCommons, ErgoLikeContextTesting, ErgoLikeTestInterpreter, ErgoLikeTestProvingInterpreter}
import sigmastate.interpreter.HintsBag

import java.math.BigInteger
import java.nio.charset.StandardCharsets
import scala.util.Try

/** Non-normative feasibility probe for the detached U-2 activation capability.
  *
  * The candidate verifiers remain independent of the lifecycle contracts and ABI.
  */
class BitcoinRsBtcActivationCapabilityFeasibilitySpecification
  extends CompilerTestingCommons with CompilerCrossVersionProps {

  private implicit lazy val IR: TestingIRContext = new TestingIRContext

  // "ERG-RSBTC" || version 1 || Ergo mainnet || Bitcoin mainnet || U-2 activation.
  private val CapabilityDomainHex = "4552472d525342544301000001"
  private val capabilityDomain = Base16.decode(CapabilityDomainHex).get
  private val Bip340ChallengeTag = "BIP0340/challenge"
  private val Bip340ChallengeTagHashHex = Base16.encode(
    Sha256.hash(Bip340ChallengeTag.getBytes(StandardCharsets.UTF_8)))
  private val Secp256k1FieldPrime =
    "115792089237316195423570985008687907853269984665640564039457584007908834671663"
  private val holderSecret = new BigInteger(
    "29182557886782426272937726427992863799856075118578590413181215670663537724842")
  private val holderNonce = new BigInteger(
    "38578371320453794620695132567889106709655726142926070685166171385030337685019")
  private val holderInput = DLogProverInput(holderSecret)
  private val holder = holderInput.publicImage

  private lazy val sigmaMessageProofTree = compileV6(sigmaMessageProofScript)
  private lazy val sigmaMessageLengthGuardTree = compileV6(sigmaMessageLengthGuardScript)
  private lazy val originBox = capabilityBox(
    holder,
    capabilityDomain)
  private lazy val alternateOriginBox = capabilityBox(
    holder,
    capabilityDomain :+ 1.toByte)
  private lazy val originId: Array[Byte] = originBox.id
  private lazy val capabilityMessage = capabilityDomain ++ originId
  private lazy val sigmaMessageFiatShamirBytes = deterministicSigmaFiatShamirBytes()
  private lazy val sigmaMessageProof = deterministicSigmaMessageProof(capabilityMessage)
  private val bip340Vector0PublicKey = Base16.decode(
    "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9").get
  private val bip340Vector0Message = Array.fill(32)(0.toByte)
  private val bip340Vector0Signature = Base16.decode(
    "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215" +
      "25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0").get
  private val bip340Vector0Holder = ProveDlog(CryptoContext.default.decodePoint(
    Array(2.toByte) ++ bip340Vector0PublicKey))
  private lazy val bip340PrimitiveTree = compileV6(bip340VerifierScript(
    "getVar[Coll[Byte]](8).get"))
  private lazy val bip340CapabilityTree = compileV6(bip340VerifierScript(
    s"""sha256(fromBase16("$CapabilityDomainHex") ++ SELF.id)"""))
  private lazy val bip340LengthGuardTree = compileV6(bip340LengthGuardScript)
  private lazy val bip340Vector0Box = capabilityBox(
    bip340Vector0Holder,
    capabilityDomain :+ 4.toByte,
    bip340PrimitiveTree)
  private lazy val bip340OriginBox = capabilityBox(
    holder,
    capabilityDomain :+ 5.toByte,
    bip340CapabilityTree)
  private lazy val bip340AlternateOriginBox = capabilityBox(
    holder,
    capabilityDomain :+ 6.toByte,
    bip340CapabilityTree)
  private lazy val bip340CapabilityMessage = Sha256.hash(
    capabilityDomain ++ bip340OriginBox.id)
  private lazy val bip340Capability = deterministicBip340Signature(
    bip340CapabilityMessage)

  private def capabilityBox(
      key: ProveDlog,
      transactionSeed: Array[Byte],
      tree: ErgoTree = sigmaMessageProofTree): ErgoBox = capabilityBoxWithRegisters(
    Map(R4 -> GroupElementConstant(key.value)),
    transactionSeed,
    tree)

  private def capabilityBoxWithRegisters(
      registers: ErgoBox.AdditionalRegisters,
      transactionSeed: Array[Byte],
      tree: ErgoTree): ErgoBox = testBox(
    value = 100000000L,
    ergoTree = tree,
    creationHeight = 0,
    additionalRegisters = registers,
    transactionId = ModifierId @@ Base16.encode(Blake2b256.hash(transactionSeed)),
    boxIndex = 0)

  property("Candidate A probe compiles under Sigma V6") {
    sigmaMessageProofTree.version shouldBe V6SoftForkVersion
  }

  property("Candidate A deterministic fixture agrees with the Sigma off-chain verifier") {
    sigmaMessageProof.length shouldBe 56
    new ErgoLikeTestInterpreter()
      .verifySignature(holder, capabilityMessage, sigmaMessageProof)(null) shouldBe true
  }

  property("Candidate A ABI tuple has an exact golden encoding") {
    val actual = Seq(
      s"holder=${Base16.encode(holder.pkBytes)}",
      s"originId=${Base16.encode(originId)}",
      s"message=${Base16.encode(capabilityMessage)}",
      s"fiatShamir=${Base16.encode(sigmaMessageFiatShamirBytes)}",
      s"proof=${Base16.encode(sigmaMessageProof)}",
      s"treeSha256=${Base16.encode(Sha256.hash(sigmaMessageProofTree.bytes))}"
    ).mkString("\n")

    actual shouldBe
      """holder=033536cee5c33fd25d915336f03c1a81993533501f36e6d3d201682ea8df9faedb
        |originId=594fe74de2705ed110b12a0dd57b04fab0e765317961813a47908e5e8f4dc1b6
        |message=4552472d525342544301000001594fe74de2705ed110b12a0dd57b04fab0e765317961813a47908e5e8f4dc1b6
        |fiatShamir=010027100108cd033536cee5c33fd25d915336f03c1a81993533501f36e6d3d201682ea8df9faedb7300002102f848f8efad2756cf409750d2a70d884761dafe5de07073fce5dc5afa2204df77
        |proof=d18b53a5be0699f048189bd82dffd62fc4574540fa9547b300dc22a4d739b0fcce8b494ec685fda9f56f19391445529da9aa6c932aff6d64
        |treeSha256=619dcefc7807591b0bb418825c7da4cabcb7016b3052f0bb404f648176caa9dd""".stripMargin
    sigmaMessageProof.take(24) shouldBe CryptoFunctions.hashFn(
      sigmaMessageFiatShamirBytes ++ capabilityMessage)
  }

  property("Candidate A core ProverInterpreter signMessage path emits a wire-compatible envelope") {
    val signer = new ErgoLikeTestProvingInterpreter {
      override lazy val secrets: Seq[SigmaProtocolPrivateInput[_]] = Seq(holderInput)
    }
    // Captured from ProverInterpreter.signMessage against this exact key and message.
    val goldenProof = Base16.decode(
      "b91f53e2b52b69f0049746e184c298522cc9449a0a4ff0a6a6b621dfdf3af984" +
        "5ecf0b7900ada7c23f1068097ea2dfc26bb4b10c87ab11ee").get
    val proof = signer.signMessage(holder, capabilityMessage, HintsBag.empty).get

    goldenProof.length shouldBe 56
    signer.verifySignature(holder, capabilityMessage, goldenProof)(null) shouldBe true
    verifyCapability(originBox, sigmaMessageProofTree, goldenProof).get._1 shouldBe true
    proof.length shouldBe 56
    signer.verifySignature(holder, capabilityMessage, proof)(null) shouldBe true
    verifyCapability(originBox, sigmaMessageProofTree, proof).get._1 shouldBe true
  }

  property("Candidate A canonical proof verifies on-chain") {
    val result = verifyCapability(originBox, sigmaMessageProofTree, sigmaMessageProof)

    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("Candidate A binds every domain component and the origin box id") {
    val domainMutations = Seq(
      "protocol" -> 0,
      "version" -> 9,
      "Ergo network" -> 10,
      "Bitcoin network" -> 11,
      "purpose" -> 12)

    domainMutations.foreach { case (label, index) =>
      val wrongDomain = capabilityDomain.clone()
      wrongDomain(index) = (wrongDomain(index) ^ 1).toByte
      assertContractFalse(
        label,
        verifyCapability(
          originBox,
          sigmaMessageProofTree,
          deterministicSigmaMessageProof(wrongDomain ++ originId)))
    }

    assertContractFalse(
      "origin id",
      verifyCapability(alternateOriginBox, sigmaMessageProofTree, sigmaMessageProof))
  }

  property("Candidate A rejects a wrong or identity holder key") {
    val wrongInput = DLogProverInput(holderSecret.add(BigInteger.ONE))
    val wrongKeyBox = capabilityBox(wrongInput.publicImage, capabilityDomain :+ 2.toByte)
    val proofForWrongKeyBox = deterministicSigmaMessageProof(capabilityDomain ++ wrongKeyBox.id)
    assertContractFalse(
      "wrong holder",
      verifyCapability(wrongKeyBox, sigmaMessageProofTree, proofForWrongKeyBox))

    val identitySecret = BigInteger.ZERO
    val identityInput = DLogProverInput(identitySecret)
    val identityBox = capabilityBox(identityInput.publicImage, capabilityDomain :+ 3.toByte)
    val identityProof = deterministicSigmaMessageProof(
      capabilityDomain ++ identityBox.id,
      identitySecret,
      holderNonce)
    new ErgoLikeTestInterpreter()
      .verifySignature(
        identityInput.publicImage,
        capabilityDomain ++ identityBox.id,
        identityProof)(null) shouldBe true
    assertContractFalse(
      "identity holder",
      verifyCapability(identityBox, sigmaMessageProofTree, identityProof))
  }

  property("Candidate A rejects non-canonical and altered proof envelopes") {
    val groupOrder = CryptoConstants.groupOrder
    val cases = Seq(
      "empty" -> Array.emptyByteArray,
      "short" -> sigmaMessageProof.take(55),
      "long" -> (sigmaMessageProof ++ Array[Byte](0)),
      "zero challenge" -> (Array.fill(24)(0.toByte) ++ sigmaMessageProof.drop(24)),
      "equation-invalid zero response" -> proofWithResponse(BigInteger.ZERO),
      "response at group order" -> proofWithResponse(groupOrder),
      "response above group order" -> proofWithResponse(groupOrder.add(BigInteger.ONE)))

    cases.foreach { case (label, proof) =>
      assertContractFalse(label, verifyCapability(originBox, sigmaMessageProofTree, proof))
    }
  }

  property("Candidate A pins generic trailing-byte acceptance against the exact U-2 envelope") {
    val proofWithTrailingByte = sigmaMessageProof :+ 1.toByte

    new ErgoLikeTestInterpreter()
      .verifySignature(holder, capabilityMessage, proofWithTrailingByte)(null) shouldBe true
    assertContractFalse(
      "U-2 exact envelope",
      verifyCapability(originBox, sigmaMessageProofTree, proofWithTrailingByte))
  }

  property("Candidate A preserves malformed ABI fields as evaluation failures") {
    val missingR4Box = capabilityBoxWithRegisters(
      Map.empty,
      capabilityDomain :+ 11.toByte,
      sigmaMessageProofTree)
    val wrongTypedR4Box = capabilityBoxWithRegisters(
      Map(R4 -> IntConstant(1)),
      capabilityDomain :+ 12.toByte,
      sigmaMessageProofTree)

    verifyCapability(
      missingR4Box,
      sigmaMessageProofTree,
      deterministicSigmaMessageProof(capabilityDomain ++ missingR4Box.id)).isFailure shouldBe true
    verifyCapability(
      wrongTypedR4Box,
      sigmaMessageProofTree,
      deterministicSigmaMessageProof(capabilityDomain ++ wrongTypedR4Box.id)).isFailure shouldBe true
    verifyCapabilityWithExtension(
      originBox,
      sigmaMessageProofTree,
      ContextExtension.empty).isFailure shouldBe true
    verifyCapabilityWithExtension(
      originBox,
      sigmaMessageProofTree,
      ContextExtension(Map(7.toByte -> IntConstant(1)))).isFailure shouldBe true
  }

  property("Candidate A length guard dominates nested capability evaluation") {
    val shortResult = verifyCapability(
      originBox,
      sigmaMessageLengthGuardTree,
      sigmaMessageProof.take(55))
    val exactLengthResult = verifyCapability(
      originBox,
      sigmaMessageLengthGuardTree,
      sigmaMessageProof)

    shortResult.isSuccess shouldBe true
    shortResult.get._1 shouldBe false
    exactLengthResult.isFailure shouldBe true
  }

  property("Candidate B official BIP340 vector 0 verifies on-chain") {
    // Source: bitcoin/bips, bip-0340/test-vectors.csv, vector 0.
    deterministicBip340Signature(
      bip340Vector0Message,
      BigInteger.valueOf(3L)) shouldBe bip340Vector0Signature
    verifyBip340(
      bip340Vector0Holder,
      bip340Vector0Message,
      bip340Vector0Signature).get shouldBe true
    val result = verifyCapability(
      bip340Vector0Box,
      bip340PrimitiveTree,
      bip340Vector0Signature,
      Map(8.toByte -> ByteArrayConstant(bip340Vector0Message)))

    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("Candidate B vault-bound fixture agrees with the off-chain oracle") {
    bip340CapabilityTree.version shouldBe V6SoftForkVersion
    bip340Capability.length shouldBe 64
    verifyBip340(holder, bip340CapabilityMessage, bip340Capability).get shouldBe true

    val result = verifyCapability(
      bip340OriginBox,
      bip340CapabilityTree,
      bip340Capability)
    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("Candidate B binds every domain component and the origin box id") {
    val domainMutations = Seq(
      "protocol" -> 0,
      "version" -> 9,
      "Ergo network" -> 10,
      "Bitcoin network" -> 11,
      "purpose" -> 12)

    domainMutations.foreach { case (label, index) =>
      val wrongDomain = capabilityDomain.clone()
      wrongDomain(index) = (wrongDomain(index) ^ 1).toByte
      val wrongMessage = Sha256.hash(wrongDomain ++ bip340OriginBox.id)
      assertContractFalse(
        label,
        verifyCapability(
          bip340OriginBox,
          bip340CapabilityTree,
          deterministicBip340Signature(wrongMessage)))
    }

    assertContractFalse(
      "origin id",
      verifyCapability(
        bip340AlternateOriginBox,
        bip340CapabilityTree,
        bip340Capability))
  }

  property("Candidate B rejects wrong and identity holder keys") {
    val wrongInput = DLogProverInput(holderSecret.add(BigInteger.ONE))
    val wrongKeyBox = capabilityBox(
      wrongInput.publicImage,
      capabilityDomain :+ 7.toByte,
      bip340CapabilityTree)
    val message = Sha256.hash(capabilityDomain ++ wrongKeyBox.id)
    val proof = deterministicBip340Signature(message)
    assertContractFalse(
      "wrong holder",
      verifyCapability(wrongKeyBox, bip340CapabilityTree, proof))

    val identityBox = capabilityBox(
      DLogProverInput(BigInteger.ZERO).publicImage,
      capabilityDomain :+ 8.toByte,
      bip340CapabilityTree)
    val identityMessage = Sha256.hash(capabilityDomain ++ identityBox.id)
    val proofForIdentityMessage = deterministicBip340Signature(identityMessage)
    verifyBip340(holder, identityMessage, proofForIdentityMessage).get shouldBe true
    assertContractFalse(
      "identity holder",
      verifyCapability(identityBox, bip340CapabilityTree, proofForIdentityMessage))
  }

  property("Candidate B x-only semantics identify opposite-parity group keys") {
    val oppositeHolder = ProveDlog(CryptoConstants.dlogGroup.inverseOf(holder.value))
    holder.pkBytes.head should not be oppositeHolder.pkBytes.head
    holder.pkBytes.drop(1) shouldBe oppositeHolder.pkBytes.drop(1)
    verifyBip340(holder, bip340CapabilityMessage, bip340Capability).get shouldBe true
    verifyBip340(oppositeHolder, bip340CapabilityMessage, bip340Capability).get shouldBe true
    val oppositeBox = capabilityBox(
      oppositeHolder,
      capabilityDomain :+ 9.toByte,
      bip340CapabilityTree)
    val message = Sha256.hash(capabilityDomain ++ oppositeBox.id)
    val proof = deterministicBip340Signature(message)

    val result = verifyCapability(oppositeBox, bip340CapabilityTree, proof)
    result.isSuccess shouldBe true
    result.get._1 shouldBe true
  }

  property("Candidate B rejects malformed envelopes and scalar boundaries") {
    val order = CryptoConstants.groupOrder
    val fieldPrime = new BigInteger(Secp256k1FieldPrime)
    val cases = Seq(
      "empty" -> Array.emptyByteArray,
      "short" -> bip340Capability.take(63),
      "long" -> (bip340Capability :+ 0.toByte),
      "equation-invalid zero response" -> bip340WithResponse(BigInteger.ZERO),
      "response at group order" -> bip340WithResponse(order),
      "response above group order" -> bip340WithResponse(order.add(BigInteger.ONE)),
      "r at field prime" -> bip340WithR(fieldPrime))

    cases.foreach { case (label, proof) =>
      assertContractFalse(
        label,
        verifyCapability(bip340OriginBox, bip340CapabilityTree, proof))
    }
  }

  property("Candidate B preserves malformed x-only point as an evaluation failure") {
    val publicKey = Base16.decode(
      "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659").get
    val message = Base16.decode(
      "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89").get
    val invalidPointSignature = Base16.decode(
      "4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D" +
        "69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B").get
    val key = ProveDlog(CryptoContext.default.decodePoint(Array(2.toByte) ++ publicKey))
    val box = capabilityBox(key, capabilityDomain :+ 10.toByte, bip340PrimitiveTree)

    verifyBip340(key, message, invalidPointSignature).isFailure shouldBe true
    verifyCapability(
      box,
      bip340PrimitiveTree,
      invalidPointSignature,
      Map(8.toByte -> ByteArrayConstant(message))).isFailure shouldBe true
  }

  property("Candidate B length guard dominates nested capability evaluation") {
    val shortResult = verifyCapability(
      bip340OriginBox,
      bip340LengthGuardTree,
      bip340Capability.take(63))
    val exactLengthResult = verifyCapability(
      bip340OriginBox,
      bip340LengthGuardTree,
      bip340Capability)

    shortResult.isSuccess shouldBe true
    shortResult.get._1 shouldBe false
    exactLengthResult.isFailure shouldBe true
  }

  property("Candidate probes pin serialized size and full-path reduction cost") {
    val candidateA = verifyCapability(originBox, sigmaMessageProofTree, sigmaMessageProof).get
    val candidateB = verifyCapability(
      bip340OriginBox,
      bip340CapabilityTree,
      bip340Capability).get
    val wrongA = sigmaMessageProof.clone()
    wrongA(0) = (wrongA(0) ^ 1).toByte
    val wrongB = bip340Capability.clone()
    wrongB(63) = (wrongB(63) ^ 1).toByte
    val negativeA = verifyCapability(originBox, sigmaMessageProofTree, wrongA).get
    val negativeB = verifyCapability(bip340OriginBox, bip340CapabilityTree, wrongB).get

    candidateA shouldBe (true, 406L)
    candidateB shouldBe (true, 396L)
    negativeA shouldBe (false, 406L)
    negativeB shouldBe (false, 396L)
    sigmaMessageProofTree.bytes.length shouldBe 211
    bip340CapabilityTree.bytes.length shouldBe 354
  }

  property("Candidate probes require Sigma V6") {
    val preV6 = (V6SoftForkVersion - 1).toByte

    an[sigmastate.lang.parsers.ParserException] should be thrownBy {
      compileAt(sigmaMessageProofScript, preV6)
    }
    an[sigmastate.lang.parsers.ParserException] should be thrownBy {
      compileAt(
        bip340VerifierScript(
          s"""sha256(fromBase16("$CapabilityDomainHex") ++ SELF.id)"""),
        preV6)
    }
  }

  private def deterministicSigmaMessageProof(
      message: Array[Byte],
      secret: BigInteger = holderSecret,
      nonce: BigInteger = holderNonce): Array[Byte] = {
    val group = CryptoConstants.dlogGroup
    val fiatShamirBytes = deterministicSigmaFiatShamirBytes(secret, nonce)
    val challenge = CryptoFunctions.hashFn(fiatShamirBytes ++ message)
    val challengeInteger = new BigInteger(1, challenge)
    val response = nonce
      .add(challengeInteger.multiply(secret))
      .mod(group.order)

    challenge ++ BigIntegers.asUnsignedByteArray(32, response)
  }

  private def deterministicSigmaFiatShamirBytes(
      secret: BigInteger = holderSecret,
      nonce: BigInteger = holderNonce): Array[Byte] = {
    val group = CryptoConstants.dlogGroup
    val signer = DLogProverInput(secret)
    val signerHolder = signer.publicImage
    val commitmentPoint = group.exponentiate(group.generator, nonce)
    val commitment = FirstDLogProverMessage(commitmentPoint)
    val unproven = UnprovenSchnorr(
      signerHolder,
      commitmentOpt = Some(commitment),
      randomnessOpt = Some(nonce),
      challengeOpt = None,
      simulated = false)
    val fiatShamirBytes = FiatShamirTree.toBytes(unproven)(null)
    val manualFiatShamirBytes =
      Base16.decode("010027100108cd").get ++ signerHolder.pkBytes ++
        Base16.decode("73000021").get ++ commitment.bytes

    fiatShamirBytes shouldBe manualFiatShamirBytes
    fiatShamirBytes
  }

  private def proofWithResponse(response: BigInteger): Array[Byte] =
    sigmaMessageProof.take(24) ++ BigIntegers.asUnsignedByteArray(32, response)

  private def deterministicBip340Signature(
      message: Array[Byte],
      secret: BigInteger = holderSecret,
      auxiliaryRandomness: Array[Byte] = Array.fill(32)(0.toByte)): Array[Byte] = {
    require(message.length == 32)
    require(auxiliaryRandomness.length == 32)
    val group = CryptoConstants.dlogGroup
    val order = group.order
    require(secret.signum() > 0 && secret.compareTo(order) < 0)
    val point = group.exponentiate(group.generator, secret)
    val normalizedSecret = if (hasEvenY(point)) secret else order.subtract(secret)
    val publicKey = xOnly(point)
    val maskedSecret = xor(
      BigIntegers.asUnsignedByteArray(32, normalizedSecret),
      taggedSha256("BIP0340/aux", auxiliaryRandomness))
    val nonceSeed = taggedSha256(
      "BIP0340/nonce",
      maskedSecret ++ publicKey ++ message)
    val initialNonce = new BigInteger(1, nonceSeed).mod(order)
    require(initialNonce.signum() != 0)
    val initialCommitment = group.exponentiate(group.generator, initialNonce)
    val nonce = if (hasEvenY(initialCommitment)) initialNonce
      else order.subtract(initialNonce)
    val commitment = group.exponentiate(group.generator, nonce)
    val commitmentX = xOnly(commitment)
    val challenge = new BigInteger(
      1,
      taggedSha256(
        Bip340ChallengeTag,
        commitmentX ++ publicKey ++ message)).mod(order)
    val response = nonce
      .add(challenge.multiply(normalizedSecret))
      .mod(order)

    commitmentX ++ BigIntegers.asUnsignedByteArray(32, response)
  }

  private def verifyBip340(
      key: ProveDlog,
      message: Array[Byte],
      signature: Array[Byte]): Try[Boolean] = Try {
    if (signature.length != 64 || message.length != 32 ||
        key.pkBytes.length != 33 || (key.pkBytes.head != 2 && key.pkBytes.head != 3)) {
      false
    } else {
      val group = CryptoConstants.dlogGroup
      val rBytes = signature.take(32)
      val r = new BigInteger(1, rBytes)
      val response = new BigInteger(1, signature.drop(32))
      val fieldPrime = new BigInteger(Secp256k1FieldPrime)
      if (r.compareTo(fieldPrime) >= 0 || response.compareTo(group.order) >= 0) {
        false
      } else {
        val normalizedKey = if (hasEvenY(key.value)) key.value else group.inverseOf(key.value)
        val rPoint = CryptoContext.default.decodePoint(Array(2.toByte) ++ rBytes)
        val challenge = new BigInteger(
          1,
          taggedSha256(
            Bip340ChallengeTag,
            rBytes ++ xOnly(normalizedKey) ++ message)).mod(group.order)
        val lhs = group.exponentiate(group.generator, response)
        val rhs = group.multiplyGroupElements(
          rPoint,
          group.exponentiate(normalizedKey, challenge))
        lhs == rhs
      }
    }
  }

  private def bip340WithResponse(response: BigInteger): Array[Byte] =
    bip340Capability.take(32) ++ BigIntegers.asUnsignedByteArray(32, response)

  private def bip340WithR(r: BigInteger): Array[Byte] =
    BigIntegers.asUnsignedByteArray(32, r) ++ bip340Capability.drop(32)

  private def hasEvenY(point: EcPointType): Boolean =
    GroupElementSerializer.toBytes(point).head == 2.toByte

  private def xOnly(point: EcPointType): Array[Byte] =
    GroupElementSerializer.toBytes(point).drop(1)

  private def taggedSha256(tag: String, payload: Array[Byte]): Array[Byte] = {
    val tagHash = Sha256.hash(tag.getBytes(StandardCharsets.UTF_8))
    Sha256.hash(tagHash ++ tagHash ++ payload)
  }

  private def xor(left: Array[Byte], right: Array[Byte]): Array[Byte] = {
    require(left.length == right.length)
    left.indices.map(i => (left(i) ^ right(i)).toByte).toArray
  }

  private def assertContractFalse(label: String, result: Try[(Boolean, Long)]): Unit =
    withClue(label) {
      result.isSuccess shouldBe true
      result.get._1 shouldBe false
    }

  private def verifyCapability(
      input: ErgoBox,
      tree: ErgoTree,
      capability: Array[Byte],
      additionalVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty): Try[(Boolean, Long)] = {
    val extension = ContextExtension(
      additionalVars + (7.toByte -> ByteArrayConstant(capability)))
    verifyCapabilityWithExtension(input, tree, extension)
  }

  private def verifyCapabilityWithExtension(
      input: ErgoBox,
      tree: ErgoTree,
      extension: ContextExtension): Try[(Boolean, Long)] = {
    val tx = new ErgoLikeTransaction(
      IndexedSeq(Input(input.id, ProverResult(Array.emptyByteArray, extension))),
      IndexedSeq.empty,
      IndexedSeq(input.toCandidate))
    val context = ErgoLikeContextTesting(
      currentHeight = 0,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = IndexedSeq.empty,
      boxesToSpend = IndexedSeq(input),
      spendingTransaction = tx,
      selfIndex = 0,
      activatedVersion = V6SoftForkVersion)

    new ErgoLikeTestInterpreter().verify(
      tree,
      context,
      ProverResult(Array.emptyByteArray, extension),
      fakeMessage)
  }

  private def compileV6(script: String): ErgoTree =
    compileAt(script, V6SoftForkVersion)

  private def compileAt(script: String, version: Byte): ErgoTree =
    VersionContext.withVersions(version, version) {
      ErgoTree.fromProposition(
        ErgoTree.headerWithVersion(ZeroHeader, version),
        compile(Map.empty, script).asBoolValue.toSigmaProp)
    }

  private val sigmaMessageProofScript: String =
    s"""{
       |  val holder = SELF.R4[GroupElement].get
       |  val capability = getVar[Coll[Byte]](7).get
       |  val capabilityLengthOk = capability.size == 56
       |
       |  sigmaProp(capabilityLengthOk && {
       |    val challengeBytes = capability.slice(0, 24)
       |    val responseBytes = capability.slice(24, 56)
       |    val challenge = Global.fromBigEndianBytes[UnsignedBigInt](challengeBytes)
       |    val response = Global.fromBigEndianBytes[UnsignedBigInt](responseBytes)
       |    val groupOrder = unsignedBigInt("${CryptoConstants.groupOrder}")
       |    val identity = groupGenerator.exp(0.toBigInt)
       |    val canonicalInputs = response < groupOrder && holder != identity
       |
       |    canonicalInputs && {
       |      val commitment = groupGenerator.expUnsigned(response)
       |        .multiply(holder.expUnsigned(challenge).negate)
       |      val fiatShamirBytes = fromBase16("010027100108cd") ++
       |        holder.getEncoded ++ fromBase16("73000021") ++ commitment.getEncoded
       |      val message = fromBase16("$CapabilityDomainHex") ++ SELF.id
       |      val expectedChallenge = blake2b256(fiatShamirBytes ++ message).slice(0, 24)
       |      expectedChallenge == challengeBytes
       |    }
       |  })
       |}""".stripMargin

  private val sigmaMessageLengthGuardScript: String =
    """{
      |  val capability = getVar[Coll[Byte]](7).get
      |  sigmaProp(capability.size == 56 && getVar[Int](8).get == 1)
      |}""".stripMargin

  private val bip340LengthGuardScript: String =
    """{
      |  val capability = getVar[Coll[Byte]](7).get
      |  sigmaProp(capability.size == 64 && getVar[Int](8).get == 1)
      |}""".stripMargin

  private def bip340VerifierScript(messageExpression: String): String =
    s"""{
       |  val holder = SELF.R4[GroupElement].get
       |  val capability = getVar[Coll[Byte]](7).get
       |  val message = $messageExpression
       |  val capabilityLengthOk = capability.size == 64
       |
       |  sigmaProp(capabilityLengthOk && {
       |    val rBytes = capability.slice(0, 32)
       |    val sBytes = capability.slice(32, 64)
       |    val r = Global.fromBigEndianBytes[UnsignedBigInt](rBytes)
       |    val s = Global.fromBigEndianBytes[UnsignedBigInt](sBytes)
       |    val groupOrder = unsignedBigInt("${CryptoConstants.groupOrder}")
       |    val fieldPrime = unsignedBigInt("$Secp256k1FieldPrime")
       |    val holderBytes = holder.getEncoded
       |    val prefix = holderBytes(0)
       |    val holderEncodingOk = holderBytes.size == 33 &&
       |      (prefix == 2.toByte || prefix == 3.toByte)
       |    val canonicalInputs = message.size == 32 && holderEncodingOk &&
       |      r < fieldPrime && s < groupOrder
       |
       |    canonicalInputs && {
       |      val normalizedHolder = if (prefix == 2.toByte) holder else holder.negate
       |      val rPoint = decodePoint(Coll[Byte](2.toByte) ++ rBytes)
       |      val xOnlyHolder = normalizedHolder.getEncoded.slice(1, 33)
       |      val tagHash = fromBase16("$Bip340ChallengeTagHashHex")
       |      val challengeBytes = sha256(
       |        tagHash ++ tagHash ++ rBytes ++ xOnlyHolder ++ message)
       |      val challenge = Global.fromBigEndianBytes[UnsignedBigInt](challengeBytes)
       |        .mod(groupOrder)
       |      val lhs = groupGenerator.expUnsigned(s)
       |      val rhs = rPoint.multiply(normalizedHolder.expUnsigned(challenge))
       |      lhs == rhs
       |    }
       |  })
       |}""".stripMargin
}
