package sigmastate.utxo.examples

import org.ergoplatform.ErgoBox.Token
import org.ergoplatform.ErgoBox.{R4, R5, R6, R7, R8}
import org.ergoplatform._
import scorex.crypto.authds.avltree.batch.{BatchAVLProver, Insert, Lookup}
import scorex.crypto.authds.{ADKey, ADValue}
import scorex.crypto.hash.{Blake2b256, Digest32, Sha256}
import scorex.util.ModifierId
import scorex.util.encode.Base16
import sigma.VersionContext
import sigma.VersionContext.V6SoftForkVersion
import sigma.ast.ErgoTree.ZeroHeader
import sigma.ast._
import sigma.ast.syntax._
import sigma.data.{AvlTreeFlags, CAvlTree, Digest32Coll}
import sigma.Extensions.ArrayOps
import sigma.interpreter.{ContextExtension, ProverResult}
import sigma.Coll
import sigmastate._
import sigmastate.helpers.TestingHelpers._
import sigmastate.helpers.{CompilerTestingCommons, ContextEnrichingTestProvingInterpreter, ErgoLikeContextTesting, ErgoLikeTestInterpreter}

import java.math.BigInteger
import java.nio.ByteBuffer
import scala.collection.compat.immutable.ArraySeq

/** Minimal rsBTC vault composition example.
  *
  * The vault composes the relay/Merkle inclusion predicate from
  * [[BitcoinRelayTxCheckSpecification]] with the same-output script-hash and amount
  * binding from PR #1180. Unlike the standalone amount-binding parser, the vault
  * does not pre-commit to a Bitcoin txid: the txid is derived from context variable
  * 1 and authenticated by Merkle inclusion under a header in the relay best-chain state.
  *
  * Deal-creation invariant: R4 must be a fresh, buyer-controlled, one-time Bitcoin
  * scriptPubKey hash for this vault/deal. The script must never be reused for another
  * accepted deal, concurrently or later. This uniqueness rule is not globally
  * contract-enforced; an OP_RETURN deal commitment is the natural stronger follow-up.
  *
  * This PLAIN profile does not prove that the payment happened after vault creation,
  * nor that the relay state is recent. Payment-height and relay-freshness policies are
  * separate composition layers.
  *
  * SELF registers:
  *   R4: expected SHA-256 hash of a one-time Bitcoin scriptPubKey (Coll[Byte])
  *   R5: minimum output value in satoshis (Long)
  *
  * Data inputs:
  *   index 0: relay state box carrying exactly the configured singleton NFT
  *
  * Context extension:
  *   var(1): Bitcoin transaction bytes
  *   var(2): Bitcoin header id in relay/internal hash byte order
  *   var(3): relay AVL lookup proof for the header
  *   var(4): Bitcoin Merkle proof, with direction byte + sibling hash per level
  *   var(5): stripped coinbase transaction bytes used as the authenticated depth witness
  *   var(6): coinbase Merkle proof, with the current hash on the left at every level
  */
class BitcoinRsBtcVaultSpecification extends CompilerTestingCommons with CompilerCrossVersionProps {

  private implicit lazy val IR: TestingIRContext = new TestingIRContext

  private val relayNftId = Array.fill(32)(0.toByte)
  private val relayToken = Digest32Coll @@ relayNftId.toColl
  private val relayBoxValue = 100000000L
  private val vaultBoxValue = 100000000L
  private val bitcoinHeaderHeight = 93500
  private val output1Amount = 2550000000L
  private val output2Amount = 360000000L
  private val maxBtcSatoshis = 2100000000000000L

  private lazy val vaultTree = compileV6(vaultScript)

  property("rsBTC vault composition compiles") {
    vaultTree.version shouldBe V6SoftForkVersion
  }

  property("rsBTC vault spends for relay-confirmed payment to expected script hash") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script), minSatoshis = output1Amount) shouldBe true
  }

  property("rsBTC vault accepts payment above minimum threshold") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script), minSatoshis = output1Amount - 1L) shouldBe true
  }

  property("rsBTC vault can target another output by script hash and amount") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output2Script), minSatoshis = output2Amount) shouldBe true
  }

  property("rsBTC vault binds recipient and amount to the same Bitcoin output") {
    val fixture = vaultFixture()

    // Output 1 satisfies this amount, while only output 2 satisfies this script hash.
    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output2Script),
      minSatoshis = output1Amount) shouldBe false
  }

  property("rsBTC vault rejects insufficient amount for matching script hash") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script), minSatoshis = output1Amount + 1L) shouldBe false
  }

  property("rsBTC vault rejects wrong expected script hash") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(Array[Byte](1, 2, 3)), minSatoshis = output1Amount) shouldBe false
  }

  property("rsBTC vault rejects wrong Merkle proof") {
    val fixture = vaultFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0)(1) = (proof(0)(1) ^ 1).toByte
    val wrongProof = CollectionConstant[SCollection[SByte.type]](proof.map(_.toColl).toColl, SCollection(SByte))
    val contextVars = fixture.contextVars.updated(4.toByte, wrongProof)

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects Merkle proof with invalid direction flag") {
    val fixture = vaultFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0)(0) = 2.toByte
    val wrongProof = CollectionConstant[SCollection[SByte.type]](proof.map(_.toColl).toColl, SCollection(SByte))
    val contextVars = fixture.contextVars.updated(4.toByte, wrongProof)

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects Merkle proof level with extra bytes") {
    val fixture = vaultFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0) = proof(0) :+ 0.toByte
    val wrongProof = CollectionConstant[SCollection[SByte.type]](proof.map(_.toColl).toColl, SCollection(SByte))
    val contextVars = fixture.contextVars.updated(4.toByte, wrongProof)

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects wrong coinbase Merkle proof") {
    val fixture = vaultFixture()
    val proof = fixture.coinbaseProof.map(_.toArray)
    proof(0)(1) = (proof(0)(1) ^ 1).toByte
    val contextVars = fixture.contextVars.updated(6.toByte, proofConstant(proof.map(_.toColl)))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects coinbase proof whose current hash is not the left child") {
    val fixture = vaultFixture()
    val proof = fixture.coinbaseProof.map(_.toArray)
    proof(0)(0) = 0.toByte
    val contextVars = fixture.contextVars.updated(6.toByte, proofConstant(proof.map(_.toColl)))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects unequal payment and coinbase proof depths") {
    val fixture = vaultFixture()
    val shorterCoinbaseProof = fixture.coinbaseProof.dropRight(1)
    val contextVars = fixture.contextVars.updated(6.toByte, proofConstant(shorterCoinbaseProof))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects otherwise valid Merkle proofs deeper than 32") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script, proofDepth = 33)

    fixture.merkleProof.length shouldBe 33
    fixture.coinbaseProof.length shouldBe 33
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false

    val widenedDepthMutant = compileVaultMutant(
      "val maxMerkleDepth = 32",
      "val maxMerkleDepth = 33")
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L,
      fixture.contextVars, widenedDepthMutant) shouldBe true
  }

  property("rsBTC vault rejects missing coinbase bytes") {
    val fixture = vaultFixture()

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      fixture.contextVars - 5.toByte) shouldBe false
  }

  property("rsBTC vault rejects missing coinbase proof") {
    val fixture = vaultFixture()

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      fixture.contextVars - 6.toByte) shouldBe false
  }

  property("rsBTC vault rejects each missing producer context variable") {
    val fixture = vaultFixture()

    Seq[Byte](1, 2, 3, 4).foreach { varId =>
      vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
        fixture.contextVars - varId) shouldBe false
    }
  }

  property("rsBTC vault rejects each wrong-typed producer context variable") {
    val fixture = vaultFixture()

    Seq[Byte](1, 2, 3, 4, 5, 6).foreach { varId =>
      val wrongTypedVars = fixture.contextVars.updated(varId, IntConstant(1))
      vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
        wrongTypedVars) shouldBe false
    }
  }

  property("rsBTC vault rejects a coinbase shorter than its fixed prefix") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script,
      coinbaseBytes = mainnetCoinbaseBytes().take(41))

    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false
  }

  property("rsBTC vault rejects a 64-byte coinbase depth witness") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val coinbaseBytes = valid64ByteTx()
    java.util.Arrays.fill(coinbaseBytes, 37, 41, 0xff.toByte)
    val fixture = twoTransactionVaultFixture(txBytes, script, coinbaseBytes = coinbaseBytes)

    coinbaseBytes.length shouldBe 64
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false
  }

  property("rsBTC vault rejects a depth witness with multiple coinbase inputs") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val coinbaseBytes = mainnetCoinbaseBytes()
    coinbaseBytes(4) = 2.toByte
    val fixture = twoTransactionVaultFixture(txBytes, script, coinbaseBytes = coinbaseBytes)

    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false
  }

  property("rsBTC vault rejects a depth witness with a nonzero coinbase prevout hash") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val coinbaseBytes = mainnetCoinbaseBytes()
    coinbaseBytes(5) = 1.toByte
    val fixture = twoTransactionVaultFixture(txBytes, script, coinbaseBytes = coinbaseBytes)

    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false
  }

  property("rsBTC vault rejects a depth witness without the coinbase prevout index") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val coinbaseBytes = mainnetCoinbaseBytes()
    coinbaseBytes(37) = 0.toByte
    val fixture = twoTransactionVaultFixture(txBytes, script, coinbaseBytes = coinbaseBytes)

    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false
  }

  property("rsBTC vault rejects coinbase proof levels with extra bytes") {
    val fixture = vaultFixture()
    val proof = fixture.coinbaseProof.map(_.toArray)
    proof(0) = proof(0) :+ 0.toByte
    val contextVars = fixture.contextVars.updated(6.toByte, proofConstant(proof.map(_.toColl)))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects header id absent from relay best chain") {
    val fixture = vaultFixture()
    val contextVars = fixture.contextVars
      .updated(2.toByte, ByteArrayConstant(fixture.missingHeaderId))
      .updated(3.toByte, ByteArrayConstant(fixture.missingHeaderProof))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects data input without relay NFT") {
    val fixture = vaultFixture()
    val wrongRelayFixture = fixture.copy(relayDataInput = fixture.missingRelayNftDataInput)

    vaultProves(wrongRelayFixture, Sha256.hash(fixture.output1Script), output1Amount) shouldBe false
  }

  property("rsBTC vault rejects wrong relay NFT id") {
    val fixture = vaultFixture()
    val wrongRelayFixture = fixture.copy(relayDataInput = fixture.wrongRelayNftDataInput)

    vaultProves(wrongRelayFixture, Sha256.hash(fixture.output1Script), output1Amount) shouldBe false
  }

  property("rsBTC vault rejects relay NFT quantity other than one") {
    val fixture = vaultFixture()
    val wrongRelayFixture = fixture.copy(relayDataInput = fixture.wrongRelayNftQuantityDataInput)

    vaultProves(wrongRelayFixture, Sha256.hash(fixture.output1Script), output1Amount) shouldBe false
  }

  property("rsBTC vault rejects relay data input with an additional token") {
    val fixture = vaultFixture()
    val wrongRelayFixture = fixture.copy(relayDataInput = fixture.extraRelayTokenDataInput)

    vaultProves(wrongRelayFixture, Sha256.hash(fixture.output1Script), output1Amount) shouldBe false
  }

  property("rsBTC vault rejects insufficient relay confirmations") {
    val fixture = vaultFixture(tipHeight = bitcoinHeaderHeight + 5)

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script), minSatoshis = output1Amount) shouldBe false
  }

  property("rsBTC vault rejects expected script hash with wrong length") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script).drop(1), minSatoshis = output1Amount) shouldBe false
  }

  property("rsBTC vault rejects zero minimum satoshis") {
    val fixture = vaultFixture()

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script), minSatoshis = 0L) shouldBe false
  }

  property("rsBTC vault rejects transaction bytes not matching Merkle inclusion") {
    val fixture = vaultFixture()
    val txBytes = fixture.txBytes.clone()
    txBytes(0) = (txBytes(0) ^ 1).toByte
    val contextVars = fixture.contextVars.updated(1.toByte, ByteArrayConstant(txBytes))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault rejects when relay data input zero is absent") {
    val fixture = vaultFixture()

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      includeRelayDataInput = false) shouldBe false
  }

  property("rsBTC vault rejects a display-order header id instead of the relay key order") {
    val fixture = vaultFixture()
    val contextVars = fixture.contextVars
      .updated(2.toByte, ByteArrayConstant(fixture.displayOrderHeaderId))
      .updated(3.toByte, ByteArrayConstant(fixture.displayOrderHeaderProof))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
  }

  property("rsBTC vault uses the same transaction bytes for inclusion and amount binding") {
    val fixture = vaultFixture()
    val parserOnlyTxBytes = fixture.txBytes.clone()
    parserOnlyTxBytes(0) = (parserOnlyTxBytes(0) ^ 1).toByte
    val splitWitnessVars = fixture.contextVars
      .updated(1.toByte, ByteArrayConstant(parserOnlyTxBytes))
      .updated(7.toByte, ByteArrayConstant(fixture.txBytes))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      splitWitnessVars) shouldBe false

    val splitWitnessMutant = compileVaultMutant(
      "val txId = doubleSha256(txBytes)",
      "val txId = doubleSha256(getVar[Coll[Byte]](7).get)")
    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      splitWitnessVars, splitWitnessMutant) shouldBe true
  }

  property("rsBTC vault ignores context extensions on other Ergo inputs") {
    val fixture = vaultFixture()
    val unrelatedVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map(
      1.toByte -> ByteArrayConstant(Array.fill(64)(0x7f.toByte)),
      2.toByte -> ByteArrayConstant(Array.fill(32)(0x42.toByte)),
      3.toByte -> ByteArrayConstant(Array[Byte](1, 2, 3)),
      4.toByte -> proofConstant(Array.empty[Coll[Byte]]),
      5.toByte -> ByteArrayConstant(Array[Byte](9)),
      6.toByte -> proofConstant(Array.empty[Coll[Byte]]))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      otherInputContextVars = Some(unrelatedVars)) shouldBe true
  }

  property("rsBTC vault cannot substitute an independent txid commitment for inclusion") {
    val fixture = vaultFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0)(1) = (proof(0)(1) ^ 1).toByte
    val wrongProofVars = fixture.contextVars
      .updated(4.toByte, proofConstant(proof.map(_.toColl)))
      .updated(7.toByte, ByteArrayConstant(doubleSha256(fixture.txBytes)))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      wrongProofVars) shouldBe false

    val independentTxidMutant = compileVaultMutant(
      "properProof &&",
      "txId == getVar[Coll[Byte]](7).get &&")
    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      wrongProofVars, independentTxidMutant) shouldBe true
  }

  property("rsBTC vault requires both inclusion and payment verdicts without boolean bypass") {
    val fixture = vaultFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0)(1) = (proof(0)(1) ^ 1).toByte
    val wrongProofVars = fixture.contextVars.updated(4.toByte, proofConstant(proof.map(_.toColl)))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      wrongProofVars) shouldBe false

    val booleanBypassMutant = compileVaultMutant(
      "properProof &&",
      "(properProof || anyOutputMatches) &&")
    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount,
      wrongProofVars, booleanBypassMutant) shouldBe true
  }

  property("rsBTC vault uses one output descriptor for amount and script") {
    val highValueScript = Array[Byte](1, 2, 3, 4)
    val targetScript = Array[Byte](5, 6, 7, 8)
    val txBytes = syntheticTx(Seq(
      output1Amount -> highValueScript,
      output2Amount -> targetScript))
    val fixture = twoTransactionVaultFixture(txBytes, targetScript)

    vaultProves(fixture, Sha256.hash(targetScript), output1Amount) shouldBe false

    val divergentWalkMutant = compileVaultMutant(
      "val amount = readAmount(start)",
      "val amount = readAmount(47)")
    vaultProves(fixture, Sha256.hash(targetScript), output1Amount,
      fixture.contextVars, divergentWalkMutant) shouldBe true
  }

  property("rsBTC vault rejects authenticated trailing bytes outside the canonical walk") {
    val txBytes = valid64ByteTx() :+ 0.toByte
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script)

    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe false

    val extentMutant = compileVaultMutant(
      "val locktimeOk = outputsEnd == txBytes.size - 4",
      "val locktimeOk = true")
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L,
      fixture.contextVars, extentMutant) shouldBe true
  }

  property("rsBTC vault accepts a valid 64-byte payment at authenticated Merkle depth") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script)

    txBytes.length shouldBe 64
    fixture.merkleProof.length shouldBe fixture.coinbaseProof.length
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe true
  }

  property("rsBTC vault accepts the maximum authenticated Merkle depth") {
    val txBytes = valid64ByteTx()
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script, proofDepth = 32)

    fixture.merkleProof.length shouldBe 32
    fixture.coinbaseProof.length shouldBe 32
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1000L) shouldBe true
  }

  property("rsBTC vault accepts an output exactly at the Bitcoin supply bound") {
    val txBytes = valid64ByteTx(maxBtcSatoshis)
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script)

    vaultProves(fixture, Sha256.hash(script), minSatoshis = maxBtcSatoshis) shouldBe true
  }

  property("rsBTC vault rejects a minimum above the Bitcoin supply") {
    val txBytes = valid64ByteTx(maxBtcSatoshis)
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script)

    vaultProves(fixture, Sha256.hash(script),
      minSatoshis = maxBtcSatoshis + 1L) shouldBe false
  }

  property("rsBTC vault enforces the Bitcoin supply bound on parsed output amounts") {
    val txBytes = valid64ByteTx(maxBtcSatoshis + 1L)
    val script = txBytes.slice(56, 60)
    val fixture = twoTransactionVaultFixture(txBytes, script)

    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1L) shouldBe false

    val supplyBoundMutant = compileVaultMutant(
      "val amountOk = amount <= maxBtcSatoshis && amount >= minSatoshis",
      "val amountOk = amount >= minSatoshis")
    vaultProves(fixture, Sha256.hash(script), minSatoshis = 1L,
      fixture.contextVars, supplyBoundMutant) shouldBe true
  }

  private def compileV6(script: String): ErgoTree =
    VersionContext.withVersions(V6SoftForkVersion, V6SoftForkVersion) {
      ErgoTree.fromProposition(ErgoTree.headerWithVersion(ZeroHeader, V6SoftForkVersion),
        compile(Map.empty, script).asBoolValue.toSigmaProp)
    }

  private def vaultProves(
      fixture: VaultFixture,
      scriptHash: Array[Byte],
      minSatoshis: Long,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty,
      tree: ErgoTree = vaultTree,
      otherInputContextVars: Option[Map[Byte, EvaluatedValue[_ <: SType]]] = None,
      includeRelayDataInput: Boolean = true): Boolean = {
    val spendVars = if (contextVars.isEmpty) fixture.contextVars else contextVars
    val vaultInput = testBox(
      vaultBoxValue,
      tree,
      creationHeight = 0,
      additionalRegisters = Map(
        R4 -> ByteArrayConstant(scriptHash),
        R5 -> LongConstant(minSatoshis)),
      transactionId = ModifierId @@ Base16.encode(doubleSha256(scriptHash)),
      boxIndex = 0)
    val vaultTxInput = Input(vaultInput.id,
      ProverResult(Array.emptyByteArray, ContextExtension(spendVars)))
    val otherInput = otherInputContextVars.map { vars =>
      val box = testBox(
        vaultBoxValue,
        TrueTree,
        creationHeight = 0,
        transactionId = ModifierId @@ Base16.encode(doubleSha256(Array[Byte](9))),
        boxIndex = 1)
      box -> Input(box.id, ProverResult(Array.emptyByteArray, ContextExtension(vars)))
    }
    val txInputs = IndexedSeq(vaultTxInput) ++ otherInput.map(_._2)
    val boxesToSpend = IndexedSeq(vaultInput) ++ otherInput.map(_._1)
    val dataInputs = if (includeRelayDataInput) IndexedSeq(DataInput(fixture.relayDataInput.id)) else IndexedSeq.empty
    val dataBoxes = if (includeRelayDataInput) IndexedSeq(fixture.relayDataInput) else IndexedSeq.empty
    val tx = new ErgoLikeTransaction(
      txInputs,
      dataInputs,
      IndexedSeq(vaultInput.toCandidate))
    val ctx = ErgoLikeContextTesting(
      currentHeight = 0,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = dataBoxes,
      boxesToSpend = boxesToSpend,
      spendingTransaction = tx,
      selfIndex = 0,
      activatedVersion = V6SoftForkVersion)

    proveAndVerify(tree, ctx, spendVars)
  }

  private def compileVaultMutant(original: String, replacement: String): ErgoTree = {
    val firstIndex = vaultScript.indexOf(original)
    firstIndex should not be -1
    firstIndex shouldBe vaultScript.lastIndexOf(original)
    compileV6(vaultScript.replace(original, replacement))
  }

  private def proveAndVerify(
      tree: ErgoTree,
      ctx: ErgoLikeContext,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]]): Boolean = {
    val prover = contextVars.foldLeft(new ContextEnrichingTestProvingInterpreter()) {
      case (p, (id, value)) => p.withContextExtender(id, value)
    }
    val verifier = new ErgoLikeTestInterpreter
    prover.prove(tree, ctx, fakeMessage).toOption.exists { pr =>
      verifier.verify(tree, ctx.withExtension(pr.extension), pr, fakeMessage).get._1
    }
  }

  private case class VaultFixture(
      relayDataInput: ErgoBox,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]],
      merkleProof: Array[Coll[Byte]],
      coinbaseBytes: Array[Byte],
      coinbaseProof: Array[Coll[Byte]],
      txBytes: Array[Byte],
      output1Script: Array[Byte],
      output2Script: Array[Byte],
      missingHeaderId: Array[Byte],
      missingHeaderProof: Array[Byte],
      displayOrderHeaderId: Array[Byte],
      displayOrderHeaderProof: Array[Byte],
      missingRelayNftDataInput: ErgoBox,
      wrongRelayNftDataInput: ErgoBox,
      wrongRelayNftQuantityDataInput: ErgoBox,
      extraRelayTokenDataInput: ErgoBox)

  private def vaultFixture(tipHeight: Int = bitcoinHeaderHeight + 6): VaultFixture = {
    val header = fromHex("01000000076379e2c0ec4a614ad1bf0ec716e6873f2c7abac604a08cc78e070000000000579a6bbcd07e9c3d622672ad20495d4485b5233395ab4081db7cab0fd2b577d2396cec4c2a8b091b031a7313")
    val expectedHeaderId = fromHex("4bc5e00fefc3727a3f217a37a2c368ddf80fe08e233f3b53e6b8030000000000")
    val txBytes = fromHex("0100000001eba8353ac2e5503f15548975108013246457ed83d331db760f0595b8bd7c54cb000000008c4930460221008c64f29882d9a59cbb070d75b4cdca56c04b523b0af37a0ffecee24e31cb2814022100b183ab317ad217f4a6f4e610c6138e5c2d7681d40f46201f268a5a90c1c07afa0141040b362c040204c13f6e1ec78b60978bdd76d851d4a1612cd9e82ead5177694f8f37fa4e8c78579876bbaf8a561772f320d3125f36cd1f1c5e9eb3f8bc08b626d2ffffffff0280e9fd97000000001976a914f0630fd41ff0722cf29de4db609f06a4c17fad2d88ac002a7515000000001976a9141dea9e37227b8d7a6296849fc76e00e8f5a6674e88ac00000000")
    val output1Script = fromHex("76a914f0630fd41ff0722cf29de4db609f06a4c17fad2d88ac")
    val output2Script = fromHex("76a9141dea9e37227b8d7a6296849fc76e00e8f5a6674e88ac")

    val tx1 = fromHex("a7c2b4a2cc940f9f541905048fe8352bd158dab18d15221fab7ee2187bd3cb5e")
    val tx2 = fromHex("1d74396699ae0effcd67fd5d031b780ff56c336bfc5d2d015d21db687d732764")
    val tx3Id = fromHex("d8c9d6a13a7fb8236833b1e93d298f4626deeb78b2f1814aa9a779961c08ce39")
    val merkleProof = Array(
      (1.toByte +: tx3Id.reverse).toColl,
      (0.toByte +: doubleSha256(tx1.reverse ++ tx2.reverse)).toColl)
    val coinbaseBytes = mainnetCoinbaseBytes()
    val coinbaseProof = Array(
      (1.toByte +: tx2.reverse).toColl,
      (1.toByte +: doubleSha256(tx3Id.reverse ++ tx3Id.reverse)).toColl)

    doubleSha256(coinbaseBytes).sameElements(tx1.reverse) shouldBe true
    doubleSha256(header).sameElements(expectedHeaderId) shouldBe true
    buildVaultFixture(header, txBytes, merkleProof, coinbaseBytes, coinbaseProof,
      output1Script, output2Script, tipHeight)
  }

  private def twoTransactionVaultFixture(
      txBytes: Array[Byte],
      outputScript: Array[Byte],
      tipHeight: Int = bitcoinHeaderHeight + 6,
      proofDepth: Int = 1,
      coinbaseBytes: Array[Byte] = mainnetCoinbaseBytes()): VaultFixture = {
    require(proofDepth >= 1)
    val paymentId = doubleSha256(txBytes)
    val coinbaseId = doubleSha256(coinbaseBytes)
    var merkleProof = Array((0.toByte +: coinbaseId).toColl)
    var coinbaseProof = Array((1.toByte +: paymentId).toColl)
    var currentRoot = doubleSha256(coinbaseId ++ paymentId)
    var level = 1
    while (level < proofDepth) {
      val duplicateLevel = (1.toByte +: currentRoot).toColl
      merkleProof = merkleProof :+ duplicateLevel
      coinbaseProof = coinbaseProof :+ duplicateLevel
      currentRoot = doubleSha256(currentRoot ++ currentRoot)
      level += 1
    }
    val merkleRoot = merkleRootFromProof(txBytes, merkleProof)
    require(merkleRoot.sameElements(currentRoot))
    require(merkleRoot.sameElements(merkleRootFromProof(coinbaseBytes, coinbaseProof)))
    val header = fromHex("01000000076379e2c0ec4a614ad1bf0ec716e6873f2c7abac604a08cc78e070000000000579a6bbcd07e9c3d622672ad20495d4485b5233395ab4081db7cab0fd2b577d2396cec4c2a8b091b031a7313")
    Array.copy(merkleRoot, 0, header, 36, 32)

    buildVaultFixture(header, txBytes, merkleProof, coinbaseBytes, coinbaseProof,
      outputScript, Array.emptyByteArray, tipHeight)
  }

  private def buildVaultFixture(
      header: Array[Byte],
      txBytes: Array[Byte],
      merkleProof: Array[Coll[Byte]],
      coinbaseBytes: Array[Byte],
      coinbaseProof: Array[Coll[Byte]],
      output1Script: Array[Byte],
      output2Script: Array[Byte],
      tipHeight: Int): VaultFixture = {
    val txId = doubleSha256(txBytes)
    val headerId = doubleSha256(header)
    val displayOrderHeaderId = headerId.reverse
    require(header.slice(36, 68).sameElements(merkleRootFromProof(txBytes, merkleProof)))
    require(header.slice(36, 68).sameElements(merkleRootFromProof(coinbaseBytes, coinbaseProof)))
    val headerAndHeight = header ++ longToBytes(bitcoinHeaderHeight.toLong)
    val bestChain = MutableAvl(Seq(headerId -> headerAndHeight), AvlTreeFlags.InsertOnly)
    val headerProof = bestChain.lookupProof(headerId)
    val missingHeaderId = Array.fill(32)(1.toByte)
    val missingHeaderProof = bestChain.lookupProof(missingHeaderId)
    val displayOrderHeaderProof = bestChain.lookupProof(displayOrderHeaderId)
    val relayDataInput = relayBox(bestChain.tree, tipHeight, headerId,
      transactionId = ModifierId @@ Base16.encode(txId))
    val missingRelayNftDataInput = relayBox(bestChain.tree, tipHeight, headerId,
      transactionId = ModifierId @@ Base16.encode(txId),
      relayTokens = ArraySeq.empty[Token])
    val wrongRelayNftDataInput = relayBox(bestChain.tree, tipHeight, headerId,
      transactionId = ModifierId @@ Base16.encode(txId),
      relayTokens = ArraySeq((Digest32Coll @@ Array.fill(32)(1.toByte).toColl, 1L): Token))
    val wrongRelayNftQuantityDataInput = relayBox(bestChain.tree, tipHeight, headerId,
      transactionId = ModifierId @@ Base16.encode(txId),
      relayTokens = ArraySeq((relayToken, 2L): Token))
    val extraRelayTokenDataInput = relayBox(bestChain.tree, tipHeight, headerId,
      transactionId = ModifierId @@ Base16.encode(txId),
      relayTokens = ArraySeq(
        (relayToken, 1L): Token,
        (Digest32Coll @@ Array.fill(32)(2.toByte).toColl, 1L): Token))
    val contextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map(
      1.toByte -> ByteArrayConstant(txBytes),
      2.toByte -> ByteArrayConstant(headerId),
      3.toByte -> ByteArrayConstant(headerProof),
      4.toByte -> proofConstant(merkleProof),
      5.toByte -> ByteArrayConstant(coinbaseBytes),
      6.toByte -> proofConstant(coinbaseProof))

    VaultFixture(relayDataInput, contextVars, merkleProof, coinbaseBytes, coinbaseProof,
      txBytes, output1Script, output2Script, missingHeaderId, missingHeaderProof,
      displayOrderHeaderId, displayOrderHeaderProof,
      missingRelayNftDataInput, wrongRelayNftDataInput, wrongRelayNftQuantityDataInput,
      extraRelayTokenDataInput)
  }

  private def relayBox(
      bestChain: CAvlTree,
      tipHeight: Int,
      tipId: Array[Byte],
      transactionId: ModifierId,
      relayTokens: ArraySeq[Token] = ArraySeq((relayToken, 1L): Token)): ErgoBox =
    testBox(
      relayBoxValue,
      TrueTree,
      creationHeight = 0,
      additionalTokens = relayTokens,
      additionalRegisters = Map(
        R4 -> AvlTreeConstant(bestChain),
        R5 -> AvlTreeConstant(bestChain),
        R6 -> IntConstant(tipHeight),
        R7 -> ByteArrayConstant(tipId),
        R8 -> BigIntConstant(BigInteger.ZERO)),
      transactionId = transactionId,
      boxIndex = 0)

  private case class MutableAvl(entries: Seq[(Array[Byte], Array[Byte])], flags: AvlTreeFlags) {
    private val prover = new BatchAVLProver[Digest32, Blake2b256.type](keyLength = 32, None)
    entries.foreach { case (key, value) =>
      require(prover.performOneOperation(Insert(ADKey @@ key, ADValue @@ value)).isSuccess)
    }
    prover.generateProof()

    def tree: CAvlTree = CAvlTree(new sigma.data.AvlTreeData(prover.digest.toColl, flags, 32, None))

    def lookupProof(key: Array[Byte]): Array[Byte] = {
      require(prover.performOneOperation(Lookup(ADKey @@ key)).isSuccess)
      prover.generateProof()
    }
  }

  private def longToBytes(value: Long): Array[Byte] =
    ByteBuffer.allocate(8).putLong(value).array()

  private def doubleSha256(bytes: Array[Byte]): Array[Byte] =
    Sha256.hash(Sha256.hash(bytes))

  private def merkleRootFromProof(txBytes: Array[Byte], proof: Array[Coll[Byte]]): Array[Byte] =
    proof.foldLeft(doubleSha256(txBytes)) { (prevHash, proofElemColl) =>
      val proofElem = proofElemColl.toArray
      require(proofElem.length >= 33)
      val elemHash = proofElem.slice(1, 33)
      if (proofElem(0) == 0) {
        doubleSha256(elemHash ++ prevHash)
      } else {
        doubleSha256(prevHash ++ elemHash)
      }
    }

  private def proofConstant(proof: Array[Coll[Byte]]): EvaluatedValue[_ <: SType] =
    CollectionConstant[SCollection[SByte.type]](proof.toColl, SCollection(SByte))

  private def mainnetCoinbaseBytes(): Array[Byte] =
    fromHex(
      "01000000010000000000000000000000000000000000000000000000000000000000000000" +
      "ffffffff08042a8b091b025e3cffffffff0100f2052a01000000434104d77816ded32ccc56fa" +
      "d6f455676c07908da96a37a7b9d2fd510cd4ddd92f3104f3d6e7134bd159fed3741522265" +
      "a901d44ec2ab428231c0e4986c52a22f13577ac00000000")

  private def fromHex(hex: String): Array[Byte] =
    Base16.decode(hex).get

  private def valid64ByteTx(amountSatoshis: Long = 1000L): Array[Byte] = {
    val tx = Array.fill(64)(0.toByte)
    tx(4) = 1.toByte
    tx(41) = 0.toByte
    tx(42) = 0xff.toByte
    tx(43) = 0xff.toByte
    tx(44) = 0xff.toByte
    tx(45) = 0xff.toByte
    tx(46) = 1.toByte
    val amount = ByteBuffer.allocate(8).order(java.nio.ByteOrder.LITTLE_ENDIAN).putLong(amountSatoshis).array()
    Array.copy(amount, 0, tx, 47, 8)
    tx(55) = 4.toByte
    tx(56) = 1.toByte
    tx(57) = 2.toByte
    tx(58) = 3.toByte
    tx(59) = 4.toByte
    tx
  }

  private def syntheticTx(outputs: Seq[(Long, Array[Byte])]): Array[Byte] = {
    def littleEndian32(value: Int): Array[Byte] =
      Array(value, value >> 8, value >> 16, value >> 24).map(_.toByte)
    def littleEndian64(value: Long): Array[Byte] =
      (0 until 8).map(i => (value >> (8 * i)).toByte).toArray

    val input = Array.fill(32)(0.toByte) ++ littleEndian32(0) ++
      Array(0.toByte) ++ littleEndian32(-1)
    val encodedOutputs = outputs.toArray.flatMap { case (amount, script) =>
      littleEndian64(amount) ++ Array(script.length.toByte) ++ script
    }
    littleEndian32(1) ++ Array(1.toByte) ++ input ++ Array(outputs.size.toByte) ++
      encodedOutputs ++ littleEndian32(0)
  }

  private val vaultScript: String =
    """{
      |  // context vars:
      |  // #1 - tx bytes
      |  // #2 - header id
      |  // #3 - headerProof
      |  // #4 - Merkle proof
      |  // #5 - stripped coinbase transaction bytes used as the authenticated depth witness
      |  // #6 - coinbase Merkle proof; every current hash is the left child because coinbase is leaf zero
      |
      |  // SELF registers:
      |  // R4 - expected one-time Bitcoin scriptPubKey hash
      |  // R5 - minimum output value in satoshis
      |
      |  val relayNftId = fromBase16("0000000000000000000000000000000000000000000000000000000000000000")
      |  // Six descendants after the containing header means seven confirmations including that header.
      |  val minDescendants = 6
      |  val maxMerkleDepth = 32
      |  val maxBtcSatoshis = 2100000000000000L
      |
      |  val relayDataInput = CONTEXT.dataInputs(0)
      |  val relayTokens = relayDataInput.tokens
      |  val relayToken = if (relayTokens.size == 1) relayTokens(0) else (relayNftId, 0L)
      |  // Relay authenticity is inductive: correctly initialized genesis plus BtcRelay's
      |  // proposition-and-token preservation keeps this singleton NFT under the relay script.
      |  val properRelay = relayTokens.size == 1 &&
      |                    relayToken._1 == relayNftId &&
      |                    relayToken._2 == 1L
      |
      |  val txBytes = getVar[Coll[Byte]](1).get
      |  def doubleSha256(bytes: Coll[Byte]) = sha256(sha256(bytes))
      |  val txId = doubleSha256(txBytes)
      |
      |  val headerId = getVar[Coll[Byte]](2).get
      |  val headerProof = getVar[Coll[Byte]](3).get
      |  val bestChain = relayDataInput.R4[AvlTree].get
      |  val headerAndHeight = bestChain.get(headerId, headerProof).get
      |  val height = byteArrayToLong(headerAndHeight.slice(80, 88))
      |  val tipHeight = relayDataInput.R6[Int].get
      |  val enoughConfs = (tipHeight - height) >= minDescendants
      |
      |  val merkleRootBytes = headerAndHeight.slice(36, 68)
      |  val merkleProof = getVar[Coll[Coll[Byte]]](4).get
      |  val coinbaseBytes = getVar[Coll[Byte]](5).get
      |  val coinbaseProof = getVar[Coll[Coll[Byte]]](6).get
      |
      |  def computeLevel(prevHash: Coll[Byte], proofElem: Coll[Byte]) = {
      |    val elemHash = proofElem.slice(1, 33)
      |    if (proofElem(0) == 0) {
      |      doubleSha256(elemHash ++ prevHash)
      |    } else {
      |      doubleSha256(prevHash ++ elemHash)
      |    }
      |  }
      |
      |  // The proof for a non-64-byte coinbase authenticates the actual tree depth. Equal depth
      |  // rejects shortened internal-node proofs without excluding a valid 64-byte payment.
      |  // A canonical 64-byte coinbase is deliberately rejected as the ambiguity boundary.
      |  val proofDepthOk = merkleProof.size <= maxMerkleDepth &&
      |                     merkleProof.size == coinbaseProof.size
      |  // Keep all linear proof scans and folds behind the constant-time depth envelope.
      |  val properProof = if (proofDepthOk) {
      |    val coinbaseShapeOk = if (coinbaseBytes.size >= 42) {
      |      coinbaseBytes.size != 64 &&
      |      coinbaseBytes(4) == 1 &&
      |      coinbaseBytes.slice(5, 37) == fromBase16("0000000000000000000000000000000000000000000000000000000000000000") &&
      |      coinbaseBytes.slice(37, 41) == fromBase16("ffffffff")
      |    } else {
      |      false
      |    }
      |    val proofShapeOk = merkleProof.forall({ (proofElem: Coll[Byte]) =>
      |      proofElem.size == 33 && (proofElem(0) == 0 || proofElem(0) == 1)
      |    })
      |    val coinbaseProofShapeOk = coinbaseProof.forall({ (proofElem: Coll[Byte]) =>
      |      proofElem.size == 33 && proofElem(0) == 1
      |    })
      |    val proofShapesOk = coinbaseShapeOk && proofShapeOk && coinbaseProofShapeOk
      |
      |    if (proofShapesOk) {
      |      val computedMerkleRoot = merkleProof.fold(txId, computeLevel)
      |      val computedCoinbaseRoot = coinbaseProof.fold(doubleSha256(coinbaseBytes), computeLevel)
      |      computedMerkleRoot == merkleRootBytes &&
      |      computedCoinbaseRoot == merkleRootBytes
      |    } else {
      |      false
      |    }
      |  } else {
      |    false
      |  }
      |
      |  val expectedScriptHash = SELF.R4[Coll[Byte]].get
      |  val minSatoshis = SELF.R5[Long].get
      |  val expectedScriptHashOk = expectedScriptHash.size == 32
      |  val minSatoshisOk = minSatoshis > 0L && minSatoshis <= maxBtcSatoshis
      |
      |  def readByte(pos: Int): Int = {
      |    val signed = txBytes(pos).toInt
      |    if (signed < 0) signed + 256 else signed
      |  }
      |
      |  def inputEnd(start: Int): Int = {
      |    val scriptLen = readByte(start + 36)
      |    start + 37 + scriptLen + 4
      |  }
      |
      |  def outputEnd(start: Int): Int = {
      |    val scriptLen = readByte(start + 8)
      |    start + 9 + scriptLen
      |  }
      |
      |  def amountFitsBitcoinSupply(start: Int): Boolean = {
      |    val b6 = readByte(start + 6)
      |    val b7 = readByte(start + 7)
      |    b7 == 0 && b6 <= 7
      |  }
      |
      |  def readAmount(start: Int): Long = {
      |    val b0 = readByte(start).toLong
      |    val b1 = readByte(start + 1).toLong
      |    val b2 = readByte(start + 2).toLong
      |    val b3 = readByte(start + 3).toLong
      |    val b4 = readByte(start + 4).toLong
      |    val b5 = readByte(start + 5).toLong
      |    val b6 = readByte(start + 6).toLong
      |    b0 +
      |      b1 * 256L +
      |      b2 * 65536L +
      |      b3 * 16777216L +
      |      b4 * 4294967296L +
      |      b5 * 1099511627776L +
      |      b6 * 281474976710656L
      |  }
      |
      |  def outputMatches(start: Int): Boolean = {
      |    val scriptLen = readByte(start + 8)
      |    if (scriptLen > 0 && amountFitsBitcoinSupply(start)) {
      |      val amount = readAmount(start)
      |      val amountOk = amount <= maxBtcSatoshis && amount >= minSatoshis
      |      val scriptStart = start + 9
      |      val scriptBytes = txBytes.slice(scriptStart, scriptStart + scriptLen)
      |      amountOk && sha256(scriptBytes) == expectedScriptHash
      |    } else {
      |      false
      |    }
      |  }
      |
      |  val sizeOk = txBytes.size >= 61
      |  val inputCount = readByte(4)
      |  val inputCountOk = inputCount == 1 || inputCount == 2
      |
      |  val input1ScriptLenOk = readByte(5 + 36) < 0xfd
      |  val afterInput1 = inputEnd(5)
      |
      |  val input2ScriptLenOk = if (inputCount == 2) {
      |    readByte(afterInput1 + 36) < 0xfd
      |  } else {
      |    true
      |  }
      |  val afterInput2 = if (inputCount == 2) inputEnd(afterInput1) else afterInput1
      |  val inputsEnd = afterInput2
      |
      |  val outputCount = readByte(inputsEnd)
      |  val outputCountOk = outputCount >= 1 && outputCount <= 4
      |
      |  val output1Start = inputsEnd + 1
      |  val output1ScriptLenOk = readByte(output1Start + 8) < 0xfd
      |  val match1 = outputMatches(output1Start)
      |  val afterOutput1 = outputEnd(output1Start)
      |
      |  val output2ScriptLenOk = if (outputCount >= 2) {
      |    readByte(afterOutput1 + 8) < 0xfd
      |  } else {
      |    true
      |  }
      |  val match2 = if (outputCount >= 2) outputMatches(afterOutput1) else false
      |  val afterOutput2 = if (outputCount >= 2) outputEnd(afterOutput1) else afterOutput1
      |
      |  val output3ScriptLenOk = if (outputCount >= 3) {
      |    readByte(afterOutput2 + 8) < 0xfd
      |  } else {
      |    true
      |  }
      |  val match3 = if (outputCount >= 3) outputMatches(afterOutput2) else false
      |  val afterOutput3 = if (outputCount >= 3) outputEnd(afterOutput2) else afterOutput2
      |
      |  val output4ScriptLenOk = if (outputCount == 4) {
      |    readByte(afterOutput3 + 8) < 0xfd
      |  } else {
      |    true
      |  }
      |  val match4 = if (outputCount == 4) outputMatches(afterOutput3) else false
      |  val afterOutput4 = if (outputCount == 4) outputEnd(afterOutput3) else afterOutput3
      |  val outputsEnd = afterOutput4
      |
      |  val locktimeOk = outputsEnd == txBytes.size - 4
      |  val anyOutputMatches = match1 || match2 || match3 || match4
      |  val allVarintsOk = input1ScriptLenOk && input2ScriptLenOk &&
      |                     output1ScriptLenOk && output2ScriptLenOk &&
      |                     output3ScriptLenOk && output4ScriptLenOk
      |
      |  sigmaProp(
      |    properRelay &&
      |    enoughConfs &&
      |    properProof &&
      |    expectedScriptHashOk &&
      |    sizeOk &&
      |    minSatoshisOk &&
      |    inputCountOk &&
      |    outputCountOk &&
      |    allVarintsOk &&
      |    locktimeOk &&
      |    anyOutputMatches
      |  )
      |}""".stripMargin
}
