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
  * 1 and authenticated by Merkle inclusion under a relay-verified header.
  *
  * Deal-creation invariant: R4 must be a fresh one-time Bitcoin scriptPubKey hash
  * for this vault/deal. No two live vaults should share the same expected script
  * hash. This uniqueness rule is not globally contract-enforced; an OP_RETURN deal
  * commitment is the natural stronger follow-up.
  *
  * SELF registers:
  *   R4: expected SHA-256 hash of a one-time Bitcoin scriptPubKey (Coll[Byte])
  *   R5: minimum output value in satoshis (Long)
  *
  * Context extension:
  *   var(1): Bitcoin transaction bytes
  *   var(2): Bitcoin header id
  *   var(3): relay AVL lookup proof for the header
  *   var(4): Bitcoin Merkle proof, with direction byte + sibling hash per level
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

  property("rsBTC vault rejects insufficient relay confirmations") {
    val fixture = vaultFixture(tipHeight = bitcoinHeaderHeight + 5)

    vaultProves(fixture, scriptHash = Sha256.hash(fixture.output1Script), minSatoshis = output1Amount) shouldBe false
  }

  property("rsBTC vault rejects transaction bytes not matching Merkle inclusion") {
    val fixture = vaultFixture()
    val txBytes = fixture.txBytes.clone()
    txBytes(0) = (txBytes(0) ^ 1).toByte
    val contextVars = fixture.contextVars.updated(1.toByte, ByteArrayConstant(txBytes))

    vaultProves(fixture, Sha256.hash(fixture.output1Script), output1Amount, contextVars) shouldBe false
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
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map.empty): Boolean = {
    val spendVars = if (contextVars.isEmpty) fixture.contextVars else contextVars
    val vaultInput = testBox(
      vaultBoxValue,
      vaultTree,
      creationHeight = 0,
      additionalRegisters = Map(
        R4 -> ByteArrayConstant(scriptHash),
        R5 -> LongConstant(minSatoshis)),
      transactionId = ModifierId @@ Base16.encode(doubleSha256(scriptHash)),
      boxIndex = 0)
    val tx = new ErgoLikeTransaction(
      IndexedSeq(Input(vaultInput.id, ProverResult(Array.emptyByteArray, ContextExtension(spendVars)))),
      IndexedSeq(DataInput(fixture.relayDataInput.id)),
      IndexedSeq(vaultInput.toCandidate))
    val ctx = ErgoLikeContextTesting(
      currentHeight = 0,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = IndexedSeq(fixture.relayDataInput),
      boxesToSpend = IndexedSeq(vaultInput),
      spendingTransaction = tx,
      selfIndex = 0,
      activatedVersion = V6SoftForkVersion)

    proveAndVerify(vaultTree, ctx, spendVars)
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
      txBytes: Array[Byte],
      output1Script: Array[Byte],
      output2Script: Array[Byte])

  private def vaultFixture(tipHeight: Int = bitcoinHeaderHeight + 6): VaultFixture = {
    val header = fromHex("01000000076379e2c0ec4a614ad1bf0ec716e6873f2c7abac604a08cc78e070000000000579a6bbcd07e9c3d622672ad20495d4485b5233395ab4081db7cab0fd2b577d2396cec4c2a8b091b031a7313")
    val headerId = fromHex("000000000003b8e6533b3f238ee00ff8dd68c3a2377a213f7a72c3ef0fe0c54b")
    val headerAndHeight = header ++ longToBytes(bitcoinHeaderHeight.toLong)
    val bestChain = MutableAvl(Seq(headerId -> headerAndHeight), AvlTreeFlags.InsertOnly)
    val headerProof = bestChain.lookupProof(headerId)

    val txBytes = fromHex("0100000001eba8353ac2e5503f15548975108013246457ed83d331db760f0595b8bd7c54cb000000008c4930460221008c64f29882d9a59cbb070d75b4cdca56c04b523b0af37a0ffecee24e31cb2814022100b183ab317ad217f4a6f4e610c6138e5c2d7681d40f46201f268a5a90c1c07afa0141040b362c040204c13f6e1ec78b60978bdd76d851d4a1612cd9e82ead5177694f8f37fa4e8c78579876bbaf8a561772f320d3125f36cd1f1c5e9eb3f8bc08b626d2ffffffff0280e9fd97000000001976a914f0630fd41ff0722cf29de4db609f06a4c17fad2d88ac002a7515000000001976a9141dea9e37227b8d7a6296849fc76e00e8f5a6674e88ac00000000")
    val txId = doubleSha256(txBytes)
    val output1Script = fromHex("76a914f0630fd41ff0722cf29de4db609f06a4c17fad2d88ac")
    val output2Script = fromHex("76a9141dea9e37227b8d7a6296849fc76e00e8f5a6674e88ac")

    val tx1 = fromHex("a7c2b4a2cc940f9f541905048fe8352bd158dab18d15221fab7ee2187bd3cb5e")
    val tx2 = fromHex("1d74396699ae0effcd67fd5d031b780ff56c336bfc5d2d015d21db687d732764")
    val tx3Id = fromHex("d8c9d6a13a7fb8236833b1e93d298f4626deeb78b2f1814aa9a779961c08ce39")
    val merkleProof = Array(
      (1.toByte +: tx3Id.reverse).toColl,
      (0.toByte +: doubleSha256(tx1.reverse ++ tx2.reverse)).toColl)

    val relayDataInput = relayBox(bestChain.tree, tipHeight, headerId,
      transactionId = ModifierId @@ Base16.encode(txId))
    val contextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map(
      1.toByte -> ByteArrayConstant(txBytes),
      2.toByte -> ByteArrayConstant(headerId),
      3.toByte -> ByteArrayConstant(headerProof),
      4.toByte -> CollectionConstant[SCollection[SByte.type]](merkleProof.toColl, SCollection(SByte)))

    VaultFixture(relayDataInput, contextVars, merkleProof, txBytes, output1Script, output2Script)
  }

  private def relayBox(
      bestChain: CAvlTree,
      tipHeight: Int,
      tipId: Array[Byte],
      transactionId: ModifierId): ErgoBox =
    testBox(
      relayBoxValue,
      TrueTree,
      creationHeight = 0,
      additionalTokens = ArraySeq((relayToken, 1L): Token),
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

  private def fromHex(hex: String): Array[Byte] =
    Base16.decode(hex).get

  private val vaultScript: String =
    """{
      |  // context vars:
      |  // #1 - tx bytes
      |  // #2 - header id
      |  // #3 - headerProof
      |  // #4 - Merkle proof
      |
      |  // SELF registers:
      |  // R4 - expected one-time Bitcoin scriptPubKey hash
      |  // R5 - minimum output value in satoshis
      |
      |  val relayNftId = fromBase16("0000000000000000000000000000000000000000000000000000000000000000")
      |  val minConfs = 6
      |  val maxBtcSatoshis = 2100000000000000L
      |
      |  val relayDataInput = CONTEXT.dataInputs(0)
      |  val properRelay = relayDataInput.tokens(0)._1 == relayNftId
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
      |  val enoughConfs = (tipHeight - height) >= minConfs
      |
      |  val merkleRootBytes = headerAndHeight.slice(36, 68)
      |  val merkleProof = getVar[Coll[Coll[Byte]]](4).get
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
      |  val computedMerkleRoot = merkleProof.fold(txId, computeLevel)
      |  val properProof = computedMerkleRoot == merkleRootBytes
      |
      |  val expectedScriptHash = SELF.R4[Coll[Byte]].get
      |  val minSatoshis = SELF.R5[Long].get
      |  val minSatoshisOk = minSatoshis >= 0L && minSatoshis <= maxBtcSatoshis
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
