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
import sigma.ast._
import sigma.ast.ErgoTree.ZeroHeader
import sigma.ast.syntax._
import sigma.data.{AvlTreeFlags, CAvlTree, Digest32Coll}
import sigma.Extensions.ArrayOps
import sigma.interpreter.{ContextExtension, ProverResult}
import sigma.util.NBitsUtils
import sigma.Coll
import sigmastate._
import sigmastate.helpers.TestingHelpers._
import sigmastate.helpers.{CompilerTestingCommons, ContextEnrichingTestProvingInterpreter, ErgoLikeContextTesting, ErgoLikeTestInterpreter}

import java.math.BigInteger
import java.nio.ByteBuffer
import scala.collection.compat.immutable.ArraySeq

class BitcoinRelayTxCheckSpecification extends CompilerTestingCommons with CompilerCrossVersionProps {

  private implicit lazy val IR: TestingIRContext = new TestingIRContext

  private val relayNftId = Array.fill(32)(0.toByte)
  private val relayToken = Digest32Coll @@ relayNftId.toColl
  private val relayBoxValue = 100000000L
  private val bitcoinHeaderHeight = 93500
  private val mainnetHeader566092Hex =
    "00000020a82ff9c62e69a6cbed277b7f2a9ac9da3c7133a59a6305000000000000000000f6cd5708a6ba38d8501502b5b4e5b93627e8dcc9bd13991894c6e04ade262aa99582815c505b2e17479a751b"
  private val mainnetHeader566093Hex =
    "00000020b45e33a345ad08ad2902cdd4101632fcbec009694b0c2500000000000000000016c99a795d8e0105d86f361341c7858d223fac261718bd608052822c5b4ae3cfd782815c505b2e17a56bb90b"
  private val mainnetHeader562464Hex =
    "00000020ae55d7640b738e1c16091cc73666526e7fa12af66c0419000000000000000000f7825fe0714275fe54521f66e898cf743ed43dd93f185cb628df995823e4ee2d7d58605c886f2e176d085a4c"
  private val mainnetHeader564479Hex =
    "00000020b4fe0ef78ee4d02206011ba597b45ef84ef1029ad8650300000000000000000034fdbe970f5d00d2e37de72755077c7039976baa5417ddfd358013d8ea9cb8d374c5725c886f2e1795d4ee3a"
  private val mainnetHeader564480Hex =
    "000000200cd536b3eb1cd9c028e081f1455006276b293467c3e5170000000000000000007bc1b27489db01c85d38a4bc6d2280611e9804f506d83ad00d2a33ebd663992f76c7725c505b2e174fb90f55"
  private val forkHeaderHex =
    "01000000076379e2c0ec4a614ad1bf0ec716e6873f2c7abac604a08cc78e070000000000579a6bbcd07e9c3d622672ad20495d4485b5233395ab4081db7cab0fd2b577d2396cec4c2a8b091b031a7313"
  private val expectedHeader566093Target = BigInt("4440088742263677654396177039706714734771352055402463232")
  private val expectedHeader566093Work = BigInt("26078778141331078011537")
  private val bitcoinPowLimit = BigInt("26959535291011309493156476344723991336010898738574164086137773096960")
  private val targetTimespanSeconds = 1209600L

  private lazy val btcRelayTree = compileV6(btcRelayScript)
  private lazy val btcTxCheckTree = compileV6(btcTxCheckScript)

  property("BtcRelay compiles") {
    btcRelayTree.version shouldBe V6SoftForkVersion
  }

  property("BtcTxCheck compiles") {
    btcTxCheckTree.version shouldBe V6SoftForkVersion
  }

  property("BtcRelay accepts a header added to best chain") {
    val fixture = bestChainAppendFixture()

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe true
  }

  property("BtcRelay accepts a header added to non-best chain with switch") {
    val fixture = forkAppendFixture(bestChainWorkWins = true)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe true
  }

  property("BtcRelay accepts a header added to non-best chain without switch") {
    val fixture = forkAppendFixture(bestChainWorkWins = false)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe true
  }

  property("BtcRelay accepts a retarget-boundary header with anchor proof") {
    val fixture = retargetAppendFixture()

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe true
  }

  property("BtcRelay rejects header hash above compact target") {
    val invalidHeader = invalidPowHeaderBytes()
    relayPowHitIsBelowTarget(invalidHeader) shouldBe false
    val fixture = bestChainAppendFixture(newHeaderBytes = invalidHeader)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects compact target above Bitcoin pow limit") {
    val invalidHeader = headerWithNBits(fromHex(mainnetHeader566093Hex), 0x1d010000L)
    targetFromHeader(invalidHeader) > bitcoinPowLimit shouldBe true
    val fixture = bestChainAppendFixture(newHeaderBytes = invalidHeader)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects non-positive compact target") {
    val invalidHeader = headerWithNBits(fromHex(mainnetHeader566093Hex), 0x01003456L)
    targetFromHeader(invalidHeader) shouldBe BigInt(0)
    val fixture = bestChainAppendFixture(newHeaderBytes = invalidHeader, declaredBlockWork = Some(BigInteger.ONE))

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects nBits change before retarget boundary") {
    val invalidHeader = headerWithNBits(fromHex(mainnetHeader566093Hex), 0x1d00ffffL)
    val fixture = bestChainAppendFixture(newHeaderBytes = invalidHeader)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects retarget-boundary header with wrong anchor height") {
    val fixture = retargetAppendFixture(anchorHeight = 562465)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects retarget-boundary header with wrong anchor proof") {
    val fixture = retargetAppendFixture()

    relayProves(fixture.input, fixture.output,
      fixture.contextVars.updated(9.toByte, ByteArrayConstant(Array.fill(32)(1.toByte)))) shouldBe false
  }

  property("BtcRelay rejects malformed header length") {
    val invalidHeader = fromHex(mainnetHeader566093Hex) :+ 0.toByte
    val fixture = bestChainAppendFixture(newHeaderBytes = invalidHeader)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects wrong cumulative work bytes") {
    val fixture = bestChainAppendFixture()

    relayProves(fixture.input, fixture.output,
      fixture.contextVars.updated(7.toByte, ByteArrayConstant(BigInteger.ONE.toByteArray))) shouldBe false
  }

  property("BtcRelay rejects switching to a lower-work branch") {
    val fixture = forkAppendFixture(bestChainWorkWins = false, forceSwitchOutput = true)

    relayProves(fixture.input, fixture.output, fixture.contextVars) shouldBe false
  }

  property("BtcRelay rejects wrong parent header proof") {
    val fixture = bestChainAppendFixture()
    val wrongProof = Array.fill(32)(1.toByte)

    relayProves(fixture.input, fixture.output, fixture.contextVars.updated(3.toByte, ByteArrayConstant(wrongProof))) shouldBe false
  }

  property("BtcTxCheck validates an odd-count Bitcoin tx Merkle proof under relay header") {
    val fixture = txCheckFixture()

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars) shouldBe true
  }

  property("BtcTxCheck rejects wrong Merkle proof") {
    val fixture = txCheckFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0)(1) = (proof(0)(1) ^ 1).toByte
    val wrongProof = CollectionConstant[SCollection[SByte.type]](proof.map(_.toColl).toColl, SCollection(SByte))

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars.updated(4.toByte, wrongProof)) shouldBe false
  }

  property("BtcTxCheck rejects Merkle proof with invalid direction flag") {
    val fixture = txCheckFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0)(0) = 2.toByte
    val wrongProof = CollectionConstant[SCollection[SByte.type]](proof.map(_.toColl).toColl, SCollection(SByte))

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars.updated(4.toByte, wrongProof)) shouldBe false
  }

  property("BtcTxCheck rejects Merkle proof level with extra bytes") {
    val fixture = txCheckFixture()
    val proof = fixture.merkleProof.map(_.toArray)
    proof(0) = proof(0) :+ 0.toByte
    val wrongProof = CollectionConstant[SCollection[SByte.type]](proof.map(_.toColl).toColl, SCollection(SByte))

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars.updated(4.toByte, wrongProof)) shouldBe false
  }

  property("BtcTxCheck rejects insufficient confirmations") {
    val fixture = txCheckFixture(tipHeight = bitcoinHeaderHeight + 5)

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars) shouldBe false
  }

  property("BtcTxCheck rejects wrong transaction bytes") {
    val fixture = txCheckFixture()
    val txBytes = fixture.txBytes.clone()
    txBytes(0) = (txBytes(0) ^ 1).toByte

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars.updated(1.toByte, ByteArrayConstant(txBytes))) shouldBe false
  }

  property("BtcTxCheck rejects wrong header id") {
    val fixture = txCheckFixture()
    val headerId = fixture.headerId.clone()
    headerId(0) = (headerId(0) ^ 1).toByte

    txCheckProves(fixture.input, fixture.relayDataInput, fixture.contextVars.updated(2.toByte, ByteArrayConstant(headerId))) shouldBe false
  }

  property("relay work calculation is pinned for the mainnet header fixture") {
    val header = fromHex(mainnetHeader566093Hex)

    targetFromHeader(header) shouldBe expectedHeader566093Target
    blockWorkFromHeader(header) shouldBe expectedHeader566093Work
  }

  property("relay retarget calculation is pinned for the mainnet boundary fixture") {
    val anchor = fromHex(mainnetHeader562464Hex)
    val parent = fromHex(mainnetHeader564479Hex)
    val next = fromHex(mainnetHeader564480Hex)

    nBitsFromHeader(anchor) shouldBe 0x172e6f88L
    nBitsFromHeader(parent) shouldBe 0x172e6f88L
    nBitsFromHeader(next) shouldBe 0x172e5b50L
    timestampFromHeader(parent) - timestampFromHeader(anchor) shouldBe 1207543L
    expectedRetargetNBits(parent, anchor) shouldBe nBitsFromHeader(next)
  }

  private def compileV6(script: String): ErgoTree =
    VersionContext.withVersions(V6SoftForkVersion, V6SoftForkVersion) {
      ErgoTree.fromProposition(ErgoTree.headerWithVersion(ZeroHeader, V6SoftForkVersion),
        compile(Map.empty, script).asBoolValue.toSigmaProp)
    }

  private def relayProves(
      relayInput: ErgoBox,
      relayOutput: ErgoBoxCandidate,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]]): Boolean = {
    val contextExtension = ContextExtension(contextVars)
    val tx = new ErgoLikeTransaction(
      IndexedSeq(Input(relayInput.id, ProverResult(Array.emptyByteArray, contextExtension))),
      IndexedSeq.empty,
      IndexedSeq(relayOutput))
    val ctx = ErgoLikeContextTesting(
      currentHeight = 0,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      boxesToSpend = IndexedSeq(relayInput),
      tx,
      self = relayInput,
      activatedVersion = V6SoftForkVersion)

    proveAndVerify(btcRelayTree, ctx, contextVars)
  }

  private def txCheckProves(
      txCheckInput: ErgoBox,
      relayDataInput: ErgoBox,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]]): Boolean = {
    val contextExtension = ContextExtension(contextVars)
    val tx = new ErgoLikeTransaction(
      IndexedSeq(Input(txCheckInput.id, ProverResult(Array.emptyByteArray, contextExtension))),
      IndexedSeq(DataInput(relayDataInput.id)),
      IndexedSeq(txCheckInput.toCandidate))
    val ctx = ErgoLikeContextTesting(
      currentHeight = 0,
      lastBlockUtxoRoot = sigma.data.AvlTreeData.dummy,
      minerPubkey = ErgoLikeContextTesting.dummyPubkey,
      dataBoxes = IndexedSeq(relayDataInput),
      boxesToSpend = IndexedSeq(txCheckInput),
      spendingTransaction = tx,
      selfIndex = 0,
      activatedVersion = V6SoftForkVersion)

    proveAndVerify(btcTxCheckTree, ctx, contextVars)
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

  private case class RelayFixture(
      input: ErgoBox,
      output: ErgoBoxCandidate,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]])

  private case class TxCheckFixture(
      input: ErgoBox,
      relayDataInput: ErgoBox,
      contextVars: Map[Byte, EvaluatedValue[_ <: SType]],
      merkleProof: Array[Coll[Byte]],
      txBytes: Array[Byte],
      headerId: Array[Byte])

  private def bestChainAppendFixture(
      newHeaderBytes: Array[Byte] = fromHex(mainnetHeader566093Hex),
      declaredBlockWork: Option[BigInteger] = None): RelayFixture = {
    val h1 = HeaderFixture(
      hex = mainnetHeader566092Hex,
      height = 566092,
      cumulativeWork = new BigInteger("100500500500"))
    val h2Work = declaredBlockWork.getOrElse(blockWorkFromHeader(newHeaderBytes).bigInteger)
    val h2 = HeaderFixture(
      bytes = newHeaderBytes,
      height = h1.height + 1,
      cumulativeWork = h1.cumulativeWork.add(h2Work))

    val bestChain = MutableAvl(Seq(h1.id -> h1.headerAndHeight), AvlTreeFlags.InsertOnly)
    val allHeaders = MutableAvl(Seq(h1.id -> allHeadersRecord(h1, bestChain.tree.digest.toArray, h1.cumulativeWork)), AvlTreeFlags.InsertOnly)
    val parentLookupProof = allHeaders.lookupProof(h1.id)

    val input = relayBox(bestChain.tree, allHeaders.tree, h1.height, h1.id, h1.cumulativeWork)
    val bestChainBefore = bestChain.tree
    val bestInsertProof = bestChain.insertProof(h2.id, h2.headerAndHeight)
    val bestChainAfter = bestChain.tree
    val allHeadersInsertProof = allHeaders.insertProof(h2.id, allHeadersRecord(h2, bestChainAfter.digest.toArray, h2.cumulativeWork))
    val output = relayCandidate(bestChainAfter, allHeaders.tree, h2.height, h2.id, h2.cumulativeWork)

    RelayFixture(input, output, relayContextVars(h2.bytes, bestInsertProof, parentLookupProof, bestChainBefore, bestInsertProof,
      allHeadersInsertProof, h2.cumulativeWork))
  }

  private def forkAppendFixture(bestChainWorkWins: Boolean, forceSwitchOutput: Boolean = false): RelayFixture = {
    val h0 = HeaderFixture(
      hex = forkHeaderHex,
      height = 566092,
      cumulativeWork = if (bestChainWorkWins) new BigInteger("100500500500") else new BigInteger("100500500500000000000000"))
    val h1 = HeaderFixture(
      hex = mainnetHeader566092Hex,
      height = 566092,
      cumulativeWork = new BigInteger("100500500600"))
    val h2Bytes = fromHex(mainnetHeader566093Hex)
    val h2 = HeaderFixture(h2Bytes, h1.height + 1, h1.cumulativeWork.add(blockWorkFromHeader(h2Bytes).bigInteger))

    val h0BestChain = MutableAvl(Seq(h0.id -> h0.headerAndHeight), AvlTreeFlags.InsertOnly)
    val h1BestChain = MutableAvl(Seq(h1.id -> h1.headerAndHeight), AvlTreeFlags.InsertOnly)
    val allHeaders = MutableAvl(Seq(
      h1.id -> allHeadersRecord(h1, h1BestChain.tree.digest.toArray, h1.cumulativeWork),
      h0.id -> allHeadersRecord(h0, h0BestChain.tree.digest.toArray, h0.cumulativeWork)), AvlTreeFlags.InsertOnly)
    val parentLookupProof = allHeaders.lookupProof(h1.id)

    val input = relayBox(h0BestChain.tree, allHeaders.tree, h0.height, h0.id, h0.cumulativeWork)
    val h1BestChainBefore = h1BestChain.tree
    val h1BestInsertProof = h1BestChain.insertProof(h2.id, h2.headerAndHeight)
    val h1BestChainAfter = h1BestChain.tree
    val allHeadersInsertProof = allHeaders.insertProof(h2.id, allHeadersRecord(h2, h1BestChainAfter.digest.toArray, h2.cumulativeWork))

    val output =
      if (bestChainWorkWins || forceSwitchOutput) relayCandidate(h1BestChainAfter, allHeaders.tree, h2.height, h2.id, h2.cumulativeWork)
      else relayCandidate(h0BestChain.tree, allHeaders.tree, h0.height, h0.id, h0.cumulativeWork)

    RelayFixture(input, output, relayContextVars(h2.bytes, h1BestInsertProof, parentLookupProof, h1BestChainBefore,
      h1BestInsertProof, allHeadersInsertProof, h2.cumulativeWork))
  }

  private def retargetAppendFixture(anchorHeight: Int = 562464): RelayFixture = {
    val anchor = HeaderFixture(
      hex = mainnetHeader562464Hex,
      height = anchorHeight,
      cumulativeWork = BigInteger.ZERO)
    val parent = HeaderFixture(
      hex = mainnetHeader564479Hex,
      height = 564479,
      cumulativeWork = new BigInteger("100500500500"))
    val nextBytes = fromHex(mainnetHeader564480Hex)
    val next = HeaderFixture(
      bytes = nextBytes,
      height = parent.height + 1,
      cumulativeWork = parent.cumulativeWork.add(blockWorkFromHeader(nextBytes).bigInteger))

    val bestChain = MutableAvl(Seq(
      anchor.id -> anchor.headerAndHeight,
      parent.id -> parent.headerAndHeight), AvlTreeFlags.InsertOnly)
    val allHeaders = MutableAvl(Seq(parent.id -> allHeadersRecord(parent, bestChain.tree.digest.toArray, parent.cumulativeWork)),
      AvlTreeFlags.InsertOnly)
    val parentLookupProof = allHeaders.lookupProof(parent.id)

    val input = relayBox(bestChain.tree, allHeaders.tree, parent.height, parent.id, parent.cumulativeWork)
    val bestChainBefore = bestChain.tree
    val retargetAnchorProof = bestChain.lookupProof(anchor.id)
    val bestInsertProof = bestChain.insertProof(next.id, next.headerAndHeight)
    val bestChainAfter = bestChain.tree
    val allHeadersInsertProof = allHeaders.insertProof(next.id, allHeadersRecord(next, bestChainAfter.digest.toArray, next.cumulativeWork))
    val output = relayCandidate(bestChainAfter, allHeaders.tree, next.height, next.id, next.cumulativeWork)

    RelayFixture(input, output, relayContextVars(next.bytes, bestInsertProof, parentLookupProof, bestChainBefore, bestInsertProof,
      allHeadersInsertProof, next.cumulativeWork, retargetAnchorId = Some(anchor.id), retargetAnchorProof = Some(retargetAnchorProof)))
  }

  private def txCheckFixture(tipHeight: Int = bitcoinHeaderHeight + 6): TxCheckFixture = {
    val header = fromHex("01000000076379e2c0ec4a614ad1bf0ec716e6873f2c7abac604a08cc78e070000000000579a6bbcd07e9c3d622672ad20495d4485b5233395ab4081db7cab0fd2b577d2396cec4c2a8b091b031a7313")
    val headerId = fromHex("000000000003b8e6533b3f238ee00ff8dd68c3a2377a213f7a72c3ef0fe0c54b")
    val headerAndHeight = header ++ longToBytes(bitcoinHeaderHeight.toLong)
    val bestChain = MutableAvl(Seq(headerId -> headerAndHeight), AvlTreeFlags.InsertOnly)
    val headerProof = bestChain.lookupProof(headerId)

    val txBytes = fromHex("0100000001eba8353ac2e5503f15548975108013246457ed83d331db760f0595b8bd7c54cb000000008c4930460221008c64f29882d9a59cbb070d75b4cdca56c04b523b0af37a0ffecee24e31cb2814022100b183ab317ad217f4a6f4e610c6138e5c2d7681d40f46201f268a5a90c1c07afa0141040b362c040204c13f6e1ec78b60978bdd76d851d4a1612cd9e82ead5177694f8f37fa4e8c78579876bbaf8a561772f320d3125f36cd1f1c5e9eb3f8bc08b626d2ffffffff0280e9fd97000000001976a914f0630fd41ff0722cf29de4db609f06a4c17fad2d88ac002a7515000000001976a9141dea9e37227b8d7a6296849fc76e00e8f5a6674e88ac00000000")
    val txId = doubleSha256(txBytes)

    val tx1 = fromHex("a7c2b4a2cc940f9f541905048fe8352bd158dab18d15221fab7ee2187bd3cb5e")
    val tx2 = fromHex("1d74396699ae0effcd67fd5d031b780ff56c336bfc5d2d015d21db687d732764")
    val tx3Id = fromHex("d8c9d6a13a7fb8236833b1e93d298f4626deeb78b2f1814aa9a779961c08ce39")
    // This block has three transactions, so the first Merkle level pairs the
    // proven transaction with its own duplicate per Bitcoin's odd-count rule.
    // That edge case is covered here, without claiming full mutated-tree defense.
    val merkleProof = Array(
      (1.toByte +: tx3Id.reverse).toColl,
      (0.toByte +: doubleSha256(tx1.reverse ++ tx2.reverse)).toColl)

    val relayDataInput = relayBox(bestChain.tree, bestChain.tree, tipHeight, headerId, BigInteger.ZERO,
      transactionId = ModifierId @@ Base16.encode(txId))
    val txCheckInput = testBox(
      relayBoxValue,
      btcTxCheckTree,
      creationHeight = 0,
      transactionId = ModifierId @@ Base16.encode(txId.reverse),
      boxIndex = 0)

    val contextVars: Map[Byte, EvaluatedValue[_ <: SType]] = Map(
      1.toByte -> ByteArrayConstant(txBytes),
      2.toByte -> ByteArrayConstant(headerId),
      3.toByte -> ByteArrayConstant(headerProof),
      4.toByte -> CollectionConstant[SCollection[SByte.type]](merkleProof.toColl, SCollection(SByte)))

    TxCheckFixture(txCheckInput, relayDataInput, contextVars, merkleProof, txBytes, headerId)
  }

  private def relayContextVars(
      newHeader: Array[Byte],
      bestInsertProof: Array[Byte],
      parentLookupProof: Array[Byte],
      parentChain: CAvlTree,
      parentChainInsertProof: Array[Byte],
      allHeadersInsertProof: Array[Byte],
      cumulativeWork: BigInteger,
      retargetAnchorId: Option[Array[Byte]] = None,
      retargetAnchorProof: Option[Array[Byte]] = None): Map[Byte, EvaluatedValue[_ <: SType]] = {
    val base = Map(
      1.toByte -> ByteArrayConstant(newHeader),
      2.toByte -> ByteArrayConstant(bestInsertProof),
      3.toByte -> ByteArrayConstant(parentLookupProof),
      4.toByte -> AvlTreeConstant(parentChain),
      5.toByte -> ByteArrayConstant(parentChainInsertProof),
      6.toByte -> ByteArrayConstant(allHeadersInsertProof),
      7.toByte -> ByteArrayConstant(cumulativeWork.toByteArray))
    base ++ retargetAnchorId.map(8.toByte -> ByteArrayConstant(_)) ++
      retargetAnchorProof.map(9.toByte -> ByteArrayConstant(_))
  }

  private def relayBox(
      bestChain: CAvlTree,
      allHeaders: CAvlTree,
      tipHeight: Int,
      tipId: Array[Byte],
      tipWork: BigInteger,
      transactionId: ModifierId = ErgoBox.allZerosModifierId): ErgoBox =
    testBox(
      relayBoxValue,
      btcRelayTree,
      creationHeight = 0,
      additionalTokens = ArraySeq((relayToken, 1L): Token),
      additionalRegisters = Map(
        R4 -> AvlTreeConstant(bestChain),
        R5 -> AvlTreeConstant(allHeaders),
        R6 -> IntConstant(tipHeight),
        R7 -> ByteArrayConstant(tipId),
        R8 -> BigIntConstant(tipWork)),
      transactionId = transactionId,
      boxIndex = 0)

  private def relayCandidate(
      bestChain: CAvlTree,
      allHeaders: CAvlTree,
      tipHeight: Int,
      tipId: Array[Byte],
      tipWork: BigInteger): ErgoBoxCandidate =
    relayBox(bestChain, allHeaders, tipHeight, tipId, tipWork).toCandidate

  private def allHeadersRecord(header: HeaderFixture, chainDigest: Array[Byte], cumulativeWork: BigInteger): Array[Byte] =
    header.headerAndHeight ++ chainDigest ++ cumulativeWork.toByteArray

  private case class HeaderFixture(bytes: Array[Byte], height: Int, cumulativeWork: BigInteger) {
    val id: Array[Byte] = doubleSha256(bytes)
    val headerAndHeight: Array[Byte] = bytes ++ longToBytes(height.toLong)
  }

  private object HeaderFixture {
    def apply(hex: String, height: Int, cumulativeWork: BigInteger): HeaderFixture =
      HeaderFixture(fromHex(hex), height, cumulativeWork)
  }

  private case class MutableAvl(entries: Seq[(Array[Byte], Array[Byte])], flags: AvlTreeFlags) {
    private val prover = new BatchAVLProver[Digest32, Blake2b256.type](keyLength = 32, None)
    entries.foreach { case (key, value) =>
      require(prover.performOneOperation(Insert(ADKey @@ key, ADValue @@ value)).isSuccess)
    }
    prover.generateProof()

    def tree: CAvlTree = CAvlTree(new sigma.data.AvlTreeData(prover.digest.toColl, flags, 32, None))

    def insertProof(key: Array[Byte], value: Array[Byte]): Array[Byte] = {
      require(prover.performOneOperation(Insert(ADKey @@ key, ADValue @@ value)).isSuccess)
      prover.generateProof()
    }

    def lookupProof(key: Array[Byte]): Array[Byte] = {
      require(prover.performOneOperation(Lookup(ADKey @@ key)).isSuccess)
      prover.generateProof()
    }
  }

  private def blockWorkFromHeader(headerBytes: Array[Byte]): BigInt = {
    val target = targetFromHeader(headerBytes)
    val maxTarget = (BigInt(1) << 256) - 1

    (maxTarget / (target + 1)) + 1
  }

  private def targetFromHeader(headerBytes: Array[Byte]): BigInt = {
    NBitsUtils.decodeCompactBits(nBitsFromHeader(headerBytes))
  }

  private def nBitsFromHeader(headerBytes: Array[Byte]): Long =
    byteArrayToLong(Array.fill(4)(0.toByte) ++ headerBytes.slice(72, 76).reverse)

  private def timestampFromHeader(headerBytes: Array[Byte]): Long =
    byteArrayToLong(Array.fill(4)(0.toByte) ++ headerBytes.slice(68, 72).reverse)

  private def expectedRetargetNBits(parentHeader: Array[Byte], anchorHeader: Array[Byte]): Long = {
    val actualTimespan = timestampFromHeader(parentHeader) - timestampFromHeader(anchorHeader)
    val boundedTimespan = math.max(targetTimespanSeconds / 4, math.min(targetTimespanSeconds * 4, actualTimespan))
    val newTarget = (targetFromHeader(parentHeader) * boundedTimespan) / targetTimespanSeconds
    NBitsUtils.encodeCompactBits(newTarget.min(bitcoinPowLimit))
  }

  private def relayPowHitIsBelowTarget(headerBytes: Array[Byte]): Boolean = {
    val hitBytes = doubleSha256(headerBytes).reverse
    hitBytes.head >= 0 && BigInt(hitBytes) <= targetFromHeader(headerBytes)
  }

  private def invalidPowHeaderBytes(): Array[Byte] = {
    val bytes = fromHex(mainnetHeader566093Hex)
    bytes(79) = (bytes(79) ^ 1).toByte
    bytes
  }

  private def headerWithNBits(headerBytes: Array[Byte], nBits: Long): Array[Byte] = {
    val updated = headerBytes.clone()
    val nBitsBytes = ByteBuffer.allocate(4).putInt(nBits.toInt).array().reverse
    Array.copy(nBitsBytes, 0, updated, 72, 4)
    updated
  }

  private def byteArrayToLong(bytes: Array[Byte]): Long =
    ByteBuffer.wrap(bytes).getLong

  private def longToBytes(value: Long): Array[Byte] =
    ByteBuffer.allocate(8).putLong(value).array()

  private def doubleSha256(bytes: Array[Byte]): Array[Byte] =
    Sha256.hash(Sha256.hash(bytes))

  private def fromHex(hex: String): Array[Byte] =
    Base16.decode(hex).get

  private val btcRelayScript: String =
    """{
      |    // registers:
      |    // R4 - best headers-chain tree
      |    // R5 - all headers tree
      |    // R6 - tip height
      |    // R7 - tip block id
      |
      |    // R8 - tip cumulative work
      |    //
      |    // context vars:
      |    // #1 - new header bytes
      |    // #2 - best chain tree insert proof // if tip update
      |    // #3 - parent header lookup proof in all headers db
      |    // #4 - parent header's best chain digest
      |    // #5 - parent header's best chain insert proof
      |    // #6 - all headers insert proof
      |    // #7 - new header's cumulative work as byte array
      |    // #8 - retarget-period anchor header id, only when new height is divisible by 2016
      |    // #9 - retarget-period anchor lookup proof, only when new height is divisible by 2016
      |
      |    // id -> header (80 bytes) + height (8 bytes)
      |    val bestChainDigest = SELF.R4[AvlTree].get
      |
      |    // id -> header (80 bytes) + height (8 bytes) + chain digest (33 bytes) + cumulative work
      |    // chain digest here is constructed in the same way as best header chain digest
      |    val allHeadersDigest = SELF.R5[AvlTree].get
      |
      |    val tipHeight = SELF.R6[Int].get
      |    val tipHash = SELF.R7[Coll[Byte]].get
      |    val tipWork = SELF.R8[BigInt].get
      |
      |    val selfOut = OUTPUTS(0)
      |
      |    def reverse4(bytes: Coll[Byte]): Coll[Byte] = {
      |        Coll(bytes(3), bytes(2), bytes(1), bytes(0))
      |    }
      |
      |    def reverse32(bytes: Coll[Byte]): Coll[Byte] = {
      |        Coll(
      |          bytes(31), bytes(30), bytes(29), bytes(28),
      |          bytes(27), bytes(26), bytes(25), bytes(24),
      |          bytes(23), bytes(22), bytes(21), bytes(20),
      |          bytes(19), bytes(18), bytes(17), bytes(16),
      |          bytes(15), bytes(14), bytes(13), bytes(12),
      |          bytes(11), bytes(10), bytes(9), bytes(8),
      |          bytes(7), bytes(6), bytes(5), bytes(4),
      |          bytes(3), bytes(2), bytes(1), bytes(0)
      |        )
      |    }
      |
      |    def doubleSha256(bytes: Coll[Byte]) = sha256(sha256(bytes))
      |
      |    def headerId(headerBytes: Coll[Byte]) = doubleSha256(headerBytes)
      |
      |    val candidateHeaderBytes = getVar[Coll[Byte]](1).get
      |    val validHeaderSize = candidateHeaderBytes.size == 80
      |    val zero16 = Coll[Byte](
      |      0.toByte, 0.toByte, 0.toByte, 0.toByte,
      |      0.toByte, 0.toByte, 0.toByte, 0.toByte,
      |      0.toByte, 0.toByte, 0.toByte, 0.toByte,
      |      0.toByte, 0.toByte, 0.toByte, 0.toByte)
      |    val zero32 = zero16 ++ zero16
      |    val zero80 = zero32 ++ zero32 ++ zero16
      |    val headerBytes = (candidateHeaderBytes ++ zero80).slice(0, 80)
      |    val prevBlockId = headerBytes.slice(4, 36)
      |    // val merkleRootBytes = headerBytes.slice(36, 68)
      |    val nBitsBytes = reverse4(headerBytes.slice(72, 76))
      |
      |    // calculate target to validate PoW & calculate work
      |    val pad = Coll[Byte](0.toByte, 0.toByte, 0.toByte, 0.toByte)
      |    val nbits = byteArrayToLong(pad ++ nBitsBytes)
      |    val compactSizeOk = nBitsBytes(0) > 0.toByte && nBitsBytes(0) <= 32.toByte
      |    val compactSignOk = nBitsBytes(1) >= 0.toByte
      |    val target = if (compactSizeOk && compactSignOk) Global.decodeNbits(nbits) else bigInt("0")
      |    val bitcoinPowLimit = bigInt("26959535291011309493156476344723991336010898738574164086137773096960")
      |    val targetSanityOk = target > bigInt("0") && target <= bitcoinPowLimit
      |
      |    // block (header) id
      |    val id = headerId(headerBytes)
      |
      |    val validPow = targetSanityOk && {
      |        val hitBytes = reverse32(id)
      |        val hit = byteArrayToBigInt(hitBytes)
      |
      |        // <= according to https://bitcoin.stackexchange.com/a/105224
      |        hitBytes(0) >= 0.toByte && hit <= target
      |    }
      |
      |    val maxWorkNumerator = unsignedBigInt("115792089237316195423570985008687907853269984665640564039457584007913129639935")
      |    val maxSignedWork = unsignedBigInt("57896044618658097711785492504343953926634992332820282019728792003956564819967")
      |    val workUnsigned = if (targetSanityOk) {
      |        (maxWorkNumerator / (target.toUnsigned + unsignedBigInt("1"))) + unsignedBigInt("1")
      |    } else {
      |        unsignedBigInt("0")
      |    }
      |    val workFitsSigned = workUnsigned <= maxSignedWork
      |    val work = if (workFitsSigned) workUnsigned.toSigned else bigInt("0")
      |
      |    // best chain header record
      |    val headerRow = (id, headerBytes ++ longToByteArray(tipHeight.toLong + 1))
      |
      |    val validTipUpdate = if(prevBlockId == tipHash) {
      |
      |        val proof = getVar[Coll[Byte]](2).get
      |
      |        val nextTree: Option[AvlTree] = bestChainDigest.insert(Coll(headerRow), proof)
      |         // This will fail if the operation failed or the proof is incorrect due to calling .get on the Option
      |        val outputDigest: Coll[Byte] = nextTree.get.digest
      |
      |        val outBestChainTree = selfOut.R4[AvlTree].get
      |
      |        val cumWork = tipWork + work
      |
      |        outBestChainTree.digest == outputDigest &&
      |        outBestChainTree.enabledOperations == bestChainDigest.enabledOperations &&
      |        selfOut.R6[Int].get == tipHeight + 1 &&
      |        selfOut.R7[Coll[Byte]].get == id &&
      |        selfOut.R8[BigInt].get == cumWork
      |    } else {
      |        true
      |    }
      |
      |    val allHeadersDbUpdate = {
      |
      |        val parentProof = getVar[Coll[Byte]](3).get
      |        val parentData = allHeadersDigest.get(prevBlockId, parentProof).get
      |
      |        // parentData stores the full parent header so retarget checks can read timestamp and nBits.
      |        val parentHeight = byteArrayToLong(parentData.slice(80, 88))
      |        val nextHeight = parentHeight + 1
      |
      |        val parentChainDigest = parentData.slice(88, 121)
      |
      |        val parentChainProvided = getVar[AvlTree](4).get
      |
      |        val difficultyTransitionOk = if (nextHeight % 2016L == 0L) {
      |            val anchorId = getVar[Coll[Byte]](8).get
      |            val anchorProof = getVar[Coll[Byte]](9).get
      |            val anchorData = parentChainProvided.get(anchorId, anchorProof).get
      |            val anchorHeader = anchorData.slice(0, 80)
      |            val anchorHeight = byteArrayToLong(anchorData.slice(80, 88))
      |            val anchorTime = byteArrayToLong(pad ++ reverse4(anchorHeader.slice(68, 72)))
      |            val parentTime = byteArrayToLong(pad ++ reverse4(parentData.slice(68, 72)))
      |            val rawTimespan = parentTime - anchorTime
      |            val boundedTimespan = if (rawTimespan < 302400L) {
      |                302400L
      |            } else {
      |                if (rawTimespan > 4838400L) 4838400L else rawTimespan
      |            }
      |            val boundedTimespanBigInt = byteArrayToBigInt(longToByteArray(boundedTimespan))
      |            val parentNbitsBytes = reverse4(parentData.slice(72, 76))
      |            val parentNbits = byteArrayToLong(pad ++ parentNbitsBytes)
      |            val parentTarget = Global.decodeNbits(parentNbits)
      |            val rawExpectedTarget = parentTarget * boundedTimespanBigInt / bigInt("1209600")
      |            val expectedTarget = if (rawExpectedTarget > bitcoinPowLimit) bitcoinPowLimit else rawExpectedTarget
      |
      |            anchorHeight == nextHeight - 2016L &&
      |            anchorId == headerId(anchorHeader) &&
      |            parentTarget > bigInt("0") &&
      |            parentTarget <= bitcoinPowLimit &&
      |            Global.encodeNbits(expectedTarget) == nbits
      |        } else {
      |            headerBytes.slice(72, 76) == parentData.slice(72, 76)
      |        }
      |
      |        val parentCumWork = byteArrayToBigInt(parentData.slice(121, parentData.size))
      |        val cumWork = parentCumWork + work
      |
      |        val parentChainUpdateProof = getVar[Coll[Byte]](5).get
      |        val updDigest = parentChainProvided.insert(Coll(headerRow), parentChainUpdateProof).get.digest
      |
      |        val allHeadersInsertProof = getVar[Coll[Byte]](6).get
      |        val cumWorkProvided = getVar[Coll[Byte]](7).get
      |
      |        val keyVal = (id, (headerBytes ++ longToByteArray(parentHeight + 1) ++ updDigest ++ cumWorkProvided))
      |        val allHeadersDbUpdated = allHeadersDigest.insert(Coll(keyVal), allHeadersInsertProof).get
      |        val newAllHeadersDigestProvided = selfOut.R5[AvlTree].get
      |
      |        val allHeadersUpdateOk = parentChainProvided.digest == parentChainDigest &&
      |                                    cumWork == byteArrayToBigInt(cumWorkProvided) &&
      |                                    allHeadersDbUpdated == newAllHeadersDigestProvided &&
      |                                    difficultyTransitionOk
      |
      |        if (cumWork > tipWork && prevBlockId != tipHash) {
      |            // switch to better chain
      |
      |            val outBestChainTree = selfOut.R4[AvlTree].get
      |
      |            val switchOk = outBestChainTree.digest == updDigest &&
      |                            outBestChainTree.enabledOperations == bestChainDigest.enabledOperations &&
      |                            selfOut.R6[Int].get == parentHeight + 1 &&
      |                            selfOut.R7[Coll[Byte]].get == id &&
      |                            selfOut.R8[BigInt].get == cumWork
      |
      |            allHeadersUpdateOk && switchOk
      |        } else {
      |            // add header along with metadata to all-headers tree
      |            val noSwitchOk = if (prevBlockId == tipHash) {
      |                true
      |            } else {
      |                val outBestChainTree = selfOut.R4[AvlTree].get
      |                outBestChainTree.digest == bestChainDigest.digest &&
      |                outBestChainTree.enabledOperations == bestChainDigest.enabledOperations &&
      |                selfOut.R6[Int].get == tipHeight &&
      |                selfOut.R7[Coll[Byte]].get == tipHash &&
      |                selfOut.R8[BigInt].get == tipWork
      |            }
      |
      |            allHeadersUpdateOk && noSwitchOk
      |        }
      |    }
      |
      |    val selfPreservation = selfOut.value >= SELF.value && selfOut.tokens == SELF.tokens
      |
      |    sigmaProp(validHeaderSize && validPow && workFitsSigned && selfPreservation && validTipUpdate && allHeadersDbUpdate)
      |}""".stripMargin

  private val btcTxCheckScript: String =
    """{
      |    // context vars:
      |    // #1 - tx bytes
      |    // #2 - header id
      |    // #3 - headerProof
      |    // #4 - Merkle proof
      |
      |    // registers:
      |    // no registers used
      |
      |    // Reference fixture relay NFT id. A deployed relay would substitute its real relay NFT.
      |    val relayNftId = fromBase16("0000000000000000000000000000000000000000000000000000000000000000")
      |    val minConfs = 6 // minimum 6 confirmations required
      |
      |    val relayDataInput = CONTEXT.dataInputs(0)
      |
      |    val properRelay = relayDataInput.tokens(0)._1 == relayNftId
      |
      |    def doubleSha256(bytes: Coll[Byte]) = sha256(sha256(bytes))
      |
      |    val txBytes = getVar[Coll[Byte]](1).get
      |    val txId = doubleSha256(txBytes)
      |
      |    // Transaction amount/recipient parsing is composed by the amount-binding parser example.
      |
      |    val headerId = getVar[Coll[Byte]](2).get
      |
      |    val headerProof = getVar[Coll[Byte]](3).get
      |
      |    val bestChain = relayDataInput.R4[AvlTree].get
      |
      |    val headerAndHeight = bestChain.get(headerId, headerProof).get
      |
      |    val height = byteArrayToLong(headerAndHeight.slice(80, 88))
      |
      |    val tipHeight = relayDataInput.R6[Int].get
      |
      |    val enoughConfs = (tipHeight - height) >= minConfs
      |
      |    val merkleRootBytes = headerAndHeight.slice(36, 68)
      |
      |    val merkleProof = getVar[Coll[Coll[Byte]]](4).get
      |    val proofShapeOk = merkleProof.forall({ (proofElem: Coll[Byte]) =>
      |        proofElem.size == 33 && (proofElem(0) == 0 || proofElem(0) == 1)
      |    })
      |
      |    def computeLevel(prevHash: Coll[Byte], proofElem: Coll[Byte]) = {
      |        val elemHash = proofElem.slice(1,33)
      |        if(proofElem(0) == 0){
      |          doubleSha256(elemHash ++ prevHash)
      |        } else {
      |          doubleSha256(prevHash ++ elemHash)
      |        }
      |    }
      |
      |    val computedMerkleRoot = merkleProof.fold(txId, computeLevel)
      |
      |    val properProof = proofShapeOk && computedMerkleRoot == merkleRootBytes
      |
      |    // This predicate authenticates relay-confirmed inclusion; spending policy is supplied by the composing contract.
      |
      |    sigmaProp(properRelay && enoughConfs && properProof)
      |}""".stripMargin
}
