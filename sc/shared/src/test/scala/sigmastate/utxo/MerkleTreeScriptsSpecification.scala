package sigmastate.utxo

import scorex.crypto.authds.LeafData
import scorex.crypto.authds.merkle.MerkleTree
import scorex.crypto.authds.merkle.serialization.BatchMerkleProofSerializer
import scorex.crypto.hash.{Blake2b256, Digest32}
import org.ergoplatform.dsl.{ContractSpec, SigmaContractSyntax, TestContractSpec}
import sigma.Colls
import sigma.VersionContext
import sigma.VersionContext.V7SoftForkVersion
import sigma.ast._
import sigma.compiler.ir.IRContext
import sigma.data.{CMerkleTree, MerkleTreeData}
import sigma.interpreter.ProverResult
import sigmastate.eval.Extensions.MerkleTreeOps
import sigmastate.helpers.TestingHelpers.createBox
import sigmastate.helpers.{CompilerTestingCommons, ErgoLikeContextTesting, ErgoLikeTestInterpreter}
import sigmastate.utils.Helpers._

/** End-to-end specification for the static MerkleTree type introduced in v7.0
  * (see https://github.com/ergoplatform/sigmastate-interpreter/issues/296).
  *
  * Each test builds a real Merkle tree via scrypto, generates a proof, then constructs
  * an ErgoTree expression that invokes the corresponding [[SMerkleTreeMethods]] method.
  * The expression is reduced via the JIT interpreter under a v7-activated VersionContext
  * to confirm the method dispatch and verifier wiring work end-to-end.
  */
class MerkleTreeScriptsSpecification extends CompilerTestingCommons { suite =>
  implicit lazy val IR: IRContext = new TestingIRContext

  private implicit val hf: Blake2b256.type = Blake2b256
  private val proofSerializer = new BatchMerkleProofSerializer[Digest32, Blake2b256.type]()

  private def buildTree(numLeaves: Int): (MerkleTree[Digest32], Seq[Array[Byte]]) = {
    val leaves: Seq[Array[Byte]] = (0 until numLeaves).map(i => Blake2b256.hash(s"leaf-$i"))
    val payload: Seq[LeafData] = leaves.map(LeafData @@ _)
    (MerkleTree[Digest32](payload), leaves)
  }

  private def merkleTreeValue(tree: MerkleTree[Digest32]): sigma.MerkleTree =
    CMerkleTree(MerkleTreeData(Colls.fromArray(tree.rootHash)))

  private def roundTripAndVerify(expr: Value[SBoolean.type]): (Boolean, Long) = {
    val original = ErgoTree.fromProposition(
      ErgoTree.headerWithVersion(ErgoTree.ZeroHeader, V7SoftForkVersion),
      BoolToSigmaProp(expr)
    )
    val serializer = sigma.serialization.ErgoTreeSerializer.DefaultSerializer
    val decoded = serializer.deserializeErgoTree(serializer.serializeErgoTree(original))
    val context = ErgoLikeContextTesting.dummy(createBox(0, decoded), V7SoftForkVersion)

    new ErgoLikeTestInterpreter()
      .verify(decoded, context, ProverResult.empty, fakeMessage)
      .getOrThrow
  }

  property("MerkleTree.containsLeaf reduces to true under v7") {
    VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      val (tree, leaves) = buildTree(8)
      val proof = tree.proofByIndices(Seq(3)).get
      val proofBytes = proofSerializer.serialize(proof)

      val expr = MethodCall(
        MerkleTreeConstant(merkleTreeValue(tree)),
        SMerkleTreeMethods.containsLeafMethod,
        Vector(ByteArrayConstant(leaves(3)), ByteArrayConstant(proofBytes)),
        Map()
      ).asInstanceOf[Value[SBoolean.type]]

      roundTripAndVerify(expr)._1 shouldBe true
    }
  }

  property("MerkleTree.containsLeaf rejects wrong leaf under v7") {
    VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      val (tree, leaves) = buildTree(8)
      // Proof is for index 3, but we pass leaves(0) -> must reject.
      val proof = tree.proofByIndices(Seq(3)).get
      val proofBytes = proofSerializer.serialize(proof)

      val expr = MethodCall(
        MerkleTreeConstant(merkleTreeValue(tree)),
        SMerkleTreeMethods.containsLeafMethod,
        Vector(ByteArrayConstant(leaves(0)), ByteArrayConstant(proofBytes)),
        Map()
      ).asInstanceOf[Value[SBoolean.type]]

      roundTripAndVerify(expr)._1 shouldBe false
    }
  }

  property("MerkleTree.containsLeaf source, Scala DSL, and serialized execution agree") {
    VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      val (tree, leaves) = buildTree(8)
      val proof = tree.proofByIndices(Seq(3)).get
      val proofBytes = Colls.fromArray(proofSerializer.serialize(proof))
      val leaf = Colls.fromArray(leaves(3))
      val treeValue = merkleTreeValue(tree)

      val scalaResult = treeValue.containsLeaf(leaf, proofBytes)
      val compiled = compile(
        Map("tree" -> treeValue, "leaf" -> leaf, "proof" -> proofBytes),
        "tree.containsLeaf(leaf, proof)").asInstanceOf[Value[SBoolean.type]]

      scalaResult shouldBe true
      roundTripAndVerify(compiled)._1 shouldBe scalaResult
    }
  }

  property("MerkleTree.containsLeaves accepts a real batch proof under v7") {
    VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      val (tree, leaves) = buildTree(16)
      val indices = Seq(1, 4, 9, 13)
      val proof = tree.proofByIndices(indices).get
      val proofBytes = proofSerializer.serialize(proof)

      val claimed = Colls.fromArray(indices.map(i => Colls.fromArray(leaves(i))).toArray)
      val expr = MethodCall(
        MerkleTreeConstant(merkleTreeValue(tree)),
        SMerkleTreeMethods.containsLeavesMethod,
        Vector(
          CollectionConstant[SCollection[SByte.type]](claimed, SCollection(SByte)),
          ByteArrayConstant(proofBytes)
        ),
        Map()
      ).asInstanceOf[Value[SBoolean.type]]

      roundTripAndVerify(expr)._1 shouldBe true
    }
  }

  property("MerkleTreeMethods are unavailable under v6") {
    VersionContext.withVersions(VersionContext.V6SoftForkVersion, VersionContext.V6SoftForkVersion) {
      SMerkleTreeMethods.methods shouldBe empty
    }
  }

  property("MerkleTreeMethods are unavailable under v5") {
    val v5: Byte = (VersionContext.V6SoftForkVersion - 1).toByte
    VersionContext.withVersions(VersionContext.V6SoftForkVersion, v5) {
      SMerkleTreeMethods.methods shouldBe empty
    }
  }

  property("MerkleTreeMethods are available under v7") {
    VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      val methodNames = SMerkleTreeMethods.methods.map(_.name).toSet
      methodNames should contain allOf ("digest", "updateDigest", "containsLeaf", "containsLeaves")
    }
  }

  property("MerkleTree contract environment compiles under v7") {
    case class MerkleTreeEnvContract[Spec <: ContractSpec](tree: sigma.MerkleTree)
        (implicit val spec: Spec) extends SigmaContractSyntax {
      lazy val contractEnv = Env("tree" -> tree)
      lazy val treeProp = proposition(
        "treeProp",
        _ => sigmaProp(true),
        "sigmaProp(tree.digest == tree.digest)",
        Some(V7SoftForkVersion))
    }

    VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      implicit val spec = TestContractSpec(suite)(IR)
      val (tree, _) = buildTree(8)
      val contract = MerkleTreeEnvContract[spec.type](merkleTreeValue(tree))(spec)
      contract.treeProp.ergoTree.version shouldBe V7SoftForkVersion
    }
  }

  property("MerkleTree ErgoTree cannot be serialized under v5/v6 headers") {
    val (tree, leaves) = buildTree(8)
    val proof = tree.proofByIndices(Seq(3)).get
    val proofBytes = proofSerializer.serialize(proof)
    val mt = merkleTreeValue(tree)

    // The MethodCall has to be built under v7 (so the method resolves), but the
    // resulting ErgoTree, when serialized under a pre-v7 header, switches the
    // VersionContext internally and must fail.
    val expr = VersionContext.withVersions(V7SoftForkVersion, V7SoftForkVersion) {
      MethodCall(
        MerkleTreeConstant(mt),
        SMerkleTreeMethods.containsLeafMethod,
        Vector(ByteArrayConstant(leaves(3)), ByteArrayConstant(proofBytes)),
        Map()
      )
    }

    val sigmaProp = BoolToSigmaProp(expr.asInstanceOf[Value[SBoolean.type]])
    Seq(0.toByte, 1.toByte, 2.toByte, VersionContext.V6SoftForkVersion).foreach { ver =>
      val header = ErgoTree.headerWithVersion(ErgoTree.ZeroHeader, ver)
      a[Exception] should be thrownBy {
        val tree = ErgoTree.fromProposition(header, sigmaProp)
        sigma.serialization.ErgoTreeSerializer.DefaultSerializer.serializeErgoTree(tree)
      }
    }
  }
}
