package sigmastate.lang

import org.ergoplatform.ErgoAddressEncoder.TestnetNetworkPrefix
import org.scalatest.matchers.should.Matchers
import org.scalatest.propspec.AnyPropSpec
import sigma.VersionContext
import sigma.ast.SCollection.SByteArray
import sigma.ast.{SFunc, SMerkleTree, SType, TransformingSigmaBuilder}
import sigma.ast.SigmaPredef.PredefinedFuncRegistry
import sigma.compiler.phases.{SigmaBinder, SigmaTyper}
import sigmastate.interpreter.Interpreter.ScriptEnv
import sigmastate.lang.parsers.ParserException

class MerkleTreeSourceSpecification extends AnyPropSpec with Matchers {
  private val source = "{ (tree: MerkleTree) => tree.digest }"

  private def typecheck(version: Byte): SType =
    VersionContext.withVersions(version, version) {
      val builder = TransformingSigmaBuilder
      val registry = new PredefinedFuncRegistry(builder)
      val env: ScriptEnv = Map.empty
      val parsed = SigmaParser(source).get.value
      val bound = new SigmaBinder(env, builder, TestnetNetworkPrefix, registry).bind(parsed)
      val typer = new SigmaTyper(builder, registry, Map.empty, lowerMethodCalls = true)
      typer.typecheck(bound).tpe
    }

  property("MerkleTree source typechecks under script v4") {
    typecheck(VersionContext.V7SoftForkVersion) shouldBe
      SFunc(IndexedSeq(SMerkleTree), SByteArray)
  }

  property("MerkleTree source method is rejected before script v4") {
    an[ParserException] should be thrownBy typecheck(VersionContext.V6SoftForkVersion)
  }
}
