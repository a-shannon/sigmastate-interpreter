package sigma.ast

import org.scalatest.matchers.should.Matchers
import org.scalatest.propspec.AnyPropSpec
import sigma.VersionContext

/** Cross-platform safety net for the JS reflection registry in
  * [[sigma.reflection.ReflectionData]].
  *
  * Most new `SMethod` declarations resolve their Java handler eagerly via
  * `.withIRInfo(MethodCallIrBuilder, javaMethodOf[T, A]("name"))`. On JVM that
  * goes through `java.lang.reflect`; on JS it goes through the hand-written
  * `sigma.reflection` registry. A missing registry entry throws
  * `NoSuchMethodException` the first time the enclosing `lazy val SMethod` is
  * forced, which can be deep in serializer-spec land instead of here.
  *
  * Forcing `container.methods` under every supported `(activatedVersion,
  * ergoTreeVersion)` combination through
  * [[VersionContext.V7SoftForkVersion]] triggers every per-version lazy method table,
  * surfacing missing registry entries here rather than in a downstream consumer.
  */
class MethodsContainerSpec extends AnyPropSpec with Matchers {

  private val reflection = sigmastate.InterpreterReflection

  // Range covers every script version through V7 explicitly so this test remains
  // independent from the default CrossVersionProps matrix.
  private val versions: Seq[Byte] =
    (0 to VersionContext.V7SoftForkVersion).map(_.toByte)

  private val combinations: Seq[(Byte, Byte)] =
    for {
      activated <- versions
      ergoTree  <- versions if ergoTree <= activated
    } yield (activated, ergoTree)

  property("every MethodsContainer builds its method table on this platform") {
    combinations.foreach { case (activated, ergoTree) =>
      VersionContext.withVersions(activated, ergoTree) {
        val containers =
          if (VersionContext.current.isV3OrLaterErgoTreeVersion) MethodsContainer.methodsV6
          else MethodsContainer.methodsV5

        containers.foreach { container =>
          try container.methods
          catch {
            case t: Throwable =>
              fail(
                s"Failed building method table for ${container.typeName} " +
                  s"under (activated=$activated, ergoTree=$ergoTree): ${t.getMessage}",
                t
              )
          }
        }
      }
    }
  }

  property("MerkleTree methods resolve their cross-platform handlers") {
    reflection should not be null

    VersionContext.withVersions(
      VersionContext.V7SoftForkVersion,
      VersionContext.V7SoftForkVersion) {
      SMerkleTreeMethods.digestMethod.javaMethod.getName shouldBe "digest"
      SMerkleTreeMethods.updateDigestMethod.javaMethod.getName shouldBe "updateDigest"
      SMerkleTreeMethods.containsLeafMethod.evalMethod.getName shouldBe "containsLeaf_eval"
      SMerkleTreeMethods.containsLeavesMethod.evalMethod.getName shouldBe "containsLeaves_eval"
    }
  }

  property("SigmaProp.propBytesV2 resolves its cross-platform handlers") {
    reflection should not be null

    VersionContext.withVersions(
      VersionContext.V7SoftForkVersion,
      VersionContext.V7SoftForkVersion) {
      SSigmaPropMethods.PropBytesMethodV2.javaMethod.getName shouldBe "propBytes"
      SSigmaPropMethods.PropBytesMethodV2.evalMethod.getName shouldBe "propBytesV2_eval"
    }
  }
}
