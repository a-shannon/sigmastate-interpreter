/*
 * SPDX-License-Identifier: MIT
 *
 * Copyright 2026 A. Shannon.
 */
package sigma.eval

import java.io.ByteArrayOutputStream
import java.nio.charset.StandardCharsets

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import sigma.VersionContext
import sigma.ast.SCollection.SByteArray
import sigma.ast._
import sigma.ast.syntax.TrueSigmaProp
import sigma.stark.profile.RawSealV1Decoder.WrongChunkLength
import sigma.stark.profile.Risc0RawSealVerifier.{ClaimMismatch, TransportRejected, Verified}
import sigma.stark.profile.{ProfileBlake2b256, Risc0ClaimBuilder, Risc0ProfilePackageLoader}
import sigmastate.helpers.ErgoLikeContextTesting
import sigmastate.helpers.TestingHelpers.createBox
import sigmastate.interpreter.{CErgoTreeEvaluator, CostAccumulator}

class Eip0045StockRuntimeNegativePathSpec extends AnyFunSuite with Matchers {
  import StarkVerificationCapability._

  private val PackageRoot = "/stark-kats/eip0045-profile-package/"
  private val DirectRoot = "/stark-kats/eip0045-direct/"
  private val ChainDomainId = Array.tabulate[Byte](ProfileIdBytes)(i => (i + 1).toByte)
  private val ProgramId = Array.tabulate[Byte](ProfileIdBytes)(i => (0xa0 + i).toByte)
  private val Payload = "stock-runtime-negative-path".getBytes(StandardCharsets.UTF_8)
  private val DispatchSentinel = 1709
  private val FixedSentinel = 2903
  private val StaticProfileIdEvalCost = 5

  private def resourceBytes(path: String): Array[Byte] = {
    val in = getClass.getResourceAsStream(path)
    require(in != null, "missing test resource " + path)
    val out = new ByteArrayOutputStream()
    val buffer = new Array[Byte](8192)
    try {
      var read = in.read(buffer)
      while (read >= 0) {
        if (read > 0) out.write(buffer, 0, read)
        read = in.read(buffer)
      }
      out.toByteArray
    } finally {
      in.close()
      out.close()
    }
  }

  private lazy val loadedProfile = Risc0ProfilePackageLoader.load(
    resourceBytes(PackageRoot + "manifest.bin"),
    resourceBytes(PackageRoot + "algorithm.txt"),
    resourceBytes(PackageRoot + "constants.bin"),
    resourceBytes(PackageRoot + "profile-id.bin")) match {
    case Right(value) => value
    case Left(failure) => fail("frozen B1/B2/B3 package rejected: " + failure)
  }

  private lazy val rawSeal = resourceBytes(DirectRoot + "po2-15-raw-seal.bin")
  private lazy val retainedClaim = resourceBytes(DirectRoot + "po2-15-claim-digest.bin")

  private def canonicalChunks(bytes: Array[Byte]): Array[Array[Byte]] = {
    val lengths = Array(65535, 65535, 65535, 26063)
    val result = new Array[Array[Byte]](lengths.length)
    var offset = 0
    var i = 0
    while (i < lengths.length) {
      result(i) = java.util.Arrays.copyOfRange(bytes, offset, offset + lengths(i))
      offset += lengths(i)
      i += 1
    }
    result
  }

  private def runtime = Risc0StockProfileRuntime.fromLoadedProfile(loadedProfile) match {
    case Right(value) => value
    case Left(failure) => fail("stock runtime rejected frozen profile: " + failure)
  }

  private def capability = {
    val entry = active(runtime, FixedSentinel) match {
      case Right(value) => value
      case Left(failure) => fail("active entry rejected: " + failure)
    }
    snapshot(
      ChainDomainId,
      protocolGeneration = 10,
      HistoricalBlockValidation,
      DispatchSentinel,
      Vector(entry)) match {
      case Right(value) => value
      case Left(failure) => fail("active snapshot rejected: " + failure)
    }
  }

  private def evaluator(): CErgoTreeEvaluator = {
    val settings = CErgoTreeEvaluator.DefaultEvalSettings
    val accumulator = new CostAccumulator(JitCost(0), Some(JitCost.fromBlockCost(1000000)))
    val tree = ErgoTree.fromProposition(TrueSigmaProp)
    val box = createBox(1000000L, tree)
    val sigmaContext = ErgoLikeContextTesting.dummy(
      box,
      activatedVersion = VersionContext.StarkVerificationVersion)
      .withErgoTreeVersion(VersionContext.StarkVerificationVersion)
      .toSigmaContext()
    new CErgoTreeEvaluator(
      sigmaContext,
      ErgoTree.EmptyConstants,
      accumulator,
      CErgoTreeEvaluator.DefaultProfiler,
      settings,
      capability)
  }

  private def evalDirect(evaluator: CErgoTreeEvaluator, value: Value[_ <: SType]): Any =
    VersionContext.withVersions(
      VersionContext.StarkVerificationVersion,
      VersionContext.StarkVerificationVersion) {
      evaluator.eval(Map.empty, value)
    }

  private def proofValue(
      values: Array[Array[Byte]]): Value[SCollection[SCollection[SByte.type]]] =
    ConcreteCollection[SByteArray](
      values.iterator.map(ByteArrayConstant(_)).toIndexedSeq,
      SByteArray).asInstanceOf[Value[SCollection[SCollection[SByte.type]]]]

  private def node(
      proof: Array[Array[Byte]],
      payload: Array[Byte] = Payload,
      programId: Array[Byte] = ProgramId): VerifyStark =
    VerifyStark(
      proofValue(proof),
      ByteArrayConstant(payload),
      ByteArrayConstant(programId),
      ByteArrayConstant(loadedProfile.profileId))

  private def buildBinding(
      chainDomainId: Array[Byte],
      programId: Array[Byte],
      contractId: Array[Byte],
      payload: Array[Byte]): Risc0ClaimBuilder.Binding =
    Risc0ClaimBuilder.build(
      loadedProfile,
      chainDomainId,
      programId,
      contractId,
      payload) match {
      case Right(value) => value
      case Left(failure) => fail("ErgoStatementV1 construction rejected: " + failure)
    }

  private def flipFirst(value: Array[Byte]): Array[Byte] = {
    val result = value.clone()
    result(0) = (result(0) ^ 1).toByte
    result
  }

  test("retained po2-15 claim accepts before the host-derived claim reaches ClaimMismatch") {
    val proof = canonicalChunks(rawSeal)
    loadedProfile.verifier.verify(proof, retainedClaim) shouldBe Right(Verified(1, 15))

    val e = evaluator()
    val contractId = ProfileBlake2b256.hash(e.context.SELF.propositionBytes.toArray)
    val binding = buildBinding(
      ChainDomainId,
      ProgramId,
      contractId,
      Payload)

    binding.statement.length shouldBe Risc0ClaimBuilder.StatementPrefixBytes + Payload.length
    binding.expectedClaim.sameElements(retainedClaim) shouldBe false

    loadedProfile.verifier.verify(proof, binding.expectedClaim) shouldBe
      Left(ClaimMismatch)

    evalDirect(e, node(proof)) shouldBe false
  }

  test("dispatch and fixed sentinels are charged before program payload and proof children") {
    val inaccessibleBytes = ConstantPlaceholder(0, SByteArray)
    val inaccessibleChunks = ConstantPlaceholder(0, SCollection(SByteArray))
      .asInstanceOf[Value[SCollection[SCollection[SByte.type]]]]
    val call = VerifyStark(
      inaccessibleChunks,
      inaccessibleBytes,
      inaccessibleBytes,
      ByteArrayConstant(loadedProfile.profileId))
    val e = evaluator()
    val before = e.getAccumulatedCost.value

    an[IndexOutOfBoundsException] shouldBe thrownBy(evalDirect(e, call))
    e.getAccumulatedCost.value - before shouldBe
      StaticProfileIdEvalCost + DispatchSentinel + FixedSentinel
  }

  test("one host field mutation at a time changes the claim without changing proof transport") {
    val proof = canonicalChunks(rawSeal)
    loadedProfile.verifier.verify(proof, retainedClaim) shouldBe Right(Verified(1, 15))
    val e = evaluator()
    val contractId = ProfileBlake2b256.hash(e.context.SELF.propositionBytes.toArray)
    val baseline = buildBinding(ChainDomainId, ProgramId, contractId, Payload)
    val mutations = Vector(
      ("chain-domain-id", flipFirst(ChainDomainId), ProgramId, contractId, Payload),
      ("program-id", ChainDomainId, flipFirst(ProgramId), contractId, Payload),
      ("contract-id", ChainDomainId, ProgramId, flipFirst(contractId), Payload),
      ("application-payload", ChainDomainId, ProgramId, contractId, flipFirst(Payload)))

    mutations.foreach { case (label, chain, program, contract, payload) =>
      withClue(label + ": ") {
        val changedFields = Vector(
          !chain.sameElements(ChainDomainId),
          !program.sameElements(ProgramId),
          !contract.sameElements(contractId),
          !payload.sameElements(Payload)).count(identity)
        changedFields shouldBe 1

        val binding = buildBinding(chain, program, contract, payload)
        binding.statement.sameElements(baseline.statement) shouldBe false
        binding.expectedClaim.sameElements(baseline.expectedClaim) shouldBe false
        binding.expectedClaim.sameElements(retainedClaim) shouldBe false

        loadedProfile.verifier.verify(proof, binding.expectedClaim) shouldBe
          Left(ClaimMismatch)
      }
    }
  }

  test("one transport mutation is typed at the decoder and remains false at the active adapter") {
    val proof = canonicalChunks(rawSeal)
    val shortened = proof.map(_.clone())
    shortened(0) = java.util.Arrays.copyOf(shortened(0), shortened(0).length - 1)
    shortened(0).sameElements(proof(0)) shouldBe false
    shortened.iterator.drop(1).zip(proof.iterator.drop(1)).forall {
      case (left, right) => left.sameElements(right)
    } shouldBe true

    loadedProfile.verifier.verify(shortened, retainedClaim) shouldBe
      Left(TransportRejected(WrongChunkLength(0, 65535, 65534)))

    val e = evaluator()
    val before = e.getAccumulatedCost.value
    evalDirect(e, node(shortened)) shouldBe false
    e.getAccumulatedCost.value - before should be >=
      (DispatchSentinel + FixedSentinel)
  }
}
