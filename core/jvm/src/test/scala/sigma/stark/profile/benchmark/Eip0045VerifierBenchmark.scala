/*
 * SPDX-License-Identifier: MIT AND Apache-2.0
 *
 * Copyright 2026 A. Shannon.
 */
package sigma.stark.profile.benchmark

import java.io.{ByteArrayOutputStream, IOException}
import java.lang.management.{ManagementFactory, MemoryPoolMXBean, MemoryUsage}
import java.nio.charset.StandardCharsets
import java.nio.file.{FileAlreadyExistsException, Files, Paths, StandardOpenOption}
import java.time.Instant

import sigma.stark.FriVerifier
import sigma.stark.profile.{
  RawSealV1Decoder,
  Risc0ClaimBuilder,
  Risc0ProfilePackageLoader,
  Risc0RawSealVerifier
}
import sigma.stark.profile.Risc0RawSealVerifier.{
  ClaimMismatch,
  ControlIdNotAllowed,
  Failure,
  MalformedProof,
  Probe,
  TransportRejected,
  Verified
}
import sigma.stark.profile.benchmark.Eip0045BenchmarkSupport._
import sigma.stark.profile.benchmark.Eip0045CampaignContract._

import scala.collection.JavaConverters._
import scala.io.Source
import scala.util.Properties
import scala.util.control.NonFatal

/** Opt-in B5 evidence harness for the EIP-0045 stock-profile JVM verifier.
  *
  * Full benchmark campaigns run explicitly with `coreJVM/Test/runMain`. The
  * object is not itself a ScalaTest suite; focused support tests call it only
  * for bounded zero-warmup, one-sample smoke runs. Each run authenticates the
  * frozen B1/B2/B3 package through the production loader, validates all six
  * scenario paths, warms them in a
  * rotating schedule, then records one complete verifier invocation per
  * sample. It never derives or recommends a consensus fixedJit value.
  */
object Eip0045VerifierBenchmark {
  private val PackageRoot = "/stark-kats/eip0045-profile-package/"
  private val DirectRoot = "/stark-kats/eip0045-direct/"
  private val IndependentRoot = "/stark-kats/eip0045-arkadia-independent/"
  private val ExpectedProfileId =
    "23c4a123ffb33a1c8db89436fe0e7972bd8e4e289459ee5fd71be5440607d383"
  private val ExpectedSealSha256 =
    "088e6a306c7143f5a3e057924c42f63a6eb58dd3c30686a8ade5082fac4b386e"
  private val ExpectedClaimSha256 =
    "df9df2763693f97b85acd9d3cda4b13e2421b3dc052a6f91ab995c89ae75ee3c"
  private val ChunkLengths = Array(65535, 65535, 65535, 26063)

  @volatile private var blackhole: Int = 0
  private val MemoryPoolMeasurementLock = new AnyRef

  private[benchmark] trait ExecutionObserver {
    def beforeVerifierSetup(): Unit
    def beforeOutput(): Unit
    def beforeValidationInvocation(): Unit = ()
    def beforeWarmupInvocation(): Unit = ()
    def beforeTimedInvocation(): Unit = ()
  }

  private object NoExecutionObserver extends ExecutionObserver {
    override def beforeVerifierSetup(): Unit = ()
    override def beforeOutput(): Unit = ()
  }

  private final class ValidationProbe extends Probe {
    var queries: Int = 0
    var lastCheckpoint: String = "none"
    override def onCheckpoint(label: String, _values: Array[Int]): Unit = {
      lastCheckpoint = label
      if (label == "query") queries += 1
    }
  }

  private final case class Scenario(
      id: String,
      expectedOutcome: String,
      expectedQueries: Int,
      expectedValidationBoundary: String,
      expectedLastCheckpoint: String,
      run: () => Either[Failure, Verified],
      runWithProbe: Probe => Either[Failure, Verified])

  private final case class ProofFixture(
      rawSeal: Array[Byte],
      expectedClaim: Array[Byte])

  private final case class Fixture(
      verifier: Risc0RawSealVerifier,
      primary: ProofFixture,
      independent: ProofFixture,
      resources: Vector[ResourceMetadata])

  private final case class Measurements(
      timingSamples: Array[Array[Long]],
      allocationSamples: Array[Array[Long]],
      garbageCollectorDeltas: Vector[GarbageCollectorDelta],
      memoryPoolPhaseEnvelopes: Vector[MemoryPoolPhaseEnvelope])

  private final case class ValidationResult(
      queryCheckpoints: Int,
      boundary: String,
      lastVerifierCheckpoint: String)

  private final class ThreadAllocationMeter(
      bean: com.sun.management.ThreadMXBean,
      threadId: Long) {
    val description: String =
      "com.sun.management.ThreadMXBean.getThreadAllocatedBytes(currentThread)"

    def read(): Long = {
      val value = bean.getThreadAllocatedBytes(threadId)
      if (value < 0L)
        throw new IllegalStateException("thread allocation counter became unavailable")
      value
    }
  }

  private[benchmark] trait MemoryPoolHandle {
    def identity: MemoryPoolIdentity
    def isValid: Boolean
    def resetPeakUsage(): Unit
    def usage(): MemoryUsageEvidence
    def peakUsage(): MemoryUsageEvidence
  }

  private[benchmark] trait MemoryPoolSource {
    def handles(): Vector[MemoryPoolHandle]
  }

  private[benchmark] final case class MemoryPoolTopology(
      handles: Vector[MemoryPoolHandle],
      identities: Vector[MemoryPoolIdentity])

  private final class PlatformMemoryPoolHandle(bean: MemoryPoolMXBean)
      extends MemoryPoolHandle {
    override val identity: MemoryPoolIdentity = MemoryPoolIdentity(
      bean.getName,
      if (bean.getType == null) null else bean.getType.name())

    override def isValid: Boolean = bean.isValid
    override def resetPeakUsage(): Unit = bean.resetPeakUsage()
    override def usage(): MemoryUsageEvidence = memoryUsageEvidence(bean.getUsage)
    override def peakUsage(): MemoryUsageEvidence = memoryUsageEvidence(bean.getPeakUsage)
  }

  private object PlatformMemoryPoolSource extends MemoryPoolSource {
    override def handles(): Vector[MemoryPoolHandle] =
      ManagementFactory.getMemoryPoolMXBeans.asScala
        .map(bean => new PlatformMemoryPoolHandle(bean): MemoryPoolHandle)
        .toVector
  }

  def main(args: Array[String]): Unit =
    run(args, NoExecutionObserver, PlatformMemoryPoolSource)

  private[benchmark] def runWithObserverForTest(
      args: Array[String],
      observer: ExecutionObserver): Unit = run(args, observer, PlatformMemoryPoolSource)

  private[benchmark] def runWithMemoryPoolSourceForTest(
      args: Array[String],
      observer: ExecutionObserver,
      memoryPoolSource: MemoryPoolSource): Unit = run(args, observer, memoryPoolSource)

  private[benchmark] def currentEnvironmentForTest(
      declaredCpuModel: String): EnvironmentMetadata = {
    val meter = openThreadAllocationMeter()
    val memoryPools = openMemoryPoolTopology(PlatformMemoryPoolSource)
    environmentMetadata(
      Config(0, 1, None, Some(declaredCpuModel), "commit:" + ("0" * 40), None, None),
      meter.description,
      memoryPools.identities)
  }

  private def run(
      args: Array[String],
      observer: ExecutionObserver,
      memoryPoolSource: MemoryPoolSource): Unit = {
    if (observer == null)
      throw new IllegalArgumentException("benchmark execution observer is null")
    if (memoryPoolSource == null)
      throw new IllegalArgumentException("benchmark memory pool source is null")
    MemoryPoolMeasurementLock.synchronized {
      runSerialized(args, observer, memoryPoolSource)
    }
  }

  private def runSerialized(
      args: Array[String],
      observer: ExecutionObserver,
      memoryPoolSource: MemoryPoolSource): Unit = {
    if (args != null && args.contains("--help")) {
      System.out.print(Usage)
      return
    }
    val config = parseArgs(args) match {
      case Right(value) => value
      case Left(detail) =>
        System.err.println("argument error: " + detail)
        System.err.print(Usage)
        throw new IllegalArgumentException(detail)
    }

    val allocationMeter = openThreadAllocationMeter()
    val memoryPools = openMemoryPoolTopology(memoryPoolSource)
    val environment = environmentMetadata(
      config,
      allocationMeter.description,
      memoryPools.identities)
    val campaignBinding = loadCampaignBinding(config, environment)

    // Campaign policy is fully resolved before profile resources are loaded or
    // any verifier object can be constructed or invoked.
    val fixture = loadFixture(observer)
    val scenarios = buildScenarios(fixture)
    val startedAt = Instant.now().toString
    val runStarted = System.nanoTime()

    val validation = scenarios.map(scenario => validateScenario(scenario, observer))
    warmUp(scenarios, config.warmupRounds, observer)
    val measurements = measure(
      scenarios,
      config.sampleRounds,
      allocationMeter,
      memoryPools,
      memoryPoolSource,
      observer)

    val duration = System.nanoTime() - runStarted
    val scenarioEvidence = scenarios.indices.map { i =>
      val sampleVector = measurements.timingSamples(i).toVector
      val summary = statistics(sampleVector) match {
        case Right(value) => value
        case Left(detail) => throw new IllegalStateException(detail)
      }
      val allocationVector = measurements.allocationSamples(i).toVector
      val allocationSummary = allocationStatistics(allocationVector) match {
        case Right(value) => value
        case Left(detail) => throw new IllegalStateException(detail)
      }
      ScenarioEvidence(
        scenarios(i).id,
        scenarios(i).expectedOutcome,
        validation(i).queryCheckpoints,
        validation(i).boundary,
        validation(i).lastVerifierCheckpoint,
        sampleVector,
        summary,
        allocationVector,
        allocationSummary)
    }.toVector

    val payload = EvidencePayload(
      startedAtUtc = startedAt,
      benchmarkDurationNs = duration,
      profileId = ExpectedProfileId,
      implementationRevision = config.implementationRevision,
      verifierEntryPoint = "sigma.stark.profile.Risc0RawSealVerifier.verify",
      resources = fixture.resources,
      warmupRounds = config.warmupRounds,
      sampleRounds = config.sampleRounds,
      campaignBinding = campaignBinding,
      environment = environment,
      scenarios = scenarioEvidence,
      garbageCollectorDeltas = measurements.garbageCollectorDeltas,
      memoryPoolPhaseEnvelopes = measurements.memoryPoolPhaseEnvelopes,
      limitations = (campaignBinding match {
        case Some(_) => ExpectedCampaignLimitations
        case None => ExpectedCampaignLimitations.dropRight(1) :+
          "No campaign manifest or run ID is bound, so this diagnostic is not acceptable campaign evidence."
      }) ++
        (if (config.implementationRevision == "unrecorded")
          Vector("implementationRevision is unrecorded, so this run is not acceptable campaign evidence.")
        else Vector.empty))
    val json = renderEnvelope(payload)

    config.outputPath match {
      case Some(pathText) => writeEvidenceOutput(pathText, json, observer)
      case None =>
        observer.beforeOutput()
        System.out.print(json)
    }

    // Force the verification outcomes to remain observable across the whole
    // run even under an aggressively optimizing JVM.
    if (blackhole == Int.MinValue) System.err.println("blackhole=" + blackhole)
  }

  private def loadCampaignBinding(
      config: Config,
      environment: EnvironmentMetadata): Option[CampaignBinding] =
    (config.campaignManifestPath, config.campaignRunId) match {
      case (None, None) => None
      case (Some(pathText), Some(runId)) =>
        val bytes = readBoundedCampaignManifest(pathText)
        resolveRunPolicy(
          bytes,
          runId,
          config.implementationRevision,
          config.warmupRounds,
          config.sampleRounds,
          environment) match {
          case Right(policy) => Some(policy.campaignBinding)
          case Left(detail) => throw new IllegalArgumentException(detail)
        }
      case _ =>
        throw new IllegalArgumentException(
          "campaign manifest and run ID must be supplied together")
    }

  private def readBoundedCampaignManifest(pathText: String): Array[Byte] = {
    val path = try Paths.get(pathText)
    catch {
      case _: RuntimeException =>
        throw new IllegalArgumentException("campaign manifest path is invalid")
    }
    try {
      if (!Files.isRegularFile(path))
        throw new IllegalArgumentException("campaign manifest is not a regular file")

      val in = Files.newInputStream(path)
      val out = new ByteArrayOutputStream()
      val buffer = new Array[Byte](8192)
      try {
        var read = in.read(buffer)
        while (read >= 0) {
          if (read > 0) {
            if (out.size().toLong + read.toLong > MaxCampaignManifestBytes.toLong)
              throw new IllegalArgumentException(
                "campaign manifest exceeds " + MaxCampaignManifestBytes + " bytes")
            out.write(buffer, 0, read)
          }
          read = in.read(buffer)
        }
        val bytes = out.toByteArray
        if (bytes.isEmpty)
          throw new IllegalArgumentException("campaign manifest is empty")
        bytes
      } finally {
        in.close()
        out.close()
      }
    } catch {
      case error: IllegalArgumentException => throw error
      case _: IOException | _: SecurityException =>
        throw new IllegalArgumentException("campaign manifest could not be read")
    }
  }

  private def writeEvidenceOutput(
      pathText: String,
      json: String,
      observer: ExecutionObserver): Unit = {
    val path = try Paths.get(pathText)
    catch {
      case _: RuntimeException =>
        throw new IllegalArgumentException("benchmark output path is invalid")
    }
    try {
      val parent = path.toAbsolutePath.normalize().getParent
      if (parent != null && !Files.isDirectory(parent))
        throw new IllegalArgumentException(
          "benchmark output parent directory does not exist")
      observer.beforeOutput()
      Files.write(
        path,
        json.getBytes(StandardCharsets.UTF_8),
        StandardOpenOption.CREATE_NEW,
        StandardOpenOption.WRITE)
    } catch {
      case error: IllegalArgumentException => throw error
      case _: FileAlreadyExistsException =>
        throw new IllegalArgumentException("benchmark output already exists")
      case _: IOException | _: SecurityException =>
        throw new IllegalArgumentException("benchmark output could not be created")
    }
    System.err.println("wrote EIP-0045 benchmark evidence")
  }

  private[benchmark] def deriveIndependentClaim(
      imageId: Array[Byte],
      journal: Array[Byte],
      retainedClaim: Array[Byte]): Either[String, Array[Byte]] = {
    Risc0ClaimBuilder.deriveOkClaimDigests(imageId, journal) match {
      case Left(_) => Left("independent claim inputs are invalid")
      case Right(value) =>
        val derived = value.expectedClaim
        if (!java.util.Arrays.equals(derived, retainedClaim))
          Left("independent claim does not match the retained claim resource")
        else Right(derived)
    }
  }

  private def loadFixture(observer: ExecutionObserver): Fixture = {
    observer.beforeVerifierSetup()
    val algorithm = resourceBytes(PackageRoot + "algorithm.txt")
    val constants = resourceBytes(PackageRoot + "constants.bin")
    val manifest = resourceBytes(PackageRoot + "manifest.bin")
    val profileIdResource = resourceBytes(PackageRoot + "profile-id.bin")
    val rawSeal = resourceBytes(DirectRoot + "po2-15-raw-seal.bin")
    val expectedClaim = resourceBytes(DirectRoot + "po2-15-claim-digest.bin")
    val fixtureManifest = resourceBytes(DirectRoot + "fixture-manifest.json")
    val independentRawSeal = resourceBytes(IndependentRoot + "raw-seal.bin")
    val independentRetainedClaim = resourceBytes(IndependentRoot + "claim-digest.bin")
    val independentImageId = resourceBytes(IndependentRoot + "image-id.bin")
    val independentJournal = resourceBytes(IndependentRoot + "journal.bin")
    val independentManifest = resourceBytes(IndependentRoot + "fixture-manifest.json")
    val expectedProfileBytes = decodeHex(ExpectedProfileId)

    require(
      java.util.Arrays.equals(profileIdResource, expectedProfileBytes),
      "profile-id.bin is not the frozen B3 profile ID")
    require(rawSeal.length == RawSealV1Decoder.ByteCount, "raw-seal fixture length changed")
    require(sha256Hex(rawSeal) == ExpectedSealSha256, "raw-seal fixture digest changed")
    require(expectedClaim.length == Risc0RawSealVerifier.DigestBytes, "claim fixture length changed")
    require(sha256Hex(expectedClaim) == ExpectedClaimSha256, "claim fixture digest changed")
    require(
      ChunkLengths.sum == rawSeal.length,
      "canonical chunk partition does not cover the raw-seal fixture")

    val resources = Vector(
      metadata("profile-algorithm", PackageRoot + "algorithm.txt", algorithm),
      metadata("profile-constants", PackageRoot + "constants.bin", constants),
      metadata("profile-manifest", PackageRoot + "manifest.bin", manifest),
      metadata("profile-id", PackageRoot + "profile-id.bin", profileIdResource),
      metadata("raw-seal", DirectRoot + "po2-15-raw-seal.bin", rawSeal),
      metadata("claim-digest", DirectRoot + "po2-15-claim-digest.bin", expectedClaim),
      metadata("fixture-manifest", DirectRoot + "fixture-manifest.json", fixtureManifest),
      metadata("po2-16-raw-seal", IndependentRoot + "raw-seal.bin", independentRawSeal),
      metadata(
        "po2-16-claim-digest",
        IndependentRoot + "claim-digest.bin",
        independentRetainedClaim),
      metadata("po2-16-image-id", IndependentRoot + "image-id.bin", independentImageId),
      metadata("po2-16-journal", IndependentRoot + "journal.bin", independentJournal),
      metadata(
        "po2-16-fixture-manifest",
        IndependentRoot + "fixture-manifest.json",
        independentManifest))
    require(resources == ExpectedResources, "benchmark resource identities changed")
    require(
      independentRawSeal.length == RawSealV1Decoder.ByteCount,
      "independent raw-seal fixture length changed")
    val independentExpectedClaim = deriveIndependentClaim(
      independentImageId,
      independentJournal,
      independentRetainedClaim) match {
      case Right(value) => value
      case Left(detail) => throw new IllegalStateException(detail)
    }

    val loaded = Risc0ProfilePackageLoader.load(
      manifest,
      algorithm,
      constants,
      expectedProfileBytes) match {
      case Right(value) => value
      case Left(reason) =>
        throw new IllegalStateException("frozen profile package rejected: " + reason)
    }
    require(
      java.util.Arrays.equals(loaded.profileId, expectedProfileBytes),
      "loaded profile identity changed")

    Fixture(
      loaded.verifier,
      ProofFixture(rawSeal, expectedClaim),
      ProofFixture(independentRawSeal, independentExpectedClaim),
      resources)
  }

  private def buildScenarios(fixture: Fixture): Vector[Scenario] = {
    val validChunks = canonicalChunks(fixture.primary.rawSeal)
    val independentValidChunks = canonicalChunks(fixture.independent.rawSeal)
    val wrongClaim = fixture.primary.expectedClaim.clone()
    wrongClaim(0) = (wrongClaim(0) ^ 1).toByte

    val lateMutation = fixture.primary.rawSeal.clone()
    val mutationOffset = (RawSealV1Decoder.WordCount - 1) * 4
    lateMutation(mutationOffset) = (lateMutation(mutationOffset) ^ 1).toByte
    val lateMutationChunks = canonicalChunks(lateMutation)

    val earlyCanonicalMutation = fixture.primary.rawSeal.clone()
    earlyCanonicalMutation(132) = (earlyCanonicalMutation(132) ^ 1).toByte
    val earlyCanonicalMutationChunks = canonicalChunks(earlyCanonicalMutation)
    require(
      RawSealV1Decoder.decode(earlyCanonicalMutationChunks).isRight,
      "early cryptographic mutation is not a canonical raw seal")

    val earlyRejectedChunks = Array(
      java.util.Arrays.copyOfRange(fixture.primary.rawSeal, 0, 65534),
      java.util.Arrays.copyOfRange(fixture.primary.rawSeal, 65534, 131070),
      java.util.Arrays.copyOfRange(fixture.primary.rawSeal, 131070, 196605),
      java.util.Arrays.copyOfRange(
        fixture.primary.rawSeal,
        196605,
        fixture.primary.rawSeal.length))

    Vector(
      Scenario(
        "valid-proof",
        "verified:1:15",
        FriVerifier.Queries,
        "verification-complete",
        "query",
        () => fixture.verifier.verify(validChunks, fixture.primary.expectedClaim),
        probe => fixture.verifier.verify(validChunks, fixture.primary.expectedClaim, probe)),
      Scenario(
        "early-transport-rejection",
        "raw-seal-transport-rejected",
        0,
        "transport-chunk-shape",
        "none",
        () => fixture.verifier.verify(earlyRejectedChunks, fixture.primary.expectedClaim),
        probe => fixture.verifier.verify(
          earlyRejectedChunks,
          fixture.primary.expectedClaim,
          probe)),
      Scenario(
        "early-canonical-cryptographic-rejection",
        "raw-seal-control-id-not-allowed",
        0,
        "terminal-control-allowlist",
        "group_root_code",
        () => fixture.verifier.verify(
          earlyCanonicalMutationChunks,
          fixture.primary.expectedClaim),
        probe => fixture.verifier.verify(
          earlyCanonicalMutationChunks,
          fixture.primary.expectedClaim,
          probe)),
      Scenario(
        "late-cryptographic-mutation",
        "raw-seal-malformed-proof",
        FriVerifier.Queries,
        "fri",
        "query",
        () => fixture.verifier.verify(lateMutationChunks, fixture.primary.expectedClaim),
        probe => fixture.verifier.verify(
          lateMutationChunks,
          fixture.primary.expectedClaim,
          probe)),
      Scenario(
        "late-claim-mismatch",
        "raw-seal-claim-mismatch",
        FriVerifier.Queries,
        "expected-claim-comparison",
        "query",
        () => fixture.verifier.verify(validChunks, wrongClaim),
        probe => fixture.verifier.verify(validChunks, wrongClaim, probe)),
      Scenario(
        "valid-independent-po2-16",
        "verified:1:16",
        FriVerifier.Queries,
        "verification-complete",
        "query",
        () => fixture.verifier.verify(
          independentValidChunks,
          fixture.independent.expectedClaim),
        probe => fixture.verifier.verify(
          independentValidChunks,
          fixture.independent.expectedClaim,
          probe)))
  }

  private def validateScenario(
      scenario: Scenario,
      observer: ExecutionObserver): ValidationResult = {
    val probe = new ValidationProbe
    observer.beforeValidationInvocation()
    val outcome = scenario.runWithProbe(probe)
    checkOutcome(scenario, outcome)
    if (probe.queries != scenario.expectedQueries) {
      throw new IllegalStateException(
        scenario.id + " reached " + probe.queries +
          " query checkpoints; expected " + scenario.expectedQueries)
    }
    val boundary = validationBoundary(outcome)
    if (boundary != scenario.expectedValidationBoundary) {
      throw new IllegalStateException(
        scenario.id + " reached validation boundary " + boundary +
          "; expected " + scenario.expectedValidationBoundary)
    }
    if (probe.lastCheckpoint != scenario.expectedLastCheckpoint) {
      throw new IllegalStateException(
        scenario.id + " last verifier checkpoint was " + probe.lastCheckpoint +
          "; expected " + scenario.expectedLastCheckpoint)
    }
    ValidationResult(probe.queries, boundary, probe.lastCheckpoint)
  }

  private def validationBoundary(outcome: Either[Failure, Verified]): String = outcome match {
    case Right(_) => "verification-complete"
    case Left(TransportRejected(_: RawSealV1Decoder.WrongChunkLength)) =>
      "transport-chunk-shape"
    case Left(ControlIdNotAllowed) => "terminal-control-allowlist"
    case Left(MalformedProof(stage, _)) => stage
    case Left(ClaimMismatch) => "expected-claim-comparison"
    case Left(other) =>
      throw new IllegalStateException(
        "unclassified validation failure: " + other.code)
  }

  private def warmUp(
      scenarios: Vector[Scenario],
      rounds: Int,
      observer: ExecutionObserver): Unit = {
    var round = 0
    while (round < rounds) {
      runRotated(scenarios, round) { scenario =>
        observer.beforeWarmupInvocation()
        checkOutcome(scenario, scenario.run())
      }
      round += 1
    }
  }

  private def measure(
      scenarios: Vector[Scenario],
      rounds: Int,
      allocationMeter: ThreadAllocationMeter,
      memoryPools: MemoryPoolTopology,
      memoryPoolSource: MemoryPoolSource,
      observer: ExecutionObserver): Measurements = {
    val timingSamples = Array.fill(scenarios.length)(new Array[Long](rounds))
    val allocationSamples = Array.fill(scenarios.length)(new Array[Long](rounds))
    val measured = captureMemoryPoolPhaseEnvelope(memoryPools, memoryPoolSource) {
      val gcBefore = garbageCollectorSnapshot()
      var round = 0
      while (round < rounds) {
        runRotated(scenarios, round) { scenario =>
          observer.beforeTimedInvocation()
          val allocatedBefore = allocationMeter.read()
          val started = System.nanoTime()
          val outcome = scenario.run()
          val elapsed = System.nanoTime() - started
          val allocatedAfter = allocationMeter.read()
          checkOutcome(scenario, outcome)
          val scenarioIndex = scenarios.indexWhere(_.id == scenario.id)
          timingSamples(scenarioIndex)(round) = elapsed
          allocationSamples(scenarioIndex)(round) = allocatedBytesDelta(
            allocatedBefore,
            allocatedAfter) match {
            case Right(value) => value
            case Left(detail) => throw new IllegalStateException(detail)
          }
        }
        round += 1
      }
      val gcAfter = garbageCollectorSnapshot()
      garbageCollectorDeltas(gcBefore, gcAfter) match {
        case Right(value) => value
        case Left(detail) => throw new IllegalStateException(detail)
      }
    }
    Measurements(timingSamples, allocationSamples, measured._1, measured._2)
  }

  private[benchmark] def openMemoryPoolTopology(
      source: MemoryPoolSource): MemoryPoolTopology = {
    if (source == null) throw new IllegalStateException("memory pool source is null")
    val handles = try source.handles()
    catch {
      case NonFatal(error) =>
        throw new IllegalStateException("memory pool topology could not be read", error)
    }
    if (handles == null) throw new IllegalStateException("memory pool topology is null")
    if (handles.isEmpty) throw new IllegalStateException("memory pool topology is empty")
    if (handles.exists(_ == null))
      throw new IllegalStateException("memory pool topology contains a null handle")

    val paired = handles.zipWithIndex.map { case (handle, index) =>
      val identity = try handle.identity
      catch {
        case NonFatal(error) =>
          throw new IllegalStateException(
            "memory pool identity at index " + index + " could not be read",
            error)
      }
      validateMemoryPoolIdentities(Vector(identity)) match {
        case Left(detail) => throw new IllegalStateException(detail)
        case Right(_) =>
      }
      requireMemoryPoolValid(handle, identity)
      (identity, handle)
    }.sortBy { case (identity, _) => (identity.name, identity.memoryType) }
    val identities = paired.map(_._1)
    validateMemoryPoolIdentities(identities) match {
      case Left(detail) => throw new IllegalStateException(detail)
      case Right(_) =>
    }
    MemoryPoolTopology(paired.map(_._2), identities)
  }

  private[benchmark] def captureMemoryPoolPhaseEnvelope[A](
      topology: MemoryPoolTopology,
      source: MemoryPoolSource)(
      sampling: => A): (A, Vector[MemoryPoolPhaseEnvelope]) =
    MemoryPoolMeasurementLock.synchronized {
    if (topology == null) throw new IllegalStateException("memory pool topology is null")
    if (topology.handles == null || topology.identities == null ||
        topology.handles.length != topology.identities.length)
      throw new IllegalStateException("memory pool topology is inconsistent")
    validateMemoryPoolIdentities(topology.identities) match {
      case Left(detail) => throw new IllegalStateException(detail)
      case Right(_) =>
    }

    val preResetTopology = openMemoryPoolTopology(source)
    if (preResetTopology.identities != topology.identities)
      throw new IllegalStateException("memory pool topology changed before peak reset")

    var i = 0
    while (i < topology.handles.length) {
      resetMemoryPoolPeak(topology.handles(i), topology.identities(i))
      i += 1
    }
    val afterResetPeakUsage = topology.handles.indices.map { index =>
      readMemoryPoolUsage(
        topology.handles(index),
        topology.identities(index),
        peak = true,
        phase = "after-reset peak usage")
    }.toVector

    val result = sampling

    val endUsage = topology.handles.indices.map { index =>
      readMemoryPoolUsage(
        topology.handles(index),
        topology.identities(index),
        peak = false,
        phase = "end usage")
    }.toVector
    val finalPeakUsage = topology.handles.indices.map { index =>
      readMemoryPoolUsage(
        topology.handles(index),
        topology.identities(index),
        peak = true,
        phase = "final peak usage")
    }.toVector
    val finalTopology = openMemoryPoolTopology(source)
    if (finalTopology.identities != topology.identities)
      throw new IllegalStateException("memory pool topology changed during sampling")

    val envelopes = topology.identities.indices.map { index =>
      MemoryPoolPhaseEnvelope(
        topology.identities(index),
        afterResetPeakUsage(index),
        endUsage(index),
        finalPeakUsage(index))
    }.toVector
    validateMemoryPoolPhaseEnvelopes(topology.identities, envelopes) match {
      case Left(detail) => throw new IllegalStateException(detail)
      case Right(_) =>
    }
      (result, envelopes)
    }

  private def resetMemoryPoolPeak(
      handle: MemoryPoolHandle,
      identity: MemoryPoolIdentity): Unit = {
    requireMemoryPoolValid(handle, identity)
    try handle.resetPeakUsage()
    catch {
      case NonFatal(error) =>
        throw new IllegalStateException(
          "memory pool " + identity.name + " peak usage could not be reset",
          error)
    }
  }

  private def readMemoryPoolUsage(
      handle: MemoryPoolHandle,
      identity: MemoryPoolIdentity,
      peak: Boolean,
      phase: String): MemoryUsageEvidence = {
    requireMemoryPoolValid(handle, identity)
    val usage = try {
      if (peak) handle.peakUsage() else handle.usage()
    } catch {
      case NonFatal(error) =>
        throw new IllegalStateException(
          "memory pool " + identity.name + " " + phase + " could not be read",
          error)
    }
    validateMemoryUsageEvidence(usage, "memory pool " + identity.name + " " + phase) match {
      case Left(detail) => throw new IllegalStateException(detail)
      case Right(_) => usage
    }
  }

  private def requireMemoryPoolValid(
      handle: MemoryPoolHandle,
      identity: MemoryPoolIdentity): Unit = {
    val valid = try handle.isValid
    catch {
      case NonFatal(error) =>
        throw new IllegalStateException(
          "memory pool " + identity.name + " validity could not be read",
          error)
    }
    if (!valid) throw new IllegalStateException("memory pool " + identity.name + " is invalid")
  }

  private def memoryUsageEvidence(usage: MemoryUsage): MemoryUsageEvidence =
    if (usage == null) null
    else MemoryUsageEvidence(usage.getUsed, usage.getCommitted, usage.getMax)

  private def runRotated(
      scenarios: Vector[Scenario],
      round: Int)(
      action: Scenario => Unit): Unit = {
    val start = round % scenarios.length
    var offset = 0
    while (offset < scenarios.length) {
      action(scenarios((start + offset) % scenarios.length))
      offset += 1
    }
  }

  private def checkOutcome(
      scenario: Scenario,
      outcome: Either[Failure, Verified]): Unit = {
    val rendered = outcome match {
      case Right(value) => "verified:" + value.controlKind + ":" + value.controlParameter
      case Left(failure) => failure.code
    }
    blackhole = blackhole ^ rendered.hashCode
    if (rendered != scenario.expectedOutcome) {
      throw new IllegalStateException(
        scenario.id + " returned " + rendered + "; expected " + scenario.expectedOutcome)
    }
  }

  private def canonicalChunks(bytes: Array[Byte]): Array[Array[Byte]] = {
    val chunks = new Array[Array[Byte]](ChunkLengths.length)
    var offset = 0
    var i = 0
    while (i < chunks.length) {
      chunks(i) = java.util.Arrays.copyOfRange(bytes, offset, offset + ChunkLengths(i))
      offset += ChunkLengths(i)
      i += 1
    }
    chunks
  }

  private def metadata(id: String, path: String, bytes: Array[Byte]): ResourceMetadata =
    ResourceMetadata(id, "classpath:" + path, bytes.length, sha256Hex(bytes))

  private def resourceBytes(path: String): Array[Byte] = {
    val in = getClass.getResourceAsStream(path)
    require(in != null, "missing benchmark resource " + path)
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

  private def decodeHex(value: String): Array[Byte] = {
    require((value.length & 1) == 0, "hex value must have even length")
    value.grouped(2).map(Integer.parseInt(_, 16).toByte).toArray
  }

  private def openThreadAllocationMeter(): ThreadAllocationMeter = {
    val platformBean = ManagementFactory.getThreadMXBean
    val bean = platformBean match {
      case value: com.sun.management.ThreadMXBean => value
      case _ =>
        throw new IllegalStateException(
          "current JVM does not expose com.sun.management.ThreadMXBean")
    }
    if (!bean.isThreadAllocatedMemorySupported)
      throw new IllegalStateException("current JVM does not support thread allocation counters")
    if (!bean.isThreadAllocatedMemoryEnabled) {
      try bean.setThreadAllocatedMemoryEnabled(true)
      catch {
        case error: SecurityException =>
          throw new IllegalStateException(
            "thread allocation counters are disabled and cannot be enabled",
            error)
      }
    }
    if (!bean.isThreadAllocatedMemoryEnabled)
      throw new IllegalStateException("thread allocation counters remain disabled")
    val meter = new ThreadAllocationMeter(bean, Thread.currentThread().getId)
    meter.read()
    meter
  }

  private def garbageCollectorSnapshot(): Vector[GarbageCollectorSnapshot] =
    ManagementFactory.getGarbageCollectorMXBeans.asScala
      .map(bean => GarbageCollectorSnapshot(
        bean.getName,
        bean.getCollectionCount,
        bean.getCollectionTime))
      .toVector
      .sortBy(_.name)

  private def environmentMetadata(
      config: Config,
      threadAllocationMeter: String,
      memoryPoolIdentities: Vector[MemoryPoolIdentity]): EnvironmentMetadata = {
    val runtimeBean = ManagementFactory.getRuntimeMXBean
    val compilationBean = ManagementFactory.getCompilationMXBean
    val inputArgumentsIdentity = jvmInputArgumentsIdentity(
      runtimeBean.getInputArguments.asScala.toVector) match {
      case Right(value) => value
      case Left(detail) => throw new IllegalStateException(detail)
    }
    val (cpuModel, cpuModelSource) = detectCpuModel(config.declaredCpuModel)
    EnvironmentMetadata(
      javaRuntimeName = property("java.runtime.name"),
      javaRuntimeVersion = property("java.runtime.version"),
      javaVmName = runtimeBean.getVmName,
      javaVmVendor = runtimeBean.getVmVendor,
      javaVmVersion = runtimeBean.getVmVersion,
      javaVmInfo = property("java.vm.info"),
      scalaVersion = Properties.versionNumberString,
      osName = property("os.name"),
      osVersion = property("os.version"),
      osArch = property("os.arch"),
      availableProcessors = Runtime.getRuntime.availableProcessors(),
      maxHeapBytes = Runtime.getRuntime.maxMemory(),
      jitCompiler = if (compilationBean == null) "unavailable" else compilationBean.getName,
      garbageCollectors = ManagementFactory.getGarbageCollectorMXBeans.asScala
        .map(_.getName).toVector.sorted,
      memoryPoolIdentities = memoryPoolIdentities,
      threadAllocationMeter = threadAllocationMeter,
      jvmInputArgumentCount = inputArgumentsIdentity.argumentCount,
      jvmInputArgumentsSha256 = inputArgumentsIdentity.argumentsSha256,
      cpuModel = cpuModel,
      cpuModelSource = cpuModelSource)
  }

  private def detectCpuModel(declared: Option[String]): (String, String) = declared match {
    case Some(value) => (value, "--cpu-model")
    case None =>
      Option(System.getenv("PROCESSOR_IDENTIFIER")).map(_.trim).filter(_.nonEmpty) match {
        case Some(value) => (value, "PROCESSOR_IDENTIFIER")
        case None =>
          val procCpuInfo = Paths.get("/proc/cpuinfo")
          if (Files.isRegularFile(procCpuInfo)) {
            val source = Source.fromFile(procCpuInfo.toFile, "UTF-8")
            try {
              source.getLines().collectFirst {
                case line if line.startsWith("model name") && line.contains(":") =>
                  line.substring(line.indexOf(':') + 1).trim
                case line if line.startsWith("Hardware") && line.contains(":") =>
                  line.substring(line.indexOf(':') + 1).trim
              }.filter(_.nonEmpty) match {
                case Some(value) => (value, "/proc/cpuinfo")
                case None        => ("unspecified", "unavailable")
              }
            } finally source.close()
          } else ("unspecified", "unavailable")
      }
  }

  private def property(name: String): String =
    Option(System.getProperty(name)).getOrElse("unavailable")
}
