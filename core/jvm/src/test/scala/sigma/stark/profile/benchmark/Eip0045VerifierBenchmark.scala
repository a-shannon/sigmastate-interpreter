/*
 * SPDX-License-Identifier: MIT AND Apache-2.0
 *
 * Copyright 2026 A. Shannon.
 */
package sigma.stark.profile.benchmark

import java.io.{ByteArrayOutputStream, IOException}
import java.lang.management.ManagementFactory
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths, StandardOpenOption}
import java.time.Instant

import sigma.stark.FriVerifier
import sigma.stark.profile.{RawSealV1Decoder, Risc0ProfilePackageLoader, Risc0RawSealVerifier}
import sigma.stark.profile.Risc0RawSealVerifier.{Failure, Probe, Verified}
import sigma.stark.profile.benchmark.Eip0045BenchmarkSupport._

import scala.collection.JavaConverters._
import scala.io.Source
import scala.util.Properties

/** Opt-in B5 evidence harness for the EIP-0045 stock-profile JVM verifier.
  *
  * Run this object explicitly with `coreJVM/Test/runMain`; it is deliberately
  * not a ScalaTest suite and therefore adds no work or timing noise to normal
  * tests. Each run authenticates the frozen B1/B2/B3 package through the
  * production loader, validates all four scenario paths, warms them in a
  * rotating schedule, then records one complete verifier invocation per
  * sample. It never derives or recommends a consensus fixedJit value.
  */
object Eip0045VerifierBenchmark {
  private val PackageRoot = "/stark-kats/eip0045-profile-package/"
  private val DirectRoot = "/stark-kats/eip0045-direct/"
  private val ExpectedProfileId =
    "23c4a123ffb33a1c8db89436fe0e7972bd8e4e289459ee5fd71be5440607d383"
  private val ExpectedSealSha256 =
    "088e6a306c7143f5a3e057924c42f63a6eb58dd3c30686a8ade5082fac4b386e"
  private val ExpectedClaimSha256 =
    "df9df2763693f97b85acd9d3cda4b13e2421b3dc052a6f91ab995c89ae75ee3c"
  private val ChunkLengths = Array(65535, 65535, 65535, 26063)

  @volatile private var blackhole: Int = 0

  private final class QueryProbe extends Probe {
    var queries: Int = 0
    override def onCheckpoint(label: String, _values: Array[Int]): Unit =
      if (label == "query") queries += 1
  }

  private final case class Scenario(
      id: String,
      expectedOutcome: String,
      expectedQueries: Int,
      run: () => Either[Failure, Verified],
      runWithProbe: Probe => Either[Failure, Verified])

  private final case class Fixture(
      verifier: Risc0RawSealVerifier,
      rawSeal: Array[Byte],
      expectedClaim: Array[Byte],
      resources: Vector[ResourceMetadata])

  private final case class Measurements(
      timingSamples: Array[Array[Long]],
      allocationSamples: Array[Array[Long]],
      garbageCollectorDeltas: Vector[GarbageCollectorDelta])

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

  def main(args: Array[String]): Unit = {
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

    val campaignBinding = loadCampaignBinding(config)
    val fixture = loadFixture()
    val scenarios = buildScenarios(fixture)
    val allocationMeter = openThreadAllocationMeter()
    val environment = environmentMetadata(config, allocationMeter.description)
    val startedAt = Instant.now().toString
    val runStarted = System.nanoTime()

    val validationQueries = scenarios.map(validateScenario)
    warmUp(scenarios, config.warmupRounds)
    val measurements = measure(scenarios, config.sampleRounds, allocationMeter)

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
        validationQueries(i),
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
      limitations = Vector(
        "This run measures one JVM process on one host and cannot close B5 by itself.",
        "The evidence digest binds content but is not an operator signature or execution attestation.",
        "The harness does not choose, infer, or recommend a consensus fixedJit value.",
        "Profile loading, ErgoTree preflight, transaction parsing, and node admission are outside the timed and allocation scope.",
        "Allocation samples cover only the current benchmark thread; process-wide or native allocations are outside their scope.",
        "Garbage-collector deltas are process-wide observations and cannot be attributed to one scenario.",
        "Peak live memory and the complete GC pause/resource envelope are not measured and remain separate B5 obligations.",
        "The JVM input-argument digest binds ordered RuntimeMXBean strings but does not disclose or interpret them.",
        "CPU scheduling, frequency scaling, thermal state, and concurrent host load are not controlled by the harness.") ++
        (campaignBinding match {
          case Some(_) => Vector(
            "Campaign binding content-binds manifest bytes and a run ID but does not validate manifest semantics, run membership, or campaign policy compliance.")
          case None => Vector(
            "No campaign manifest or run ID is bound, so this diagnostic is not acceptable campaign evidence.")
        }) ++
        (if (config.implementationRevision == "unrecorded")
          Vector("implementationRevision is unrecorded, so this run is not acceptable campaign evidence.")
        else Vector.empty))
    val json = renderEnvelope(payload)

    config.outputPath match {
      case Some(pathText) =>
        val path = Paths.get(pathText)
        val parent = path.toAbsolutePath.normalize().getParent
        if (parent != null && !Files.isDirectory(parent))
          throw new IllegalArgumentException("output parent directory does not exist: " + parent)
        Files.write(
          path,
          json.getBytes(StandardCharsets.UTF_8),
          StandardOpenOption.CREATE_NEW,
          StandardOpenOption.WRITE)
        System.err.println("wrote EIP-0045 benchmark evidence to " + path.toAbsolutePath.normalize())
      case None =>
        System.out.print(json)
    }

    // Force the verification outcomes to remain observable across the whole
    // run even under an aggressively optimizing JVM.
    if (blackhole == Int.MinValue) System.err.println("blackhole=" + blackhole)
  }

  private def loadCampaignBinding(config: Config): Option[CampaignBinding] =
    (config.campaignManifestPath, config.campaignRunId) match {
      case (None, None) => None
      case (Some(pathText), Some(runId)) =>
        val bytes = readBoundedCampaignManifest(pathText)
        campaignBindingFromBytes(runId, bytes) match {
          case Right(value) => Some(value)
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

  private def loadFixture(): Fixture = {
    val algorithm = resourceBytes(PackageRoot + "algorithm.txt")
    val constants = resourceBytes(PackageRoot + "constants.bin")
    val manifest = resourceBytes(PackageRoot + "manifest.bin")
    val profileIdResource = resourceBytes(PackageRoot + "profile-id.bin")
    val rawSeal = resourceBytes(DirectRoot + "po2-15-raw-seal.bin")
    val expectedClaim = resourceBytes(DirectRoot + "po2-15-claim-digest.bin")
    val fixtureManifest = resourceBytes(DirectRoot + "fixture-manifest.json")
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

    val resources = Vector(
      metadata("profile-algorithm", PackageRoot + "algorithm.txt", algorithm),
      metadata("profile-constants", PackageRoot + "constants.bin", constants),
      metadata("profile-manifest", PackageRoot + "manifest.bin", manifest),
      metadata("profile-id", PackageRoot + "profile-id.bin", profileIdResource),
      metadata("raw-seal", DirectRoot + "po2-15-raw-seal.bin", rawSeal),
      metadata("claim-digest", DirectRoot + "po2-15-claim-digest.bin", expectedClaim),
      metadata("fixture-manifest", DirectRoot + "fixture-manifest.json", fixtureManifest))
    Fixture(loaded.verifier, rawSeal, expectedClaim, resources)
  }

  private def buildScenarios(fixture: Fixture): Vector[Scenario] = {
    val validChunks = canonicalChunks(fixture.rawSeal)
    val wrongClaim = fixture.expectedClaim.clone()
    wrongClaim(0) = (wrongClaim(0) ^ 1).toByte

    val lateMutation = fixture.rawSeal.clone()
    val mutationOffset = (RawSealV1Decoder.WordCount - 1) * 4
    lateMutation(mutationOffset) = (lateMutation(mutationOffset) ^ 1).toByte
    val lateMutationChunks = canonicalChunks(lateMutation)

    val earlyRejectedChunks = Array(
      java.util.Arrays.copyOfRange(fixture.rawSeal, 0, 65534),
      java.util.Arrays.copyOfRange(fixture.rawSeal, 65534, 131070),
      java.util.Arrays.copyOfRange(fixture.rawSeal, 131070, 196605),
      java.util.Arrays.copyOfRange(fixture.rawSeal, 196605, fixture.rawSeal.length))

    Vector(
      Scenario(
        "valid-proof",
        "verified:1:15",
        FriVerifier.Queries,
        () => fixture.verifier.verify(validChunks, fixture.expectedClaim),
        probe => fixture.verifier.verify(validChunks, fixture.expectedClaim, probe)),
      Scenario(
        "late-claim-mismatch",
        "raw-seal-claim-mismatch",
        FriVerifier.Queries,
        () => fixture.verifier.verify(validChunks, wrongClaim),
        probe => fixture.verifier.verify(validChunks, wrongClaim, probe)),
      Scenario(
        "late-cryptographic-mutation",
        "raw-seal-malformed-proof",
        FriVerifier.Queries,
        () => fixture.verifier.verify(lateMutationChunks, fixture.expectedClaim),
        probe => fixture.verifier.verify(lateMutationChunks, fixture.expectedClaim, probe)),
      Scenario(
        "early-transport-rejection",
        "raw-seal-transport-rejected",
        0,
        () => fixture.verifier.verify(earlyRejectedChunks, fixture.expectedClaim),
        probe => fixture.verifier.verify(earlyRejectedChunks, fixture.expectedClaim, probe)))
  }

  private def validateScenario(scenario: Scenario): Int = {
    val probe = new QueryProbe
    val outcome = scenario.runWithProbe(probe)
    checkOutcome(scenario, outcome)
    if (probe.queries != scenario.expectedQueries) {
      throw new IllegalStateException(
        scenario.id + " reached " + probe.queries +
          " query checkpoints; expected " + scenario.expectedQueries)
    }
    probe.queries
  }

  private def warmUp(scenarios: Vector[Scenario], rounds: Int): Unit = {
    var round = 0
    while (round < rounds) {
      runRotated(scenarios, round) { scenario =>
        checkOutcome(scenario, scenario.run())
      }
      round += 1
    }
  }

  private def measure(
      scenarios: Vector[Scenario],
      rounds: Int,
      allocationMeter: ThreadAllocationMeter): Measurements = {
    val timingSamples = Array.fill(scenarios.length)(new Array[Long](rounds))
    val allocationSamples = Array.fill(scenarios.length)(new Array[Long](rounds))
    val gcBefore = garbageCollectorSnapshot()
    var round = 0
    while (round < rounds) {
      runRotated(scenarios, round) { scenario =>
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
    val gcDelta = garbageCollectorDeltas(gcBefore, gcAfter) match {
      case Right(value) => value
      case Left(detail) => throw new IllegalStateException(detail)
    }
    Measurements(timingSamples, allocationSamples, gcDelta)
  }

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
      threadAllocationMeter: String): EnvironmentMetadata = {
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
