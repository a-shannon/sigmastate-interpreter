/*
 * SPDX-License-Identifier: MIT AND Apache-2.0
 *
 * Copyright 2026 A. Shannon.
 */
package sigma.stark.profile.benchmark

import java.nio.charset.StandardCharsets
import java.security.MessageDigest

/** Deterministic, dependency-free model and encoder for EIP-0045 B5 timing
  * evidence. It lives in JVM test sources so it cannot enter consensus jars or
  * the normal test run unless a focused support test explicitly exercises it.
  */
private[benchmark] object Eip0045BenchmarkSupport {
  final val Schema: String = "eip-0045-jvm-verifier-benchmark-v1"
  final val DigestAlgorithm: String = "SHA-256"
  final val DigestDomain: String = "Ergo.EIP0045.B5.Evidence.v1"
  final val Canonicalization: String = "utf8-fixed-field-order-no-whitespace-v1"
  final val DefaultWarmupRounds: Int = 15
  final val DefaultSampleRounds: Int = 100
  final val MaxWarmupRounds: Int = 10000
  final val MaxSampleRounds: Int = 10000

  final case class Config(
      warmupRounds: Int,
      sampleRounds: Int,
      outputPath: Option[String],
      declaredCpuModel: Option[String],
      implementationRevision: String)

  final case class ResourceMetadata(
      id: String,
      classpath: String,
      byteLength: Int,
      sha256: String)

  final case class EnvironmentMetadata(
      javaRuntimeName: String,
      javaRuntimeVersion: String,
      javaVmName: String,
      javaVmVendor: String,
      javaVmVersion: String,
      javaVmInfo: String,
      scalaVersion: String,
      osName: String,
      osVersion: String,
      osArch: String,
      availableProcessors: Int,
      maxHeapBytes: Long,
      jitCompiler: String,
      garbageCollectors: Vector[String],
      cpuModel: String,
      cpuModelSource: String)

  final case class TimingStatistics(
      sampleCount: Int,
      p50Ns: Long,
      p95Ns: Long,
      p99Ns: Long,
      maxNs: Long)

  final case class ScenarioEvidence(
      id: String,
      expectedOutcome: String,
      validationQueryCheckpoints: Int,
      samplesNs: Vector[Long],
      statistics: TimingStatistics)

  final case class EvidencePayload(
      startedAtUtc: String,
      benchmarkDurationNs: Long,
      profileId: String,
      implementationRevision: String,
      verifierEntryPoint: String,
      resources: Vector[ResourceMetadata],
      warmupRounds: Int,
      sampleRounds: Int,
      environment: EnvironmentMetadata,
      scenarios: Vector[ScenarioEvidence],
      limitations: Vector[String])

  val Usage: String =
    """EIP-0045 JVM verifier benchmark (opt-in; never run by the test suite)
      |Usage: Eip0045VerifierBenchmark [options]
      |  --warmup-rounds N   Complete round-robin warmup rounds (default: 15)
      |  --sample-rounds N   Timed samples per scenario (default: 100)
      |  --output FILE       Write one UTF-8 JSON evidence file; refuses overwrite
      |  --cpu-model TEXT    Explicit public CPU description for cross-host evidence
      |  --implementation-revision TEXT
      |                      Exact public commit or source-tree digest (default: unrecorded)
      |  --help              Show this help
      |""".stripMargin

  def parseArgs(args: Array[String]): Either[String, Config] = {
    if (args == null) return Left("argument array is null")

    var warmupRounds = DefaultWarmupRounds
    var sampleRounds = DefaultSampleRounds
    var outputPath: Option[String] = None
    var cpuModel: Option[String] = None
    var implementationRevision = "unrecorded"
    var seenWarmup = false
    var seenSamples = false
    var seenOutput = false
    var seenCpu = false
    var seenRevision = false
    var i = 0
    while (i < args.length) {
      val option = args(i)
      if (option == null) return Left("argument at index " + i + " is null")
      option match {
        case "--warmup-rounds" =>
          if (seenWarmup) return Left("duplicate option --warmup-rounds")
          val value = nextValue(args, i, option) match {
            case Right(v) => v
            case Left(e)  => return Left(e)
          }
          parseBoundedNonNegativeInt(option, value, MaxWarmupRounds) match {
            case Right(v) => warmupRounds = v
            case Left(e)  => return Left(e)
          }
          seenWarmup = true
          i += 2
        case "--sample-rounds" =>
          if (seenSamples) return Left("duplicate option --sample-rounds")
          val value = nextValue(args, i, option) match {
            case Right(v) => v
            case Left(e)  => return Left(e)
          }
          parseBoundedPositiveInt(option, value, MaxSampleRounds) match {
            case Right(v) => sampleRounds = v
            case Left(e)  => return Left(e)
          }
          seenSamples = true
          i += 2
        case "--output" =>
          if (seenOutput) return Left("duplicate option --output")
          val value = nextValue(args, i, option) match {
            case Right(v) => v
            case Left(e)  => return Left(e)
          }
          if (value.trim.isEmpty) return Left("--output must not be empty")
          outputPath = Some(value)
          seenOutput = true
          i += 2
        case "--cpu-model" =>
          if (seenCpu) return Left("duplicate option --cpu-model")
          val value = nextValue(args, i, option) match {
            case Right(v) => v
            case Left(e)  => return Left(e)
          }
          val normalized = value.trim
          if (normalized.isEmpty) return Left("--cpu-model must not be empty")
          if (normalized.length > 256)
            return Left("--cpu-model must be at most 256 characters")
          if (normalized.exists(ch => ch < ' '))
            return Left("--cpu-model must not contain control characters")
          cpuModel = Some(normalized)
          seenCpu = true
          i += 2
        case "--implementation-revision" =>
          if (seenRevision) return Left("duplicate option --implementation-revision")
          val value = nextValue(args, i, option) match {
            case Right(v) => v
            case Left(e)  => return Left(e)
          }
          val normalized = value.trim
          if (normalized.isEmpty)
            return Left("--implementation-revision must not be empty")
          if (normalized.length > 256)
            return Left("--implementation-revision must be at most 256 characters")
          if (normalized.exists(ch => ch < ' '))
            return Left("--implementation-revision must not contain control characters")
          implementationRevision = normalized
          seenRevision = true
          i += 2
        case "--help" =>
          return Left("--help must be handled before argument parsing")
        case unknown =>
          return Left("unknown option " + unknown)
      }
    }
    Right(Config(
      warmupRounds,
      sampleRounds,
      outputPath,
      cpuModel,
      implementationRevision))
  }

  private def nextValue(
      args: Array[String],
      optionIndex: Int,
      option: String): Either[String, String] = {
    val valueIndex = optionIndex + 1
    if (valueIndex >= args.length) Left("missing value for " + option)
    else if (args(valueIndex) == null) Left("null value for " + option)
    else Right(args(valueIndex))
  }

  private def parseBoundedNonNegativeInt(
      option: String,
      value: String,
      maximum: Int): Either[String, Int] = {
    parseInt(option, value) match {
      case Right(parsed) if parsed >= 0 && parsed <= maximum => Right(parsed)
      case Right(parsed) if parsed > maximum => Left(option + " must be at most " + maximum)
      case Right(_) => Left(option + " must be non-negative")
      case Left(e)  => Left(e)
    }
  }

  private def parseBoundedPositiveInt(
      option: String,
      value: String,
      maximum: Int): Either[String, Int] = {
    parseInt(option, value) match {
      case Right(parsed) if parsed > 0 && parsed <= maximum => Right(parsed)
      case Right(parsed) if parsed > maximum => Left(option + " must be at most " + maximum)
      case Right(_) => Left(option + " must be positive")
      case Left(e)  => Left(e)
    }
  }

  private def parseInt(option: String, value: String): Either[String, Int] = {
    try Right(value.toInt)
    catch {
      case _: NumberFormatException => Left(option + " must be a base-10 32-bit integer")
    }
  }

  /** Nearest-rank percentiles. Raw samples remain in the evidence so every
    * summary can be independently recomputed.
    */
  def statistics(samples: Seq[Long]): Either[String, TimingStatistics] = {
    if (samples == null) return Left("samples are null")
    if (samples.isEmpty) return Left("samples are empty")
    if (samples.exists(_ < 0L)) return Left("samples contain a negative duration")
    val sorted = samples.sorted
    Right(TimingStatistics(
      sorted.length,
      nearestRank(sorted, 50),
      nearestRank(sorted, 95),
      nearestRank(sorted, 99),
      sorted.last))
  }

  private def nearestRank(sorted: Seq[Long], percentile: Int): Long = {
    val numerator = sorted.length.toLong * percentile.toLong
    val oneBased = (numerator + 99L) / 100L
    sorted((oneBased - 1L).toInt)
  }

  def sha256Hex(bytes: Array[Byte]): String =
    hex(MessageDigest.getInstance(DigestAlgorithm).digest(bytes))

  def evidenceDigest(payloadJson: String): String = {
    val digest = MessageDigest.getInstance(DigestAlgorithm)
    digest.update(DigestDomain.getBytes(StandardCharsets.US_ASCII))
    digest.update(0.toByte)
    digest.update(payloadJson.getBytes(StandardCharsets.UTF_8))
    hex(digest.digest())
  }

  def renderEnvelope(payload: EvidencePayload): String = {
    val payloadJson = renderPayload(payload)
    val digest = evidenceDigest(payloadJson)
    val out = new StringBuilder(payloadJson.length + 320)
    out.append('{')
    field(out, "schema", Schema)
    out.append(',')
    field(out, "digestAlgorithm", DigestAlgorithm)
    out.append(',')
    field(out, "digestDomain", DigestDomain)
    out.append(',')
    field(out, "canonicalization", Canonicalization)
    out.append(',')
    field(out, "evidenceDigest", digest)
    out.append(',').append(quote("payload")).append(':').append(payloadJson)
    out.append('}').append('\n')
    out.toString()
  }

  private[benchmark] def renderPayload(payload: EvidencePayload): String = {
    val out = new StringBuilder(8192)
    out.append('{')
    field(out, "startedAtUtc", payload.startedAtUtc)
    out.append(',')
    numberField(out, "benchmarkDurationNs", payload.benchmarkDurationNs)
    out.append(',')
    field(out, "profileId", payload.profileId)
    out.append(',')
    field(out, "implementationRevision", payload.implementationRevision)
    out.append(',')
    field(out, "verifierEntryPoint", payload.verifierEntryPoint)
    out.append(',').append(quote("resources")).append(':')
    renderArray(out, payload.resources) { (builder, resource) =>
      builder.append('{')
      field(builder, "id", resource.id)
      builder.append(',')
      field(builder, "classpath", resource.classpath)
      builder.append(',')
      numberField(builder, "byteLength", resource.byteLength.toLong)
      builder.append(',')
      field(builder, "sha256", resource.sha256)
      builder.append('}')
    }
    out.append(',').append(quote("configuration")).append(':').append('{')
    numberField(out, "warmupRounds", payload.warmupRounds.toLong)
    out.append(',')
    numberField(out, "sampleRounds", payload.sampleRounds.toLong)
    out.append(',')
    field(out, "clock", "System.nanoTime")
    out.append(',')
    field(out, "schedule", "deterministic-round-robin-rotation")
    out.append(',')
    field(out, "percentileMethod", "nearest-rank")
    out.append(',')
    field(out, "timedScope", "Risc0RawSealVerifier.verify; fixture and profile loading excluded")
    out.append('}')
    out.append(',').append(quote("environment")).append(':')
    renderEnvironment(out, payload.environment)
    out.append(',').append(quote("scenarios")).append(':')
    renderArray(out, payload.scenarios) { (builder, scenario) =>
      builder.append('{')
      field(builder, "id", scenario.id)
      builder.append(',')
      field(builder, "expectedOutcome", scenario.expectedOutcome)
      builder.append(',')
      numberField(builder, "validationQueryCheckpoints", scenario.validationQueryCheckpoints.toLong)
      builder.append(',').append(quote("samplesNs")).append(':')
      renderLongArray(builder, scenario.samplesNs)
      builder.append(',').append(quote("statistics")).append(':').append('{')
      numberField(builder, "sampleCount", scenario.statistics.sampleCount.toLong)
      builder.append(',')
      numberField(builder, "p50Ns", scenario.statistics.p50Ns)
      builder.append(',')
      numberField(builder, "p95Ns", scenario.statistics.p95Ns)
      builder.append(',')
      numberField(builder, "p99Ns", scenario.statistics.p99Ns)
      builder.append(',')
      numberField(builder, "maxNs", scenario.statistics.maxNs)
      builder.append('}').append('}')
    }
    out.append(',').append(quote("limitations")).append(':')
    renderStringArray(out, payload.limitations)
    out.append('}')
    out.toString()
  }

  private def renderEnvironment(out: StringBuilder, environment: EnvironmentMetadata): Unit = {
    out.append('{')
    field(out, "javaRuntimeName", environment.javaRuntimeName)
    out.append(',')
    field(out, "javaRuntimeVersion", environment.javaRuntimeVersion)
    out.append(',')
    field(out, "javaVmName", environment.javaVmName)
    out.append(',')
    field(out, "javaVmVendor", environment.javaVmVendor)
    out.append(',')
    field(out, "javaVmVersion", environment.javaVmVersion)
    out.append(',')
    field(out, "javaVmInfo", environment.javaVmInfo)
    out.append(',')
    field(out, "scalaVersion", environment.scalaVersion)
    out.append(',')
    field(out, "osName", environment.osName)
    out.append(',')
    field(out, "osVersion", environment.osVersion)
    out.append(',')
    field(out, "osArch", environment.osArch)
    out.append(',')
    numberField(out, "availableProcessors", environment.availableProcessors.toLong)
    out.append(',')
    numberField(out, "maxHeapBytes", environment.maxHeapBytes)
    out.append(',')
    field(out, "jitCompiler", environment.jitCompiler)
    out.append(',').append(quote("garbageCollectors")).append(':')
    renderStringArray(out, environment.garbageCollectors)
    out.append(',')
    field(out, "cpuModel", environment.cpuModel)
    out.append(',')
    field(out, "cpuModelSource", environment.cpuModelSource)
    out.append('}')
  }

  private def renderLongArray(out: StringBuilder, values: Seq[Long]): Unit = {
    out.append('[')
    var i = 0
    while (i < values.length) {
      if (i > 0) out.append(',')
      out.append(values(i))
      i += 1
    }
    out.append(']')
  }

  private def renderStringArray(out: StringBuilder, values: Seq[String]): Unit = {
    out.append('[')
    var i = 0
    while (i < values.length) {
      if (i > 0) out.append(',')
      out.append(quote(values(i)))
      i += 1
    }
    out.append(']')
  }

  private def renderArray[A](
      out: StringBuilder,
      values: Seq[A])(
      render: (StringBuilder, A) => Unit): Unit = {
    out.append('[')
    var i = 0
    while (i < values.length) {
      if (i > 0) out.append(',')
      render(out, values(i))
      i += 1
    }
    out.append(']')
  }

  private def field(out: StringBuilder, name: String, value: String): Unit =
    out.append(quote(name)).append(':').append(quote(nullSafe(value)))

  private def numberField(out: StringBuilder, name: String, value: Long): Unit =
    out.append(quote(name)).append(':').append(value)

  private def nullSafe(value: String): String = if (value == null) "" else value

  private[benchmark] def quote(value: String): String = {
    val out = new StringBuilder(value.length + 2)
    out.append('"')
    var i = 0
    while (i < value.length) {
      value.charAt(i) match {
        case '"' => out.append("\\\"")
        case '\\' => out.append("\\\\")
        case '\b' => out.append("\\b")
        case '\f' => out.append("\\f")
        case '\n' => out.append("\\n")
        case '\r' => out.append("\\r")
        case '\t' => out.append("\\t")
        case ch if ch < ' ' =>
          out.append("\\u")
          val rendered = Integer.toHexString(ch.toInt)
          var padding = rendered.length
          while (padding < 4) {
            out.append('0')
            padding += 1
          }
          out.append(rendered)
        case ch => out.append(ch)
      }
      i += 1
    }
    out.append('"')
    out.toString()
  }

  private def hex(bytes: Array[Byte]): String = {
    val out = new StringBuilder(bytes.length * 2)
    var i = 0
    while (i < bytes.length) {
      out.append(String.format("%02x", Integer.valueOf(bytes(i) & 0xff)))
      i += 1
    }
    out.toString()
  }
}
