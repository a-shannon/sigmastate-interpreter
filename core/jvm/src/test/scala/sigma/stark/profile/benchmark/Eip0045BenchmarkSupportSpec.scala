/*
 * SPDX-License-Identifier: MIT AND Apache-2.0
 *
 * Copyright 2026 A. Shannon.
 */
package sigma.stark.profile.benchmark

import java.nio.charset.StandardCharsets
import java.nio.file.Files

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import sigma.stark.profile.benchmark.Eip0045BenchmarkSupport._

class Eip0045BenchmarkSupportSpec extends AnyFunSuite with Matchers {
  test("argument parsing is bounded, explicit, and deterministic") {
    parseArgs(Array.empty) shouldBe
      Right(Config(15, 100, None, None, "unrecorded", None, None))
    parseArgs(Array(
      "--sample-rounds", "7",
      "--warmup-rounds", "0",
      "--cpu-model", "Reference CPU",
      "--implementation-revision", "commit:0123456789abcdef",
      "--campaign-manifest", "campaign.json",
      "--campaign-run-id", "host-a:run-01",
      "--output", "evidence.json")) shouldBe
      Right(Config(
        0,
        7,
        Some("evidence.json"),
        Some("Reference CPU"),
        "commit:0123456789abcdef",
        Some("campaign.json"),
        Some("host-a:run-01")))

    parseArgs(Array("--sample-rounds", "0")) shouldBe
      Left("--sample-rounds must be positive")
    parseArgs(Array("--warmup-rounds", "-1")) shouldBe
      Left("--warmup-rounds must be non-negative")
    parseArgs(Array("--sample-rounds", "NaN")) shouldBe
      Left("--sample-rounds must be a base-10 32-bit integer")
    parseArgs(Array("--sample-rounds", "10001")) shouldBe
      Left("--sample-rounds must be at most 10000")
    parseArgs(Array("--warmup-rounds", "10001")) shouldBe
      Left("--warmup-rounds must be at most 10000")
    parseArgs(Array("--output")) shouldBe Left("missing value for --output")
    parseArgs(Array("--cpu-model", "x", "--cpu-model", "y")) shouldBe
      Left("duplicate option --cpu-model")
    parseArgs(Array("--implementation-revision", " ")) shouldBe
      Left("--implementation-revision must not be empty")
    parseArgs(Array("--implementation-revision", "x" * 257)) shouldBe
      Left("--implementation-revision must be at most 256 characters")
    parseArgs(Array("--implementation-revision", "commit:\n00")) shouldBe
      Left("--implementation-revision must not contain control characters")
    parseArgs(Array("--implementation-revision", "commit:\u007f00")) shouldBe
      Left("--implementation-revision must not contain control characters")
    parseArgs(Array("--campaign-manifest", "campaign.json")) shouldBe
      Left("--campaign-manifest and --campaign-run-id must be supplied together")
    parseArgs(Array("--campaign-run-id", "run-01")) shouldBe
      Left("--campaign-manifest and --campaign-run-id must be supplied together")
    parseArgs(Array(
      "--campaign-manifest", "campaign.json",
      "--campaign-run-id", "run-01")) shouldBe
      Left("campaign-bound runs require a recorded --implementation-revision")
    parseArgs(Array(
      "--implementation-revision", "commit:00",
      "--campaign-manifest", "campaign.json",
      "--campaign-run-id", "contains space")) shouldBe
      Left("--campaign-run-id must be 1-128 characters using only ASCII letters, digits, '.', '_', ':', or '-'")
    parseArgs(Array(
      "--implementation-revision", "commit:00",
      "--campaign-manifest", "campaign.json",
      "--campaign-manifest", "other.json")) shouldBe
      Left("duplicate option --campaign-manifest")
    parseArgs(Array(
      "--implementation-revision", "commit:00",
      "--campaign-manifest", "campaign.json",
      "--campaign-run-id", "run-01",
      "--campaign-run-id", "run-02")) shouldBe
      Left("duplicate option --campaign-run-id")
    parseArgs(Array("--unknown")) shouldBe Left("unknown option at argument index 0")
  }

  test("unknown benchmark options never echo secret-shaped or path-shaped tokens") {
    val secretShaped = "--unknown=C:\\private\\credential-token-marker"
    val result = parseArgs(Array(secretShaped))
    result shouldBe Left("unknown option at argument index 0")
    result.toString should not include secretShaped
    result.toString should not include "credential-token-marker"
  }

  test("campaign binding hashes exact bounded bytes without retaining a path") {
    val first = campaignBindingFromBytes("host-a:run-01", "manifest\n".getBytes(StandardCharsets.UTF_8))
    val changed = campaignBindingFromBytes("host-a:run-01", "manifesU\n".getBytes(StandardCharsets.UTF_8))
    first shouldBe Right(CampaignBinding(
      "host-a:run-01",
      9,
      "7021e610a5f62eefd01830fea68e5fa180e8cf017c08ea0890c326b2854ebc96"))
    changed should not be first
    changed match {
      case Right(value) => value.manifestByteLength shouldBe 9
      case Left(detail) => fail(detail)
    }
    campaignBindingFromBytes("bad run", Array[Byte](1)) shouldBe
      Left("campaign run ID is invalid")
    campaignBindingFromBytes("run-01", Array.empty[Byte]) shouldBe
      Left("campaign manifest is empty")
    campaignBindingFromBytes(
      "run-01",
      new Array[Byte](MaxCampaignManifestBytes + 1)) shouldBe
      Left("campaign manifest exceeds 1048576 bytes")
  }

  test("JVM input-argument identity binds order and element boundaries") {
    val identity = jvmInputArgumentsIdentity(Vector("-Xms4g", "-XX:+UseG1GC"))
    identity shouldBe Right(JvmInputArgumentsIdentity(
      2,
      "5c04a86bfc85463c5a6b66a6b0e51fb54d0c80cc09946b47ae03da88ce73bca3"))
    jvmInputArgumentsIdentity(Vector("-XX:+UseG1GC", "-Xms4g")) should not be identity
    jvmInputArgumentsIdentity(Vector("ab", "c")) should not be
      jvmInputArgumentsIdentity(Vector("a", "bc"))
    jvmInputArgumentsIdentity(Vector("ok", null)) shouldBe
      Left("JVM input argument at index 1 is null")
    jvmInputArgumentsIdentity(Vector.fill(MaxJvmInputArguments + 1)("")) shouldBe
      Left("JVM input argument count exceeds 1024")
    jvmInputArgumentsIdentity(Vector("x" * (MaxJvmInputArgumentBytes + 1))) shouldBe
      Left("JVM input argument at index 0 exceeds 65536 characters before UTF-8 encoding")
    jvmInputArgumentsIdentity(Vector("é" * 32769)) shouldBe
      Left("JVM input argument at index 0 exceeds 65536 UTF-8 bytes")
    jvmInputArgumentsIdentity(Vector.fill(17)("x" * MaxJvmInputArgumentBytes)) shouldBe
      Left("JVM input arguments exceed 1048576 total UTF-8 bytes")
    val unpairedSurrogate = new String(Array(0xd800.toChar))
    jvmInputArgumentsIdentity(Vector(unpairedSurrogate)) shouldBe
      Left("JVM input argument at index 0 is not valid Unicode")
  }

  test("nearest-rank p50 p95 p99 and max are reproducible from raw samples") {
    val samples = (1L to 100L).reverse
    statistics(samples) shouldBe Right(TimingStatistics(
      sampleCount = 100,
      p50Ns = 50,
      p95Ns = 95,
      p99Ns = 99,
      maxNs = 100))
    statistics(Seq(9L)) shouldBe Right(TimingStatistics(1, 9, 9, 9, 9))
    statistics(Seq.empty) shouldBe Left("samples are empty")
    statistics(Seq(1L, -1L)) shouldBe Left("samples contain a negative duration")
  }

  test("allocation summaries preserve raw samples and reject unavailable values") {
    allocationStatistics((1L to 100L).reverse) shouldBe Right(AllocationStatistics(
      sampleCount = 100,
      p50Bytes = 50,
      p95Bytes = 95,
      p99Bytes = 99,
      maxBytes = 100))
    allocationStatistics(Seq.empty) shouldBe Left("allocation samples are empty")
    allocationStatistics(Seq(1L, -1L)) shouldBe
      Left("allocation samples contain a negative value")

    allocatedBytesDelta(100L, 175L) shouldBe Right(75L)
    allocatedBytesDelta(-1L, 175L) shouldBe
      Left("thread allocation counter before sample is unavailable")
    allocatedBytesDelta(100L, -1L) shouldBe
      Left("thread allocation counter after sample is unavailable")
    allocatedBytesDelta(175L, 100L) shouldBe
      Left("thread allocation counter moved backwards")
  }

  test("garbage collector deltas fail closed on unsupported or unstable counters") {
    val before = Vector(
      GarbageCollectorSnapshot("old", 3, 20),
      GarbageCollectorSnapshot("young", 8, 11))
    val after = Vector(
      GarbageCollectorSnapshot("old", 4, 27),
      GarbageCollectorSnapshot("young", 10, 16))
    garbageCollectorDeltas(before, after) shouldBe Right(Vector(
      GarbageCollectorDelta("old", 1, 7),
      GarbageCollectorDelta("young", 2, 5)))

    garbageCollectorDeltas(
      before,
      after.reverse) shouldBe Left("garbage collector set or order changed during sampling")
    garbageCollectorDeltas(Vector.empty, Vector.empty) shouldBe
      Left("garbage collector snapshot is empty")
    garbageCollectorDeltas(
      Vector(GarbageCollectorSnapshot("old", -1, 20)),
      Vector(GarbageCollectorSnapshot("old", -1, 20))) shouldBe
      Left("garbage collector old does not expose collection counts")
    garbageCollectorDeltas(
      Vector(GarbageCollectorSnapshot("old", 4, -1)),
      Vector(GarbageCollectorSnapshot("old", 4, -1))) shouldBe
      Left("garbage collector old does not expose collection time")
    garbageCollectorDeltas(
      Vector(GarbageCollectorSnapshot("old", 4, 20)),
      Vector(GarbageCollectorSnapshot("old", 3, 21))) shouldBe
      Left("garbage collector old collection count moved backwards")
    garbageCollectorDeltas(
      Vector(GarbageCollectorSnapshot("old", 4, 20)),
      Vector(GarbageCollectorSnapshot("old", 5, 19))) shouldBe
      Left("garbage collector old collection time moved backwards")
  }

  test("JSON quoting is complete for evidence-controlled strings") {
    quote("a\"b\\c\n\t" + 1.toChar) shouldBe "\"a\\\"b\\\\c\\n\\t\\u0001\""
  }

  test("domain-separated evidence digest has an independent golden value") {
    evidenceDigest("{\"a\":1}") shouldBe
      "3ab4418ee6b3e716f02012b936bba5b4ee089ac5b39e9bd3c706730fcfe27eb0"
  }

  test("evidence envelope is canonical and binds raw samples and metadata") {
    val payload = samplePayload(Vector(10L, 20L))
    val rendered = renderEnvelope(payload)
    rendered should startWith("{\"schema\":\"eip-0045-jvm-verifier-benchmark-v3\"")
    rendered should endWith("}\n")
    rendered should include("\"campaignBinding\":{\"runId\":\"host-a:run-01\",\"manifestByteLength\":9")
    rendered should include("\"samplesNs\":[10,20]")
    rendered should include("\"p99Ns\":20")
    rendered should include("\"allocatedBytes\":[100,200]")
    rendered should include("\"p99Bytes\":200")
    rendered should include("\"jvmInputArgumentCount\":2")
    rendered should include("\"garbageCollectorDeltas\":[{\"name\":\"gc\",\"collections\":1,\"collectionTimeMs\":2}]")

    val changed = renderEnvelope(samplePayload(Vector(10L, 21L)))
    val changedManifest = renderEnvelope(payload.copy(
      campaignBinding = Some(payload.campaignBinding.get.copy(
        manifestSha256 = "b" * 64))))
    val changedRun = renderEnvelope(payload.copy(
      campaignBinding = Some(payload.campaignBinding.get.copy(runId = "host-a:run-02"))))
    val changedJvmArguments = renderEnvelope(payload.copy(
      environment = payload.environment.copy(jvmInputArgumentsSha256 = "c" * 64)))
    digestFrom(rendered) shouldBe evidenceDigest(renderPayload(payload))
    digestFrom(rendered) should not be digestFrom(changed)
    digestFrom(rendered) should not be digestFrom(changedManifest)
    digestFrom(rendered) should not be digestFrom(changedRun)
    digestFrom(rendered) should not be digestFrom(changedJvmArguments)
    renderEnvelope(payload) shouldBe rendered
  }

  test("evidence rendering rejects allocation and GC metadata drift") {
    val payload = samplePayload(Vector(10L, 20L))
    val shortAllocation = payload.scenarios.head.copy(
      allocatedBytes = Vector(100L),
      allocationStatistics = AllocationStatistics(1, 100, 100, 100, 100))
    val allocationError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(scenarios = Vector(shortAllocation)))
    }
    allocationError.getMessage should include(
      "allocation sample count does not match sampleRounds")

    val gcError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(
        garbageCollectorDeltas = Vector(GarbageCollectorDelta("other", 0, 0))))
    }
    gcError.getMessage should include("garbage collector metadata does not match sampled deltas")

    val manifestError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(
        campaignBinding = Some(payload.campaignBinding.get.copy(
          manifestSha256 = "A" * 64))))
    }
    manifestError.getMessage should include("campaign manifest SHA-256 is invalid")

    val revisionError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(implementationRevision = "unrecorded"))
    }
    revisionError.getMessage should include(
      "campaign-bound evidence has an unrecorded implementation revision")

    val nullRevisionError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(
        implementationRevision = null,
        campaignBinding = None))
    }
    nullRevisionError.getMessage shouldBe
      "requirement failed: implementationRevision is null"

    val emptyRevisionError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(
        implementationRevision = "",
        campaignBinding = None))
    }
    emptyRevisionError.getMessage shouldBe
      "requirement failed: implementationRevision must not be empty"

    val argumentsError = intercept[IllegalArgumentException] {
      renderEnvelope(payload.copy(
        environment = payload.environment.copy(jvmInputArgumentCount = -1)))
    }
    argumentsError.getMessage should include("JVM input argument count is invalid")
  }

  test("failed campaign manifest reads use constant errors and create no output") {
    val directory = Files.createTempDirectory("eip0045-b5-campaign-negative-")
    val missing = directory.resolve("missing.json")
    val empty = directory.resolve("empty.json")
    val oversized = directory.resolve("oversized.json")
    try {
      Files.createFile(empty)
      Files.write(oversized, new Array[Byte](MaxCampaignManifestBytes + 1))
      failedCampaignMessage(directory, missing, "missing-output.json") shouldBe
        "campaign manifest is not a regular file"
      failedCampaignMessage(directory, empty, "empty-output.json") shouldBe
        "campaign manifest is empty"
      failedCampaignMessage(directory, oversized, "oversized-output.json") shouldBe
        "campaign manifest exceeds 1048576 bytes"
    } finally {
      Files.deleteIfExists(missing)
      Files.deleteIfExists(empty)
      Files.deleteIfExists(oversized)
      Files.deleteIfExists(directory)
    }
  }

  test("benchmark output failures use path-free diagnostics") {
    val directory = Files.createTempDirectory("eip0045-b5-output-diagnostic-")
    val missingParent = directory.resolve("private-credential-marker").resolve("evidence.json")
    try {
      val error = intercept[IllegalArgumentException] {
        Eip0045VerifierBenchmark.main(Array(
          "--warmup-rounds", "0",
          "--sample-rounds", "1",
          "--output", missingParent.toString))
      }
      error.getMessage shouldBe "benchmark output parent directory does not exist"
      error.toString should not include missingParent.toString
      error.toString should not include "private-credential-marker"
      Files.exists(missingParent) shouldBe false
    } finally Files.deleteIfExists(directory)
  }

  private def failedCampaignMessage(
      directory: java.nio.file.Path,
      manifest: java.nio.file.Path,
      outputName: String): String = {
    val output = directory.resolve(outputName)
    val error = intercept[IllegalArgumentException] {
      Eip0045VerifierBenchmark.main(Array(
        "--implementation-revision", "commit:00",
        "--campaign-manifest", manifest.toString,
        "--campaign-run-id", "host-a:run-01",
        "--output", output.toString))
    }
    Files.exists(output) shouldBe false
    error.getMessage
  }

  private def digestFrom(envelope: String): String = {
    val marker = "\"evidenceDigest\":\""
    val start = envelope.indexOf(marker) + marker.length
    envelope.substring(start, start + 64)
  }

  private def samplePayload(samples: Vector[Long]): EvidencePayload = {
    val summary = statistics(samples) match {
      case Right(value) => value
      case Left(detail) => fail(detail)
    }
    EvidencePayload(
      startedAtUtc = "2026-07-19T00:00:00Z",
      benchmarkDurationNs = 123,
      profileId = "00",
      implementationRevision = "commit:00",
      verifierEntryPoint = "example.verify",
      resources = Vector(ResourceMetadata("proof", "classpath:/proof.bin", 2, "ab")),
      warmupRounds = 1,
      sampleRounds = samples.length,
      environment = EnvironmentMetadata(
        "runtime",
        "1",
        "vm",
        "vendor",
        "2",
        "mixed mode",
        "2.13.16",
        "os",
        "3",
        "arch",
        4,
        1024,
        "jit",
        Vector("gc"),
        "com.sun.management.ThreadMXBean.getThreadAllocatedBytes(currentThread)",
        2,
        "d" * 64,
        "cpu",
        "argument"),
      scenarios = Vector(ScenarioEvidence(
        "valid-proof",
        "verified:1:15",
        50,
        samples,
        summary,
        Vector(100L, 200L),
        AllocationStatistics(2, 100, 200, 200, 200))),
      garbageCollectorDeltas = Vector(GarbageCollectorDelta("gc", 1, 2)),
      campaignBinding = Some(CampaignBinding(
        "host-a:run-01",
        9,
        "7021e610a5f62eefd01830fea68e5fa180e8cf017c08ea0890c326b2854ebc96")),
      limitations = Vector("single host"))
  }
}
