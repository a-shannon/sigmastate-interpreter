/*
 * SPDX-License-Identifier: MIT AND Apache-2.0
 *
 * Copyright 2026 A. Shannon.
 */
package sigma.stark.profile.benchmark

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import sigma.stark.profile.benchmark.Eip0045BenchmarkSupport._

class Eip0045BenchmarkSupportSpec extends AnyFunSuite with Matchers {
  test("argument parsing is bounded, explicit, and deterministic") {
    parseArgs(Array.empty) shouldBe Right(Config(15, 100, None, None, "unrecorded"))
    parseArgs(Array(
      "--sample-rounds", "7",
      "--warmup-rounds", "0",
      "--cpu-model", "Reference CPU",
      "--implementation-revision", "commit:0123456789abcdef",
      "--output", "evidence.json")) shouldBe
      Right(Config(
        0,
        7,
        Some("evidence.json"),
        Some("Reference CPU"),
        "commit:0123456789abcdef"))

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
    parseArgs(Array("--unknown")) shouldBe Left("unknown option --unknown")
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
      "24232ba172dd2993218416e023150f2744c7e25a2c240d65fdba89fedf341105"
  }

  test("evidence envelope is canonical and binds raw samples and metadata") {
    val payload = samplePayload(Vector(10L, 20L))
    val rendered = renderEnvelope(payload)
    rendered should startWith("{\"schema\":\"eip-0045-jvm-verifier-benchmark-v2\"")
    rendered should endWith("}\n")
    rendered should include("\"samplesNs\":[10,20]")
    rendered should include("\"p99Ns\":20")
    rendered should include("\"allocatedBytes\":[100,200]")
    rendered should include("\"p99Bytes\":200")
    rendered should include("\"garbageCollectorDeltas\":[{\"name\":\"gc\",\"collections\":1,\"collectionTimeMs\":2}]")

    val changed = renderEnvelope(samplePayload(Vector(10L, 21L)))
    digestFrom(rendered) shouldBe evidenceDigest(renderPayload(payload))
    digestFrom(rendered) should not be digestFrom(changed)
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
      limitations = Vector("single host"))
  }
}
