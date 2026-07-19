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

  test("JSON quoting is complete for evidence-controlled strings") {
    quote("a\"b\\c\n\t" + 1.toChar) shouldBe "\"a\\\"b\\\\c\\n\\t\\u0001\""
  }

  test("domain-separated evidence digest has an independent golden value") {
    evidenceDigest("{\"a\":1}") shouldBe
      "12556149b3cf32123966b175607fe6d843ee2f80c4e43b38cc1d2df4eee99cb8"
  }

  test("evidence envelope is canonical and binds raw samples and metadata") {
    val payload = samplePayload(Vector(10L, 20L))
    val rendered = renderEnvelope(payload)
    rendered should startWith("{\"schema\":\"eip-0045-jvm-verifier-benchmark-v1\"")
    rendered should endWith("}\n")
    rendered should include("\"samplesNs\":[10,20]")
    rendered should include("\"p99Ns\":20")

    val changed = renderEnvelope(samplePayload(Vector(10L, 21L)))
    digestFrom(rendered) shouldBe evidenceDigest(renderPayload(payload))
    digestFrom(rendered) should not be digestFrom(changed)
    renderEnvelope(payload) shouldBe rendered
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
        "cpu",
        "argument"),
      scenarios = Vector(ScenarioEvidence(
        "valid-proof",
        "verified:1:15",
        50,
        samples,
        summary)),
      limitations = Vector("single host"))
  }
}
