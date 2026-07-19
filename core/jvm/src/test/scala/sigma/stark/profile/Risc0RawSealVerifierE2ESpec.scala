package sigma.stark.profile

import java.io.ByteArrayOutputStream
import java.security.MessageDigest

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import sigma.stark.FriVerifier
import sigma.stark.circuit.{CircuitTapSet, PolyExtTable}
import sigma.stark.profile.Risc0RawSealVerifier._

import scala.io.Source

/** End-to-end interoperability tests for the direct EIP-0045 RISC Zero
  * raw-seal verifier. The positive fixture was emitted by RISC Zero's own
  * prover at the pinned commit recorded in `fixture-manifest.json`; no host
  * receipt codec or bincode parser participates in these tests.
  */
class Risc0RawSealVerifierE2ESpec extends AnyFunSuite with Matchers {

  private val FixtureRoot = "/stark-kats/eip0045-direct/"
  private val ChunkLengths = Array(65535, 65535, 65535, 26063)

  private def resourceBytes(path: String): Array[Byte] = {
    val in = getClass.getResourceAsStream(path)
    require(in != null, s"missing test resource $path")
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

  private def resourceLines(path: String): Array[String] = {
    val in = getClass.getResourceAsStream(path)
    require(in != null, s"missing test resource $path")
    try Source.fromInputStream(in, "UTF-8").getLines().toArray
    finally in.close()
  }

  private def sha256Hex(bytes: Array[Byte]): String =
    MessageDigest.getInstance("SHA-256").digest(bytes)
      .map(b => f"${b & 0xff}%02x").mkString

  private def hex(value: String): Array[Byte] = {
    require((value.length & 1) == 0, "hex input must have even length")
    value.grouped(2).map(Integer.parseInt(_, 16).toByte).toArray
  }

  private def manifestResource(path: String): String =
    if (path.startsWith("../")) "/stark-kats/" + path.substring(3)
    else FixtureRoot + path

  private def load[A](label: String, value: Either[String, A]): A = value match {
    case Right(result) => result
    case Left(detail)  => fail(s"$label rejected pinned oracle data: $detail")
  }

  private lazy val oracleLines = resourceLines(FixtureRoot + "profile-oracle.tsv")
    .filter(line => line.nonEmpty && !line.startsWith("#"))

  private lazy val parameters: Map[String, String] = oracleLines
    .filter(_.startsWith("param\t"))
    .map(_.split("\t", -1))
    .map(fields => fields(1) -> fields(2))
    .toMap

  private lazy val innerControlRoot: Array[Byte] = oracleLines
    .find(_.startsWith("inner_control_root\t"))
    .map(_.split("\t", -1)(1)).map(hex)
    .getOrElse(fail("profile oracle has no inner control root"))

  private lazy val controls: IndexedSeq[(Int, Int, Array[Byte])] = oracleLines
    .filter(_.startsWith("control\t"))
    .map(_.split("\t", -1))
    .map(fields => (fields(1).toInt, fields(2).toInt, hex(fields(3))))
    .toIndexedSeq

  private lazy val taps: CircuitTapSet =
    load("tap table", CircuitTapSet.parse(
      resourceLines("/stark-kats/circuit_taps.tsv").iterator))

  private lazy val polyExt: PolyExtTable =
    load("poly-ext table", PolyExtTable.parse(
      resourceLines("/stark-kats/circuit_polyext_ops.tsv").iterator))

  private lazy val verifierParameters = new VerifierParameters(
    parameters("proof_system_info"),
    parameters("circuit_info"),
    parameters("output_size").toInt,
    parameters("mix_size").toInt,
    parameters("queries").toInt,
    parameters("inv_rate").toInt,
    parameters("ext_size").toInt,
    parameters("check_size").toInt,
    parameters("fri_fold").toInt,
    parameters("fri_fold_po2").toInt,
    parameters("fri_min_degree").toInt,
    taps,
    polyExt)

  private def profile(
      root: Array[Byte],
      controlOverrides: Map[(Int, Int), Array[Byte]]): RawSealProfile = {
    val entries = controls.map { case (kind, parameter, controlId) =>
      new TerminalControl(
        kind,
        parameter,
        controlOverrides.getOrElse((kind, parameter), controlId))
    }
    new RawSealProfile(parameters("outer_po2").toInt, root, entries)
  }

  private def verifier(
      root: Array[Byte] = innerControlRoot,
      controlOverrides: Map[(Int, Int), Array[Byte]] = Map.empty): Risc0RawSealVerifier =
    new Risc0RawSealVerifier(verifierParameters, profile(root, controlOverrides))

  private lazy val rawSeal = resourceBytes(FixtureRoot + "po2-15-raw-seal.bin")
  private lazy val expectedClaim = resourceBytes(FixtureRoot + "po2-15-claim-digest.bin")

  private def canonicalChunks(bytes: Array[Byte]): Array[Array[Byte]] = {
    require(bytes.length == ChunkLengths.sum, "fixture does not have the canonical raw-seal size")
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

  private final class QueryProbe extends Probe {
    var queries: Int = 0
    override def onCheckpoint(label: String, values: Array[Int]): Unit =
      if (label == "query") queries += 1
  }

  test("fixture manifest pins public provenance, exact sizes, and SHA-256 digests") {
    val manifestText = new String(
      resourceBytes(FixtureRoot + "fixture-manifest.json"),
      "UTF-8")
    manifestText should include("\"formatVersion\": 1")
    manifestText should include("\"candidateStatus\": \"non-final-pre-B3-test-evidence\"")
    manifestText should include("8eb06ab020a92dc5b63ba6dd0836d432aba6d890")

    val fileEntry =
      """(?s)\{\s*"path"\s*:\s*"([^"]+)"\s*,\s*"encoding"\s*:\s*"([^"]+)"\s*,\s*"length"\s*:\s*([0-9]+)\s*,\s*"sha256"\s*:\s*"([0-9a-f]{64})"\s*\}""".r
    val entries = fileEntry.findAllMatchIn(manifestText).map { matched =>
      (matched.group(1), matched.group(2), matched.group(3).toLong, matched.group(4))
    }.toVector
    entries.length shouldBe 5

    entries.foreach { case (path, encoding, expectedLength, expectedDigest) =>
      val bytes = resourceBytes(manifestResource(path))
      withClue(path + ": ") {
        bytes.length.toLong shouldBe expectedLength
        sha256Hex(bytes) shouldBe expectedDigest
        encoding match {
          case "raw-binary" => ()
          case "utf8-lf-text" =>
            bytes should not contain 0x0d.toByte
            new String(bytes, "UTF-8").getBytes("UTF-8") shouldBe bytes
          case other => fail(s"unknown fixture encoding $other")
        }
      }
    }

    manifestText should not include ("D:\\")
    manifestText should not include ("C:\\")
  }

  test("stock verifier accepts the real po2=15 seal through exactly four canonical chunks") {
    val chunks = canonicalChunks(rawSeal)
    chunks.map(_.length).toSeq shouldBe ChunkLengths.toSeq
    verifier().verify(chunks, expectedClaim) shouldBe Right(Verified(1, 15))
  }

  test("claim mismatch is rejected only after all 50 proof queries") {
    val wrongClaim = expectedClaim.clone()
    wrongClaim(0) = (wrongClaim(0) ^ 1).toByte
    val probe = new QueryProbe
    verifier().verify(canonicalChunks(rawSeal), wrongClaim, probe) shouldBe Left(ClaimMismatch)
    probe.queries shouldBe FriVerifier.Queries
  }

  test("a reconstructed control ID outside the fixed allowlist is rejected") {
    val disallowed = Array.fill[Byte](DigestBytes)(0)
    verifier(controlOverrides = Map((1, 15) -> disallowed))
      .verify(canonicalChunks(rawSeal), expectedClaim) shouldBe Left(ControlIdNotAllowed)
  }

  test("inner control-root mismatch is rejected only after full cryptographic verification") {
    val wrongRoot = Array.fill[Byte](DigestBytes)(0)
    val probe = new QueryProbe
    verifier(root = wrongRoot)
      .verify(canonicalChunks(rawSeal), expectedClaim, probe) shouldBe Left(InnerControlRootMismatch)
    probe.queries shouldBe FriVerifier.Queries
  }

  test("cryptographic mutations in the middle and final proof word cannot verify") {
    Seq(27000, RawSealV1Decoder.WordCount - 1).foreach { wordIndex =>
      val mutated = rawSeal.clone()
      val offset = wordIndex * 4
      mutated(offset) = (mutated(offset) ^ 1).toByte
      withClue(s"word $wordIndex: ") {
        verifier().verify(canonicalChunks(mutated), expectedClaim) match {
          case Left(MalformedProof("fri", detail)) => detail should include("root path mismatch")
          case Left(other) => fail(s"mutation reached an unexpected rejection branch: $other")
          case Right(value) => fail(s"mutation verified as $value")
        }
      }
    }
  }

  test("transport partition and literal outerPo2 are consensus-strict") {
    val shifted = Array(
      java.util.Arrays.copyOfRange(rawSeal, 0, 65534),
      java.util.Arrays.copyOfRange(rawSeal, 65534, 131070),
      java.util.Arrays.copyOfRange(rawSeal, 131070, 196605),
      java.util.Arrays.copyOfRange(rawSeal, 196605, rawSeal.length))
    verifier().verify(shifted, expectedClaim) shouldBe Left(TransportRejected(
      RawSealV1Decoder.WrongChunkLength(0, 65535, 65534)))

    val wrongOuterPo2 = rawSeal.clone()
    wrongOuterPo2(32 * 4) = 17
    wrongOuterPo2(32 * 4 + 1) = 0
    wrongOuterPo2(32 * 4 + 2) = 0
    wrongOuterPo2(32 * 4 + 3) = 0
    verifier().verify(canonicalChunks(wrongOuterPo2), expectedClaim) shouldBe Left(TransportRejected(
      RawSealV1Decoder.WrongOuterPo2(RawSealV1Decoder.ExpectedOuterPo2, 17L)))
  }
}
