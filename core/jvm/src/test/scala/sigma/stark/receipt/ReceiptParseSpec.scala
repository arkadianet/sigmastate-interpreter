package sigma.stark.receipt

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import scala.io.Source

/** Known-Answer-Test parity for the EIP-0045 verifyStark receipt parser.
  *
  * Expected values come from an EXTERNAL oracle — the `risc0_verifier` +
  * `bincode` crates themselves, which deserialized the very same
  * `proof_inner.bin` and dumped every field (and confirmed every reject
  * vector actually fails Rust-side) via `stark-kat/src/bin/receipt_dump.rs`
  * into `resources/stark-kats/receipt_struct.tsv` — never from the Scala
  * code under test (oracle-parity rule: a self-oracle proves consistency,
  * not correctness).
  */
class ReceiptParseSpec extends AnyFunSuite with Matchers {

  // ----- helpers -----

  private def resourceBytes(resource: String): Array[Byte] = {
    val is = getClass.getResourceAsStream(resource)
    require(is != null, s"missing KAT resource $resource — run stark-kat/ generator")
    try {
      val buf = new java.io.ByteArrayOutputStream()
      val chunk = new Array[Byte](8192)
      var n = is.read(chunk)
      while (n >= 0) {
        buf.write(chunk, 0, n)
        n = is.read(chunk)
      }
      buf.toByteArray
    } finally is.close()
  }

  /** All key/value pairs of the oracle dump, in order (keys may repeat). */
  private def oraclePairs: Seq[(String, String)] = {
    val is = getClass.getResourceAsStream("/stark-kats/receipt_struct.tsv")
    require(is != null, "missing receipt_struct.tsv — run stark-kat receipt_dump")
    try {
      Source
        .fromInputStream(is, "UTF-8")
        .getLines()
        .filterNot(l => l.startsWith("#") || l.isEmpty)
        .map { l =>
          val i = l.indexOf('\t')
          require(i > 0, s"malformed oracle line: $l")
          (l.substring(0, i), l.substring(i + 1))
        }
        .toList
    } finally is.close()
  }

  private lazy val oracle: Seq[(String, String)] = oraclePairs
  private lazy val proofBytes: Array[Byte] = resourceBytes("/stark-kats/proof_inner.bin")

  private def one(key: String): String = {
    val vs = oracle.collect { case (k, v) if k == key => v }
    vs.size shouldBe 1
    vs.head
  }

  private def all(key: String): Seq[String] =
    oracle.collect { case (k, v) if k == key => v }

  /** Oracle u32 (unsigned decimal) as the parser's raw-Int-bits convention. */
  private def u32(s: String): Int = java.lang.Integer.parseUnsignedInt(s)

  private def parsedSuccinct: SuccinctReceipt =
    InnerReceipt.parse(proofBytes) match {
      case Right(InnerReceipt.Succinct(sr)) => sr
      case other => fail(s"expected Right(Succinct(_)), got $other")
    }

  private def hex(bytes: Array[Byte]): String =
    bytes.map(b => "%02x".format(b & 0xFF)).mkString

  // ----- happy path -----

  test("real succinct receipt parses and the variant matches the oracle") {
    one("variant") shouldBe "Succinct"
    proofBytes.length shouldBe one("total_len").toInt
    InnerReceipt.parse(proofBytes).isRight shouldBe true
  }

  test("seal matches the oracle (length, first 8 and last 8 words)") {
    val sr = parsedSuccinct
    sr.seal.length shouldBe one("seal_len").toInt
    sr.seal.take(8) shouldBe one("seal_first8").split(',').map(u32)
    sr.seal.takeRight(8) shouldBe one("seal_last8").split(',').map(u32)
  }

  test("control_id, hashfn and verifier_parameters match the oracle") {
    val sr = parsedSuccinct
    sr.controlId.toHex shouldBe one("control_id")
    sr.hashfn shouldBe one("hashfn")
    sr.verifierParameters.toHex shouldBe one("verifier_parameters")
  }

  test("claim structure matches the oracle field by field") {
    val sr = parsedSuccinct
    one("claim_variant") shouldBe "Value"
    val claim = sr.claim match {
      case MaybePruned.Value(c) => c
      case p => fail(s"expected Value claim, got $p")
    }

    one("claim_pre_variant") shouldBe "Value"
    claim.pre match {
      case MaybePruned.Value(ss) =>
        ss.pc shouldBe u32(one("claim_pre_pc"))
        ss.merkleRoot.toHex shouldBe one("claim_pre_merkle_root")
      case p => fail(s"expected Value pre, got $p")
    }

    one("claim_post_variant") shouldBe "Value"
    claim.post match {
      case MaybePruned.Value(ss) =>
        ss.pc shouldBe u32(one("claim_post_pc"))
        ss.merkleRoot.toHex shouldBe one("claim_post_merkle_root")
      case p => fail(s"expected Value post, got $p")
    }

    val Array(exitName, exitUser) = one("claim_exit_code").split(',')
    (claim.exitCode, exitName) match {
      case (ExitCode.Halted(user), "Halted") => user shouldBe u32(exitUser)
      case (ExitCode.Paused(user), "Paused") => user shouldBe u32(exitUser)
      case (ExitCode.SystemSplit, "SystemSplit") => ()
      case (ExitCode.SessionLimit, "SessionLimit") => ()
      case other => fail(s"exit code mismatch vs oracle: $other")
    }

    one("claim_input_variant") shouldBe "Pruned"
    claim.input match {
      case MaybePruned.Pruned(d) => d.toHex shouldBe one("claim_input_digest")
      case v => fail(s"expected Pruned input, got $v")
    }

    one("claim_output_variant") shouldBe "Value"
    one("claim_output_some") shouldBe "true"
    val output = claim.output match {
      case MaybePruned.Value(Some(o)) => o
      case other => fail(s"expected Value(Some(output)), got $other")
    }
    one("claim_output_journal_variant") shouldBe "Value"
    output.journal match {
      case MaybePruned.Value(j) => hex(j) shouldBe one("claim_output_journal")
      case p => fail(s"expected Value journal, got $p")
    }
    one("claim_output_assumptions_variant") shouldBe "Value"
    output.assumptions match {
      case MaybePruned.Value(a) =>
        a.items.size shouldBe one("claim_output_assumptions_len").toInt
      case p => fail(s"expected Value assumptions, got $p")
    }
  }

  test("control inclusion proof matches the oracle (index + every digest)") {
    val sr = parsedSuccinct
    val mp = sr.controlInclusionProof
    mp.index shouldBe u32(one("merkle_index"))
    val n = one("merkle_digests_len").toInt
    mp.digests.size shouldBe n
    (0 until n).foreach { i =>
      mp.digests(i).toHex shouldBe one(s"merkle_digest_$i")
    }
  }

  test("trailing-byte policy matches the Rust oracle (bincode legacy allows trailing bytes)") {
    val allowed = one("trailing_bytes_allowed").toBoolean
    val withTrailing = proofBytes :+ 0xAB.toByte
    InnerReceipt.parse(withTrailing).isRight shouldBe allowed
  }

  // ----- error paths -----

  test("every oracle-confirmed truncation returns Left") {
    val lens = all("truncate_fails").map(_.toInt)
    lens should not be empty
    lens.foreach { t =>
      withClue(s"truncate to $t bytes: ") {
        InnerReceipt.parse(proofBytes.take(t)).isLeft shouldBe true
      }
    }
  }

  test("every oracle-confirmed length-region corruption returns Left") {
    val cases = all("corrupt_fails").map { s =>
      val Array(off, x) = s.split(',')
      (off.toInt, x.toInt)
    }
    cases should not be empty
    cases.foreach { case (off, x) =>
      withClue(s"corrupt byte $off ^ $x: ") {
        val c = proofBytes.clone()
        c(off) = (c(off) ^ x).toByte
        InnerReceipt.parse(c).isLeft shouldBe true
      }
    }
  }

  test("single-byte corruptions across the u64 length-prefix regions return Left") {
    // The oracle dump pins the length-prefix offsets; forcing any HIGH byte of
    // a u64 length non-zero makes the length exceed the remaining input, which
    // Rust bincode rejects (confirmed by the corrupt_fails vectors above for
    // one byte of each region) — the parser must reject them all, not allocate.
    val regions = Seq(
      one("offset_seal_len").toInt,
      one("offset_hashfn").toInt,
      one("offset_merkle_digests_len").toInt
    )
    regions.foreach { base =>
      (3 to 7).foreach { i =>
        withClue(s"length high byte at offset ${base + i}: ") {
          val c = proofBytes.clone()
          c(base + i) = (c(base + i) ^ 0x40).toByte
          InnerReceipt.parse(c).isLeft shouldBe true
        }
      }
    }
  }

  test("empty and garbage inputs return Left, never throw") {
    InnerReceipt.parse(Array.emptyByteArray).isLeft shouldBe true
    InnerReceipt.parse(null).isLeft shouldBe true
    InnerReceipt.parse(Array.fill[Byte](64)(0x7F.toByte)).isLeft shouldBe true
    // Composite variant tag (0) is recognized but unsupported.
    InnerReceipt.parse(Array[Byte](0, 0, 0, 0)).isLeft shouldBe true
  }
}
