package sigma.stark

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import sigma.stark.circuit.{CircuitParams, CircuitTapSet, PolyExtTable}
import sigma.stark.receipt.{ClaimDigest, Digest, InnerReceipt, MaybePruned}

import scala.io.Source

/** End-to-end Known-Answer-Test parity for the EIP-0045 verifyStark succinct
  * verifier ([[SuccinctVerifier]]) — the REAL devnet receipt accepting in
  * pure Scala.
  *
  * Expected values come from EXTERNAL oracles only (oracle-parity rule):
  *
  *  - `stark-kats/transcript_capture.tsv`: the complete recorded Fiat-Shamir
  *    transcript + 87 labeled checkpoints of risc0-zkp 3.0.4 ACCEPTING the
  *    real receipt (`proof_inner.bin`) — the ground truth every intermediate
  *    pipeline value is asserted against, in pipeline order, so a failure
  *    names the FIRST diverging checkpoint.
  *  - `stark-kats/receipt_kat.json`: the accept vector + 6 reject mutations,
  *    each previously confirmed against `risc0_verifier::verify` itself.
  *  - `receipt_kat.json` `journal_hex` / `image_id_hex`: the exact public
  *    inputs the devnet transaction carried.
  *
  * Checkpoints internal to [[FriVerifier]] (`fri_round_mix_<i>`,
  * `final_poly`) are not re-asserted here: FriKatSpec already replays the
  * SAME receipt's FRI phase against the same recording, and any divergence
  * in them would desynchronize the transcript rng and fail all 50 asserted
  * query positions (plus the final accept) in this spec.
  */
class SuccinctVerifierSpec extends AnyFunSuite with Matchers {

  // --------------------------------------------------------------------
  // ----- helpers -----
  // --------------------------------------------------------------------

  private def rawLines(resource: String): Array[String] = {
    val is = getClass.getResourceAsStream(resource)
    require(is != null, s"missing KAT resource $resource — run stark-kat/ generator")
    try Source.fromInputStream(is, "UTF-8").getLines().toArray
    finally is.close()
  }

  private def resourceBytes(resource: String): Array[Byte] = {
    val is = getClass.getResourceAsStream(resource)
    require(is != null, s"missing KAT resource $resource")
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

  private def load[A](what: String, r: Either[String, A]): A = r match {
    case Right(a) => a
    case Left(e)  => fail(s"$what loader rejected valid table: $e")
  }

  /** u32 CSV parsed via Long so values >= 2^31 round-trip bit-identically. */
  private def words(s: String): Array[Int] =
    if (s.isEmpty) Array.empty[Int]
    else s.split(',').map(w => java.lang.Long.parseLong(w.trim).toInt)

  private def hex(bytes: Array[Byte]): String =
    bytes.map(b => "%02x".format(b & 0xff)).mkString

  private val sha256: Array[Byte] => Array[Byte] =
    bytes => java.security.MessageDigest.getInstance("SHA-256").digest(bytes)

  private lazy val circuitParams: CircuitParams =
    load("params", CircuitParams.parse(rawLines("/stark-kats/circuit_params.tsv").iterator))
  private lazy val tapSet: CircuitTapSet =
    load("taps", CircuitTapSet.parse(rawLines("/stark-kats/circuit_taps.tsv").iterator))
  private lazy val opsTable: PolyExtTable =
    load("ops", PolyExtTable.parse(rawLines("/stark-kats/circuit_polyext_ops.tsv").iterator))

  private lazy val verifier = new SuccinctVerifier(circuitParams, tapSet, opsTable, sha256)

  private lazy val receiptBytes: Array[Byte] = resourceBytes("/stark-kats/proof_inner.bin")

  private lazy val receiptKatText: String =
    new String(resourceBytes("/stark-kats/receipt_kat.json"), "UTF-8")

  private def katHexField(name: String): Array[Byte] = {
    val m = ("\"" + name + "\"\\s*:\\s*\"([0-9a-f]*)\"").r
      .findFirstMatchIn(receiptKatText)
      .getOrElse(fail(s"receipt_kat.json missing '$name'"))
    m.group(1).grouped(2).map(Integer.parseInt(_, 16).toByte).toArray
  }

  /** The devnet transaction's public inputs, from the oracle-confirmed
    * accept vector of receipt_kat.json.
    */
  private lazy val journalBytes: Array[Byte] = katHexField("journal_hex")
  private lazy val imageIdBytes: Array[Byte] = katHexField("image_id_hex")

  // ---- transcript checkpoints, keyed by label ----

  private lazy val transcript: Array[Array[String]] =
    rawLines("/stark-kats/transcript_capture.tsv")
      .filterNot(_.startsWith("#"))
      .map(_.split("\t", -1))

  /** Plain `ck <label> <value>` rows. */
  private lazy val ck: Map[String, String] =
    transcript.filter(f => f(0) == "ck" && f.length == 3).map(f => f(1) -> f(2)).toMap

  /** `ck group_root <name> <words>` rows. */
  private lazy val ckGroupRoots: Map[String, Array[Int]] =
    transcript.filter(f => f(0) == "ck" && f(1) == "group_root").map(f => f(2) -> words(f(3))).toMap

  /** `ck <label> <count> <values>` rows (eval_u, combo_u, final_poly). */
  private lazy val ckCounted: Map[String, (Int, Array[Int])] =
    transcript.filter(f => f(0) == "ck" && f.length == 4 && f(1) != "group_root" && f(1) != "query")
      .map(f => f(1) -> ((f(2).toInt, words(f(3))))).toMap

  /** `ck query <q> pos <v>` rows, indexed by query. */
  private lazy val ckQueryPos: Map[Int, Int] =
    transcript.filter(f => f(0) == "ck" && f(1) == "query").map(f => f(2).toInt -> f(4).toInt).toMap

  /** The single `hash_ext_elems <n> <4n values> <out>` row — the recorded
    * coeff_u values as absorbed by the oracle's own hasher.
    */
  private lazy val recordedCoeffU: (Int, Array[Int]) = {
    val rows = transcript.filter(_(0) == "hash_ext_elems")
    rows should have length 1
    (rows(0)(1).toInt, words(rows(0)(2)))
  }

  /** One probed accepting run of the full pipeline (shared by the
    * checkpoint tests).
    */
  private lazy val proberun: (Either[String, Unit], Vector[(String, Array[Int])]) = {
    val recorded = Vector.newBuilder[(String, Array[Int])]
    val probe = new SuccinctVerifier.Probe {
      override def onCheckpoint(label: String, values: Array[Int]): Unit =
        recorded += ((label, values.clone()))
    }
    val res = verifier.verify(receiptBytes, journalBytes, imageIdBytes, probe)
    (res, recorded.result())
  }

  // --------------------------------------------------------------------
  // ----- happy path -----
  // --------------------------------------------------------------------

  test("checkpoint replay: every pipeline value matches the recorded oracle transcript, in order") {
    val (result, recorded) = proberun
    recorded should not be empty

    // Walk OUR emissions in pipeline order and assert each against its
    // recording: the failure message names the FIRST diverging checkpoint.
    recorded.foreach { case (label, values) =>
      withClue(s"FIRST DIVERGING CHECKPOINT '$label': ") {
        label match {
          case "seal_words" => values.toSeq shouldBe Seq(ck("seal_words").toInt)
          case "po2"        => values.toSeq shouldBe Seq(ck("po2").toInt)
          case "tot_cycles" => values.toSeq shouldBe Seq(ck("tot_cycles").toInt)
          case "domain"     => values.toSeq shouldBe Seq(ck("domain").toInt)
          case "out"        => values.toSeq shouldBe words(ck("out")).toSeq
          case "group_root code"  => values.toSeq shouldBe ckGroupRoots("code").toSeq
          case "group_root data"  => values.toSeq shouldBe ckGroupRoots("data").toSeq
          case "group_root accum" => values.toSeq shouldBe ckGroupRoots("accum").toSeq
          case "control_id_included" =>
            Digest(values).toHex shouldBe ck("control_id_included")
          case "mix"           => values.toSeq shouldBe words(ck("mix")).toSeq
          case "poly_mix"      => values.toSeq shouldBe words(ck("poly_mix")).toSeq
          case "z"             => values.toSeq shouldBe words(ck("z")).toSeq
          case "coeff_u" =>
            val (count, recordedWords) = recordedCoeffU
            count shouldBe ck("coeff_u_committed").toInt
            values.length shouldBe count * 4
            values.toSeq shouldBe recordedWords.toSeq
          case "eval_u" =>
            val (count, ws) = ckCounted("eval_u")
            values.length shouldBe count * 4
            values.toSeq shouldBe ws.toSeq
          case "result"        => values.toSeq shouldBe words(ck("result")).toSeq
          case "check_value"   => values.toSeq shouldBe words(ck("check_value")).toSeq
          case "fri_batch_mix" => values.toSeq shouldBe words(ck("fri_batch_mix")).toSeq
          case "combo_u" =>
            val (count, ws) = ckCounted("combo_u")
            values.length shouldBe count * 4
            values.toSeq shouldBe ws.toSeq
          case "query" =>
            values(1) shouldBe ckQueryPos(values(0))
          case "seal_control_root" =>
            Digest(values).toHex shouldBe ck("seal_control_root")
          case "seal_output_hash_bytes" =>
            hex(values.map(_.toByte)) shouldBe ck("seal_output_hash")
          case other => fail(s"unknown probe label '$other'")
        }
      }
    }

    // Coverage: the run visited every asserted stage.
    val labels = recorded.map(_._1)
    Seq("seal_words", "po2", "out", "group_root code", "control_id_included",
      "group_root data", "mix", "group_root accum", "poly_mix", "z", "coeff_u",
      "eval_u", "result", "check_value", "fri_batch_mix", "combo_u",
      "seal_control_root", "seal_output_hash_bytes").foreach { l =>
      withClue(s"stage '$l' not reached: ") { labels should contain(l) }
    }
    labels.count(_ == "query") shouldBe circuitParams.queries

    withClue("verdict: ") { result shouldBe Right(()) }
    ck("verdict") shouldBe "accept"
  }

  test("THE test: the real devnet receipt accepts end-to-end in pure Scala") {
    val t0 = System.nanoTime()
    verifier.verify(receiptBytes, journalBytes, imageIdBytes) shouldBe Right(())
    val ms = (System.nanoTime() - t0) / 1e6
    info(f"full succinct verify (parse + STARK + claim binding): $ms%.0f ms")
  }

  test("claim binding: tagged-struct digests match the recorded claim checkpoints") {
    val r = InnerReceipt.parse(receiptBytes) match {
      case Right(InnerReceipt.Succinct(r)) => r
      case other                           => fail(s"unexpected receipt parse: $other")
    }

    // Receipt fields vs recording.
    r.hashfn shouldBe ck("hashfn")
    r.verifierParameters.toHex shouldBe ck("verifier_parameters")
    r.controlId.toHex shouldBe ck("control_id")
    r.controlInclusionProof.index shouldBe ck("control_inclusion_index").toInt
    r.controlInclusionProof.digests.map(_.toHex).mkString(",") shouldBe
      ck("control_inclusion_digests")
    circuitParams.allowedControlRoot shouldBe ck("allowed_control_root")

    // Public inputs vs recording.
    hex(sha256(journalBytes)) shouldBe ck("journal_sha256")
    hex(imageIdBytes) shouldBe ck("image_id")

    // Tagged-struct scheme, stage by stage.
    val claim = r.claim match {
      case MaybePruned.Value(c) => c
      case other                => fail(s"fixture claim should be a value: $other")
    }
    val post = claim.post match {
      case MaybePruned.Value(s) => s
      case other                => fail(s"fixture post should be a value: $other")
    }
    hex(ClaimDigest.systemStateDigest(sha256, post)) shouldBe ck("post_system_state_digest")
    val output = claim.output match {
      case MaybePruned.Value(Some(o)) => o
      case other                      => fail(s"fixture output should be present: $other")
    }
    hex(ClaimDigest.outputDigest(sha256, output)) shouldBe ck("output_digest")
    hex(ClaimDigest.claimDigest(sha256, r.claim)) shouldBe ck("claim_digest")
    hex(ClaimDigest.expectedOkClaimDigest(sha256, imageIdBytes, sha256(journalBytes))) shouldBe
      ck("expected_claim_digest")
    // The capture itself is consistent: the seal output slot equals the
    // claim digest equals the expected claim digest.
    ck("claim_digest") shouldBe ck("seal_output_hash")
    ck("expected_claim_digest") shouldBe ck("claim_digest")
  }

  // --------------------------------------------------------------------
  // ----- error paths -----
  // --------------------------------------------------------------------

  /** The mutation recipes of receipt_kat.json (offset/xor/truncate_to/
    * mutate_image_id), extracted with a minimal fixed-shape reader — every
    * one was confirmed as a reject by `risc0_verifier::verify` itself at
    * generation time (`oracle_confirmed: true`).
    */
  private case class Mutation(
      description: String,
      offset: Option[Int],
      xor: Option[Int],
      truncateTo: Option[Int],
      mutateImageId: Boolean)

  private lazy val mutations: Seq[Mutation] = {
    val text = new String(resourceBytes("/stark-kats/receipt_kat.json"), "UTF-8")
    def field(block: String, name: String): String = {
      val m = ("\"" + name + "\"\\s*:\\s*(null|true|false|-?\\d+|\"[^\"]*\")").r
        .findFirstMatchIn(block)
        .getOrElse(fail(s"receipt_kat.json mutation missing field '$name'"))
      m.group(1)
    }
    def intOpt(v: String): Option[Int] = if (v == "null") None else Some(v.toInt)
    val blocks = text.split("\\{").drop(2) // fields before "mutations" hold no objects
    val ms = blocks.toSeq.map { b =>
      Mutation(
        description = field(b, "description").stripPrefix("\"").stripSuffix("\""),
        offset = intOpt(field(b, "offset")),
        xor = intOpt(field(b, "xor")),
        truncateTo = intOpt(field(b, "truncate_to")),
        mutateImageId = field(b, "mutate_image_id") == "true")
    }
    ms should have length 6
    ms.foreach { m => field(blocks(ms.indexOf(m)), "expected") shouldBe "false" }
    ms
  }

  test("all oracle-confirmed receipt_kat mutations reject with Left, never throw") {
    mutations.foreach { m =>
      withClue(s"mutation '${m.description}': ") {
        val proof = m.truncateTo match {
          case Some(n) => receiptBytes.take(n)
          case None    => receiptBytes.clone()
        }
        (m.offset, m.xor) match {
          case (Some(off), Some(x)) => proof(off) = (proof(off) ^ x).toByte
          case _                    => ()
        }
        val imageId =
          if (m.mutateImageId) {
            val id = imageIdBytes.clone()
            id(0) = (id(0) ^ 1).toByte
            id
          } else imageIdBytes
        verifier.verify(proof, journalBytes, imageId).isLeft shouldBe true
      }
    }
  }

  test("wrong journal byte rejects with Left") {
    val journal = journalBytes.clone()
    journal(0) = (journal(0) ^ 1).toByte
    verifier.verify(receiptBytes, journal, imageIdBytes).isLeft shouldBe true
  }

  test("wrong image id rejects with Left") {
    val id = imageIdBytes.clone()
    id(31) = (id(31) ^ 0x80).toByte
    verifier.verify(receiptBytes, journalBytes, id).isLeft shouldBe true
  }

  test("malformed top-level inputs reject with Left, never throw") {
    // Image id must be exactly 32 bytes.
    verifier.verify(receiptBytes, journalBytes, Array.emptyByteArray).isLeft shouldBe true
    verifier.verify(receiptBytes, journalBytes, new Array[Byte](33)).isLeft shouldBe true
    verifier.verify(receiptBytes, journalBytes, null).isLeft shouldBe true
    // Degenerate receipts.
    verifier.verify(Array.emptyByteArray, journalBytes, imageIdBytes).isLeft shouldBe true
    verifier.verify(null, journalBytes, imageIdBytes).isLeft shouldBe true
    verifier.verify(receiptBytes, null, imageIdBytes).isLeft shouldBe true
  }
}
