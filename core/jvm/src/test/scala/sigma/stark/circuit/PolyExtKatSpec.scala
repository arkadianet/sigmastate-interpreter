package sigma.stark.circuit

import org.bouncycastle.crypto.digests.Blake2bDigest
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import sigma.stark.Ext4

import scala.io.Source

/** Known-Answer-Test parity for the EIP-0045 verifyStark constraint-system
  * data tables and the poly-ext interpreter.
  *
  * Expected values come from EXTERNAL oracles only — the recursion-circuit
  * tables extracted from risc0-circuit-recursion 4.0.4 / risc0-zkp 3.0.4 and
  * the Fiat-Shamir transcript capture of the REAL devnet receipt accepted by
  * the untouched Rust verifier (`stark-kats/transcript_capture.tsv`) — never
  * from the Scala code under test (oracle-parity rule).
  */
class PolyExtKatSpec extends AnyFunSuite with Matchers {

  // Raw lines, comments included — the loaders skip them themselves.
  private def rawLines(resource: String): Array[String] = {
    val is = getClass.getResourceAsStream(resource)
    require(is != null, s"missing KAT resource $resource — run stark-kat/ generator")
    try Source.fromInputStream(is, "UTF-8").getLines().toArray
    finally is.close()
  }

  private def load[A](what: String, r: Either[String, A]): A = r match {
    case Right(a) => a
    case Left(e)  => fail(s"$what loader rejected valid table: $e")
  }

  private lazy val opsTable: PolyExtTable =
    load("ops", PolyExtTable.parse(rawLines("/stark-kats/circuit_polyext_ops.tsv").iterator))
  private lazy val tapSet: CircuitTapSet =
    load("taps", CircuitTapSet.parse(rawLines("/stark-kats/circuit_taps.tsv").iterator))
  private lazy val circuitParams: CircuitParams =
    load("params", CircuitParams.parse(rawLines("/stark-kats/circuit_params.tsv").iterator))

  /** The `ck` checkpoint lines of the transcript capture relevant here, by
    * label. `eval_u` carries a leading count field; the rest are plain
    * comma-joined standard-form u32 lists (see `circuit_tables.md`).
    */
  private lazy val checkpoints: Map[String, Array[Int]] = {
    val wanted = Set("out", "mix", "poly_mix", "eval_u", "result", "check_value")
    rawLines("/stark-kats/transcript_capture.tsv").iterator
      .filter(l => l.startsWith("ck\t"))
      .map(_.split("\t", -1))
      .filter(f => wanted.contains(f(1)))
      .map { f =>
        val values = f.last.split(",", -1).map(java.lang.Long.parseLong).map { v =>
          v should be >= 0L
          v should be < 2013265921L
          v.toInt
        }
        if (f(1) == "eval_u") f(2).toInt shouldBe values.length / 4
        (f(1), values)
      }
      .toMap
  }

  private def ext(words: Array[Int], at: Int): Ext4 =
    Ext4(words(at), words(at + 1), words(at + 2), words(at + 3))

  private def blake2b256Hex(bytes: Array[Byte]): String = {
    val d = new Blake2bDigest(256)
    d.update(bytes, 0, bytes.length)
    val out = new Array[Byte](32)
    d.doFinal(out, 0)
    out.map(b => "%02x".format(b & 0xff)).mkString
  }

  // ----- loaders -----

  test("taps loader matches the extracted recursion TapSet (643 taps / 163 regs / 12,23,128 columns)") {
    tapSet.tapSize shouldBe 643
    tapSet.regCount shouldBe 163
    tapSet.regs.length shouldBe 163
    tapSet.groupNames.toSeq shouldBe Seq("accum", "code", "data")
    tapSet.groupBegin.toSeq shouldBe Seq(0, 16, 39, 643)
    tapSet.groupSize.toSeq shouldBe Seq(12, 23, 128)
    tapSet.groupTapCount(0) shouldBe 16
    tapSet.groupTapCount(1) shouldBe 23
    tapSet.groupTapCount(2) shouldBe 604
    tapSet.combosCount shouldBe 5
    tapSet.comboBegin.toSeq shouldBe Seq(0, 1, 3, 9, 15, 20)
    tapSet.comboTaps.toSeq shouldBe Seq(0, 0, 1, 0, 1, 2, 3, 4, 68, 0, 1, 2, 7, 15, 16, 0, 2, 7, 15, 16)
    tapSet.totComboBacks shouldBe 20
    // Registers cover the taps exactly, in order, sized by their skip.
    tapSet.regs.map(_.size).sum shouldBe 643
    // Register back-lists are exactly what the eval_u loop consumes; spot-pin
    // the first accum register (backs 0,1) and every code register (back 0).
    tapSet.regs(0).backs.toSeq shouldBe Seq(0, 1)
    tapSet.regs.filter(_.group == 1).foreach { r => r.backs.toSeq shouldBe Seq(0) }
  }

  test("params loader matches the extracted verifier-context parameters") {
    circuitParams.proofSystemInfo shouldBe "RISC0_STARK:v1__"
    circuitParams.circuitInfo shouldBe "RECURSION:rev1v1"
    circuitParams.outputSize shouldBe 32
    circuitParams.mixSize shouldBe 20
    circuitParams.queries shouldBe 50
    circuitParams.invRate shouldBe 4
    circuitParams.extSize shouldBe 4
    circuitParams.checkSize shouldBe 16
    circuitParams.friFold shouldBe 16
    circuitParams.friFoldPo2 shouldBe 4
    circuitParams.friMinDegree shouldBe 256
    circuitParams.minCyclesPo2 shouldBe 13
    circuitParams.maxCyclesPo2 shouldBe 24
    circuitParams.minLiftPo2 shouldBe 14
    circuitParams.hashfn shouldBe "poseidon2"
    circuitParams.allowedControlRoot shouldBe
      "a54dc85ac99f851c92d7c96d7318af41dbe7c0194edfcc37eb4d422a998c1f56"
    circuitParams.controlIds.length shouldBe 27
    circuitParams.controlIds.head shouldBe
      "0d79bc33b4760b4783cbb96fdc87724c7e0c463eb0ba1b2705d39f43c698bd2d"
    circuitParams.namedControlIds.length shouldBe 32
  }

  test("ops loader matches the extracted table shape and its Blake2b-256 integrity hash") {
    opsTable.opsCount shouldBe 12359
    opsTable.ret shouldBe 1228
    opsTable.fpVars shouldBe 11130
    opsTable.mixVars shouldBe 1229
    opsTable.opcodeHistogram shouldBe Map(
      "Add" -> 4061, "AndCond" -> 152, "AndEqz" -> 1076, "Const" -> 284,
      "Get" -> 669, "GetGlobal" -> 52, "Mul" -> 4679, "Sub" -> 1385, "True" -> 1)
    // Integrity: Blake2b-256 over the canonical re-serialization of the
    // PARSED ops must equal the hash the generator recorded from the Rust
    // table (proves parse fidelity, not just file integrity).
    blake2b256Hex(opsTable.canonicalBytes) shouldBe opsTable.blake2b256Hex
    // Every Get stays inside the tapset; the table references its full width.
    val getTaps = opsTable.ops.collect { case PolyExtOp.Get(t) => t }
    getTaps.max should be < tapSet.tapSize
  }

  // ----- oracle parity -----

  test("interpreter reproduces the recorded constraint evaluation of the real devnet receipt") {
    val out = checkpoints("out")
    val mix = checkpoints("mix")
    out.length shouldBe circuitParams.outputSize
    mix.length shouldBe circuitParams.mixSize
    val polyMix = ext(checkpoints("poly_mix"), 0)
    val evalUWords = checkpoints("eval_u")
    evalUWords.length shouldBe tapSet.tapSize * 4
    val u = Array.tabulate(tapSet.tapSize)(i => ext(evalUWords, i * 4))

    val result = PolyExtInterpreter.step(opsTable, polyMix, u, Array(out, mix)) match {
      case Right(ms) => ms
      case Left(e)   => fail(s"interpreter rejected the recorded inputs: $e")
    }
    result.tot shouldBe ext(checkpoints("result"), 0)
    // The verifier accepted, so the recorded check polynomial equals the
    // recorded result — pin that consistency of the capture itself too.
    checkpoints("check_value").toSeq shouldBe checkpoints("result").toSeq
  }

  // ----- error paths -----

  private val tinyTable = Seq(
    "meta\tops_count\t5",
    "meta\tret\t1",
    "meta\tfp_vars\t3",
    "meta\tmix_vars\t2",
    "meta\topcode_histogram\tAndEqz=1,Const=2,Sub=1,True=1",
    "meta\tblake2b256\t00",
    "op\t0\tConst\t5",
    "op\t1\tConst\t5",
    "op\t2\tSub\t0,1",
    "op\t3\tTrue\t",
    "op\t4\tAndEqz\t0,2"
  )

  test("ops loader accepts a well-formed tiny table and the interpreter evaluates it") {
    val t = load("tiny", PolyExtTable.parse(tinyTable.iterator))
    val polyMix = Ext4(7, 0, 3, 0)
    // (5 - 5) folded through True gives tot = 0, mul = polyMix.
    PolyExtInterpreter.step(t, polyMix, Array.empty[Ext4], Array(Array.empty[Int], Array.empty[Int])) match {
      case Right(ms) =>
        ms.tot shouldBe Ext4.Zero
        ms.mul shouldBe polyMix
      case Left(e) => fail(s"tiny table rejected: $e")
    }
  }

  test("ops loader rejects forward stack references, bad mnemonics, and shape mismatches") {
    def mutate(replace: (String, String)*): Seq[String] =
      tinyTable.map(l => replace.foldLeft(l) { case (acc, (from, to)) => if (acc == from) to else acc })
    // Sub referencing an fp var that is not pushed yet.
    PolyExtTable.parse(mutate("op\t2\tSub\t0,1" -> "op\t2\tSub\t0,2").iterator).isLeft shouldBe true
    // AndEqz referencing a mix var that is not pushed yet.
    PolyExtTable.parse(mutate("op\t4\tAndEqz\t0,2" -> "op\t4\tAndEqz\t1,2").iterator).isLeft shouldBe true
    // Unknown mnemonic.
    PolyExtTable.parse(mutate("op\t0\tConst\t5" -> "op\t0\tFrobnicate\t5").iterator).isLeft shouldBe true
    // Non-numeric operand.
    PolyExtTable.parse(mutate("op\t0\tConst\t5" -> "op\t0\tConst\tx").iterator).isLeft shouldBe true
    // Out-of-order op index.
    PolyExtTable.parse(mutate("op\t1\tConst\t5" -> "op\t9\tConst\t5").iterator).isLeft shouldBe true
    // Truncated table: meta counts no longer match.
    PolyExtTable.parse(tinyTable.dropRight(1).iterator).isLeft shouldBe true
    // ret not the last mix var.
    PolyExtTable.parse(mutate("meta\tret\t1" -> "meta\tret\t0").iterator).isLeft shouldBe true
    // Histogram mismatch.
    PolyExtTable.parse(
      mutate("meta\topcode_histogram\tAndEqz=1,Const=2,Sub=1,True=1" ->
        "meta\topcode_histogram\tAndEqz=1,Const=1,Sub=2,True=1").iterator).isLeft shouldBe true
  }

  test("interpreter rejects out-of-range taps and globals with Left, never throws") {
    val polyMix = Ext4(1, 2, 3, 4)
    val okArgs = Array(new Array[Int](32), new Array[Int](20))
    // Real table, u too short for its Get ops.
    PolyExtInterpreter.step(opsTable, polyMix, Array.empty[Ext4], okArgs).isLeft shouldBe true
    val u = Array.fill(tapSet.tapSize)(Ext4.Zero)
    // Missing mix-globals buffer.
    PolyExtInterpreter.step(opsTable, polyMix, u, Array(new Array[Int](32))).isLeft shouldBe true
    // Mix-globals buffer too short.
    PolyExtInterpreter.step(opsTable, polyMix, u, Array(new Array[Int](32), new Array[Int](19))).isLeft shouldBe true
    // Non-canonical global value.
    val badOut = new Array[Int](32); badOut(0) = 2013265921
    PolyExtInterpreter.step(opsTable, polyMix, u, Array(badOut, new Array[Int](20))).isLeft shouldBe true
    // All-zero canonical inputs are structurally fine and must evaluate.
    PolyExtInterpreter.step(opsTable, polyMix, u, okArgs).isRight shouldBe true
  }

  test("taps and params loaders reject malformed rows with Left, never throw") {
    val tapLines = rawLines("/stark-kats/circuit_taps.tsv")
    // Offset outside the group's column count.
    CircuitTapSet.parse(tapLines.map(l =>
      if (l == "tap\t16\t1\t0\t0\t0\t1") "tap\t16\t1\t23\t0\t0\t1" else l).iterator).isLeft shouldBe true
    // Broken register run (skip overrun at the last tap).
    CircuitTapSet.parse(tapLines.map(l =>
      if (l.startsWith("tap\t642\t")) l.dropRight(1) + "9" else l).iterator).isLeft shouldBe true
    // Dropped tap: group_begin no longer matches.
    CircuitTapSet.parse(tapLines.filterNot(_.startsWith("tap\t642\t")).iterator).isLeft shouldBe true

    val paramLines = rawLines("/stark-kats/circuit_params.tsv")
    // Dropped control id: count mismatch.
    CircuitParams.parse(paramLines.filterNot(_.startsWith("control_id\t26\t")).iterator).isLeft shouldBe true
    // Truncated root digest.
    CircuitParams.parse(paramLines.map(l =>
      if (l.startsWith("param\tallowed_control_root\t")) l.dropRight(1) else l).iterator).isLeft shouldBe true
    // Missing required int param.
    CircuitParams.parse(paramLines.filterNot(_.startsWith("param\tqueries\t")).iterator).isLeft shouldBe true
  }
}
