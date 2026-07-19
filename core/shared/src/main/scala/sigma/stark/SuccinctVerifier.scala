package sigma.stark

import sigma.stark.circuit.{CircuitParams, CircuitTapSet, PolyExtInterpreter, PolyExtTable}
import sigma.stark.receipt.{ClaimDigest, InnerReceipt, MerkleProof, SuccinctReceipt}

import BabyBear.{fromRaw, mul => fmul, toRaw}

/** Full verifier for RISC0 SUCCINCT receipts — the EIP-0045 `verifyStark`
  * top-level flow: `verify(receiptBytes, journalBytes, imageId32)` accepts
  * exactly when `risc0_verifier::verify(&v3_0(), image_id, proof, journal)`
  * (zkVerify v0.11.0, the crate the Rust Ergo node links) accepts.
  *
  * Pipeline, mirroring the Rust call graph
  * (`RV` = risc0-verifier v0.11.0 sources, `ZKP` = risc0-zkp 3.0.4):
  *
  *  1. bincode parse of `InnerReceipt` ([[InnerReceipt.parse]]); only the
  *     `Succinct` arm is admitted, and the receipt's `hashfn` must name the
  *     pinned `poseidon2` suite (`RV/context/v3.rs:120-123` suite lookup —
  *     profile-pinned here, rejecting blake2b/sha-256).
  *  2. The STARK core (`ZKP/verify/mod.rs:495-556` `verify`): Fiat-Shamir
  *     seeding with the protocol/circuit info strings, `out`+po2 slice,
  *     group Merkle commits in CODE / DATA / ACCUM order with the 20
  *     accum-mix draws between DATA and ACCUM, the control-inclusion
  *     `check_code` callback after CODE, then `verify_validity`
  *     (`ZKP/verify/mod.rs:280-447`): poly_mix, check-poly Merkle, z,
  *     coeff_u read+commit, per-register `eval_u` at `z * back_one^back`,
  *     the constraint-program evaluation ([[PolyExtInterpreter]]), the
  *     `remap [0,2,1,3]` check-polynomial recombination times
  *     `(3z)^tot_cycles - 1`, the DEEP-ALI `combo_u` fold, FRI
  *     ([[FriVerifier]]) with the per-query `fri_eval_taps` opening, and the
  *     final `verify_complete` full-consumption check.
  *  3. Control-root binding (`RV/receipt/succinct.rs:123-150`): the
  *     Poseidon2 control root recovered from the even slots of
  *     `out[0..16)` must equal the profile's `ALLOWED_CONTROL_ROOT`.
  *  4. Claim binding (`RV/receipt/succinct.rs:153-161` + `RV/receipt.rs:86-97`):
  *     the SHA-256 half-word digest in `out[16..32)` must equal the parsed
  *     claim's tagged-struct digest ([[ClaimDigest]]), which must equal the
  *     digest of `ReceiptClaim::ok(imageId, Pruned(sha256(journal)))`.
  *
  * Wire-form conventions follow [[ReadIop]] / [[MerkleVerifier]] (canonical
  * values inside, RAW Montgomery digest words at hash/commit boundaries).
  * Two deliberate subtleties, each traced to the Rust flow:
  *
  *  - po2 is the RAW wire word of the 33rd out-slice element
  *    (`ZKP/verify/mod.rs:454-475` takes `po2_elem.to_u32_words()[0]`, which
  *    is the undecoded Montgomery representation word — risc0-core 3.0.1
  *    `baby_bear.rs:146-148`), recovered here as `toRaw(canonical)`.
  *  - the control-inclusion walk (`RV/receipt/merkle.rs:55-67`) hashes
  *    sibling digests via `Elem::new_raw`, which accepts ANY u32 word and
  *    reduces it implicitly (an unreduced `w + P` encodes the same element),
  *    so sibling words are reduced mod P here instead of being rejected —
  *    rejecting them would split from the Rust node on such (otherwise
  *    valid) receipts.
  *
  * Total: `Left` on any malformed or non-verifying input, never throws.
  * Construction wants the three loader-validated circuit tables (parsed once
  * at startup from `stark-kats/`-shaped data) and an injected SHA-256
  * (core/shared cross-compiles to Scala.js, where
  * `java.security.MessageDigest` does not exist; JVM callers pass
  * `MessageDigest.getInstance("SHA-256").digest _`).
  *
  * Correctness is pinned by the recorded accepting transcript of the REAL
  * devnet receipt and the oracle-confirmed reject mutations
  * (`stark-kats/transcript_capture.tsv`, `receipt_kat.json`), per the
  * oracle-parity rule.
  */
final class SuccinctVerifier(
    params: CircuitParams,
    taps: CircuitTapSet,
    polyExt: PolyExtTable,
    sha256: ClaimDigest.Sha256) {
  import SuccinctVerifier._

  require(params.hashfn == "poseidon2",
    s"profile pins the poseidon2 suite, params say '${params.hashfn}'")
  require(params.extSize == 4, s"ext_size ${params.extSize} != 4 (Ext4 profile)")

  /** `ALLOWED_CONTROL_ROOT` as RAW digest words. */
  private val allowedControlRoot: Array[Int] = hexToWords(params.allowedControlRoot)

  private val proofSystemDigest: Array[Int] = protocolInfoDigestRaw(params.proofSystemInfo)
  private val circuitDigest: Array[Int] = protocolInfoDigestRaw(params.circuitInfo)

  /** Verify a succinct receipt against a journal and a 32-byte image id.
    * `Right(())` iff the Rust reference verifier accepts the same triple.
    */
  def verify(receiptBytes: Array[Byte], journalBytes: Array[Byte], imageId32: Array[Byte]): Either[String, Unit] =
    verify(receiptBytes, journalBytes, imageId32, NoProbe)

  /** [[verify]] with a checkpoint probe (test instrumentation; the default
    * [[SuccinctVerifier.NoProbe]] does nothing).
    */
  def verify(
      receiptBytes: Array[Byte],
      journalBytes: Array[Byte],
      imageId32: Array[Byte],
      probe: Probe): Either[String, Unit] = {
    if (imageId32 == null || imageId32.length != 32)
      return Left("image id must be exactly 32 bytes")
    if (journalBytes == null) return Left("null journal")
    InnerReceipt.parse(receiptBytes) match {
      case Left(e) => Left(s"receipt parse: $e")
      case Right(InnerReceipt.Succinct(r)) =>
        verifySuccinct(r, journalBytes, imageId32, probe)
    }
  }

  // --------------------------------------------------------------------
  // Receipt-level flow (RV/receipt/succinct.rs + RV/receipt.rs)
  // --------------------------------------------------------------------

  private def verifySuccinct(
      r: SuccinctReceipt,
      journalBytes: Array[Byte],
      imageId32: Array[Byte],
      probe: Probe): Either[String, Unit] = {
    // Suite selection by the receipt's hashfn string; only the pinned
    // poseidon2 profile is admitted (RV/context/v3.rs:120-123).
    if (r.hashfn != params.hashfn)
      return Left(s"unsupported hash suite '${r.hashfn}' (profile pins '${params.hashfn}')")

    val out = starkVerify(r.seal, r.controlInclusionProof, probe) match {
      case Left(e)  => return Left(e)
      case Right(o) => o
    }

    // Control root from the even slots of out[0..16) (Poseidon2 digests are
    // encoded interspersed with padding; RV/receipt/succinct.rs:129-150).
    // Word equality mirrors the Rust Digest compare; inner_control_root is
    // None in the pinned v3_0 profile, so the target is the allowed root.
    val sealControlRoot = new Array[Int](8)
    var i = 0
    while (i < 8) { sealControlRoot(i) = out(2 * i); i += 1 }
    probe.onCheckpoint("seal_control_root", sealControlRoot)
    if (!java.util.Arrays.equals(sealControlRoot, allowedControlRoot))
      return Left("seal control root does not match the allowed control root")

    // Output claim digest as 16 SHA half-words in out[16..32)
    // (risc0-binfmt sys_state.rs:77-91 read_sha_halfs: each half must fit
    // 16 bits).
    val outputHash = new Array[Byte](32)
    i = 0
    while (i < 16) {
      val half = out(16 + i)
      if ((half >>> 8) > 0xFF)
        return Left(s"seal output half-word $i out of range: $half")
      outputHash(2 * i) = (half & 0xFF).toByte
      outputHash(2 * i + 1) = ((half >>> 8) & 0xFF).toByte
      i += 1
    }
    probe.onCheckpoint("seal_output_hash_bytes", outputHash.map(_ & 0xFF))

    // The seal's output slot must bind the receipt's claim
    // (RV/receipt/succinct.rs:153-161)...
    val claimDig = ClaimDigest.claimDigest(sha256, r.claim)
    if (!java.util.Arrays.equals(outputHash, claimDig))
      return Left("seal output hash does not match the receipt claim digest")

    // ...and the claim must be exactly the successful execution of imageId
    // over this journal (RV/receipt.rs:86-97).
    val expected =
      ClaimDigest.expectedOkClaimDigest(sha256, imageId32, sha256(journalBytes))
    if (!java.util.Arrays.equals(expected, claimDig))
      return Left("claim digest does not match the expected image id + journal claim")

    Right(())
  }

  // --------------------------------------------------------------------
  // STARK core (ZKP/verify/mod.rs verify + verify_validity)
  // --------------------------------------------------------------------

  /** Run the seal through the fixed IOP protocol; `Right(out)` returns the
    * 32 canonical out globals on acceptance.
    */
  private def starkVerify(
      seal: Array[Int],
      inclusion: MerkleProof,
      probe: Probe): Either[String, Array[Int]] = {
    if (seal.length == 0) return Left("empty seal")
    probe.onCheckpoint("seal_words", Array(seal.length))

    val iop = new ReadIop(seal)
    // Seed the transcript with the proof-system and circuit info strings
    // (ZKP/verify/mod.rs:185-194).
    iop.commit(proofSystemDigest)
    iop.commit(circuitDigest)

    // read_slice_with_po2(OUTPUT_SIZE): 33 elems, commit their hash; po2 is
    // the raw wire word of the last element (see class scaladoc).
    val slice = iop.readFieldElemSlice(params.outputSize + 1) match {
      case None    => return Left("seal too short for out globals")
      case Some(s) => s
    }
    iop.commit(Poseidon2.unpaddedHash(slice).map(toRaw))
    val out = java.util.Arrays.copyOfRange(slice, 0, params.outputSize)
    val po2 = toRaw(slice(params.outputSize))
    if (po2 > params.maxCyclesPo2)
      return Left(s"po2 $po2 exceeds max ${params.maxCyclesPo2}")
    val totCycles = 1 << po2
    val domain = params.invRate * totCycles
    probe.onCheckpoint("po2", Array(po2))
    probe.onCheckpoint("tot_cycles", Array(totCycles))
    probe.onCheckpoint("domain", Array(domain))
    probe.onCheckpoint("out", out)

    // Group Merkle commits in protocol order; group ids are 0=accum 1=code
    // 2=data (ZKP/adapter.rs:27-29), read CODE, DATA, ACCUM
    // (ZKP/verify/mod.rs:518-546).
    val codeMerkle = MerkleVerifier.create(iop, domain, taps.groupSize(1), params.queries) match {
      case Left(e)  => return Left(s"code group: $e")
      case Right(m) => m
    }
    probe.onCheckpoint("group_root code", codeMerkle.rootRaw)

    // check_code: the code root IS the control id of the recursion program;
    // its inclusion in the allowed set is proven against the control root.
    probe.onCheckpoint("control_id_included", codeMerkle.rootRaw)
    controlInclusion(codeMerkle.rootRaw, inclusion) match {
      case Left(e)  => return Left(e)
      case Right(_) => ()
    }

    val dataMerkle = MerkleVerifier.create(iop, domain, taps.groupSize(2), params.queries) match {
      case Left(e)  => return Left(s"data group: $e")
      case Right(m) => m
    }
    probe.onCheckpoint("group_root data", dataMerkle.rootRaw)

    // Accum-mix globals: MIX_SIZE plain transcript draws (read_rng).
    val mixGlobals = new Array[Int](params.mixSize)
    var i = 0
    while (i < params.mixSize) { mixGlobals(i) = iop.randomElem(); i += 1 }
    probe.onCheckpoint("mix", mixGlobals)

    val accumMerkle = MerkleVerifier.create(iop, domain, taps.groupSize(0), params.queries) match {
      case Left(e)  => return Left(s"accum group: $e")
      case Right(m) => m
    }
    probe.onCheckpoint("group_root accum", accumMerkle.rootRaw)

    // ---- verify_validity (ZKP/verify/mod.rs:280-447) ----

    val polyMix = iop.randomExtElem()
    probe.onCheckpoint("poly_mix", extWords(polyMix))

    val checkMerkle = MerkleVerifier.create(iop, domain, params.checkSize, params.queries) match {
      case Left(e)  => return Left(s"check group: $e")
      case Right(m) => m
    }

    val z = iop.randomExtElem()
    probe.onCheckpoint("z", extWords(z))
    val backOne = FriVerifier.RouRev(po2)

    // coeff_u: (num_taps + CHECK_SIZE) ext elems, wire layout [c0,c1,c2,c3]
    // per element; commit the hash of the flattened elems
    // (hash_ext_elem_slice flat-maps subelems in that order).
    val numTaps = taps.tapSize
    val coeffWords = iop.readFieldElemSlice(4 * (numTaps + params.checkSize)) match {
      case None    => return Left("seal too short for coeff_u")
      case Some(s) => s
    }
    iop.commit(Poseidon2.unpaddedHash(coeffWords).map(toRaw))
    probe.onCheckpoint("coeff_u", coeffWords)
    val coeffU = new Array[Ext4](numTaps + params.checkSize)
    i = 0
    while (i < coeffU.length) {
      coeffU(i) = Ext4(coeffWords(4 * i), coeffWords(4 * i + 1), coeffWords(4 * i + 2), coeffWords(4 * i + 3))
      i += 1
    }

    // eval_u: per register, evaluate its coeff_u slice at z * back_one^back
    // for each of its backs (ZKP/verify/mod.rs:334-344).
    val evalU = new Array[Ext4](numTaps)
    var curPos = 0
    var k = 0
    var ri = 0
    while (ri < taps.regs.length) {
      val reg = taps.regs(ri)
      i = 0
      while (i < reg.size) {
        val x = scale(z, BabyBear.pow(backOne, reg.back(i).toLong))
        evalU(k) = polyEvalRange(coeffU, curPos, reg.size, x)
        k += 1
        i += 1
      }
      curPos += reg.size
      ri += 1
    }
    probe.onCheckpoint("eval_u", extArrayWords(evalU))

    // The mixed constraint polynomial: the circuit's op-table interpretation
    // over eval_u with the out/accum-mix globals (ZKP/verify/mod.rs:551).
    val result = PolyExtInterpreter.step(polyExt, polyMix, evalU, Array(out, mixGlobals)) match {
      case Left(e)   => return Left(s"constraint program: $e")
      case Right(ms) => ms.tot
    }
    probe.onCheckpoint("result", extWords(result))

    // Check-polynomial recombination with the [0,2,1,3] remap and basis
    // vectors, scaled by (3z)^tot_cycles - 1 (ZKP/verify/mod.rs:360-379).
    var check = Ext4.Zero
    var zi = Ext4.One
    i = 0
    while (i < 4) {
      val rmi = Remap(i)
      check = check +
        coeffU(numTaps + rmi) * zi +
        coeffU(numTaps + rmi + 4) * zi * Basis1 +
        coeffU(numTaps + rmi + 8) * zi * Basis2 +
        coeffU(numTaps + rmi + 12) * zi * Basis3
      zi = zi * z
      i += 1
    }
    check = check * (scale(z, 3).pow(BigInt(totCycles)) - Ext4.One)
    probe.onCheckpoint("check_value", extWords(check))
    if (check != result)
      return Left("constraint check failed: check polynomial != mixed constraints (invalid proof)")

    // DEEP-ALI batching: fold coeff_u into combo_u with powers of the FRI
    // batch mix (ZKP/verify/mod.rs:387-428).
    val friMix = iop.randomExtElem()
    probe.onCheckpoint("fri_batch_mix", extWords(friMix))
    val comboU = new Array[Ext4](taps.totComboBacks + 1)
    i = 0
    while (i < comboU.length) { comboU(i) = Ext4.Zero; i += 1 }
    val tapMixPows = new Array[Ext4](taps.regCount)
    val checkMixPows = new Array[Ext4](params.checkSize)
    var curMix = Ext4.One
    curPos = 0
    ri = 0
    while (ri < taps.regs.length) {
      val reg = taps.regs(ri)
      i = 0
      while (i < reg.size) {
        val idx = taps.comboBegin(reg.combo) + i
        comboU(idx) = comboU(idx) + curMix * coeffU(curPos + i)
        i += 1
      }
      tapMixPows(ri) = curMix
      curMix = curMix * friMix
      curPos += reg.size
      ri += 1
    }
    i = 0
    while (i < params.checkSize) {
      comboU(taps.totComboBacks) = comboU(taps.totComboBacks) + curMix * coeffU(curPos)
      curPos += 1
      checkMixPows(i) = curMix
      curMix = curMix * friMix
      i += 1
    }
    probe.onCheckpoint("combo_u", extArrayWords(comboU))

    // FRI over the same iop; each query opens one row of every group tree
    // (verifier index order 0=accum 1=code 2=data) plus the check tree and
    // computes the DEEP-ALI quotient sum (ZKP/verify/mod.rs:429-445).
    val gen = FriVerifier.RouFwd(FriVerifier.log2Ceil(domain))
    var qIdx = 0
    val inner: Int => Either[String, Ext4] = { idx =>
      probe.onCheckpoint("query", Array(qIdx, idx))
      qIdx += 1
      accumMerkle.verify(iop, idx) match {
        case Left(e) => Left(s"accum row: $e")
        case Right(accumRow) =>
          codeMerkle.verify(iop, idx) match {
            case Left(e) => Left(s"code row: $e")
            case Right(codeRow) =>
              dataMerkle.verify(iop, idx) match {
                case Left(e) => Left(s"data row: $e")
                case Right(dataRow) =>
                  checkMerkle.verify(iop, idx) match {
                    case Left(e) => Left(s"check row: $e")
                    case Right(checkRow) =>
                      Right(friEvalTaps(
                        comboU, checkRow, backOne, BabyBear.pow(gen, idx.toLong), z,
                        Array(accumRow, codeRow, dataRow), tapMixPows, checkMixPows))
                  }
              }
          }
      }
    }
    FriVerifier.friVerify(iop, totCycles, params.queries, inner) match {
      case Left(e)  => return Left(e)
      case Right(_) => ()
    }

    if (!iop.verifyComplete) return Left("trailing words in seal after verification")
    Right(out)
  }

  /** The FRI verify-taps sum — mirror of `ZKP/verify/mod.rs:234-273`
    * `fri_eval_taps`: per-combo numerators over the opened rows minus the
    * combo_u interpolations, divided by the DEEP-ALI vanishing factors, plus
    * the check-group term over `x - z^INV_RATE`.
    *
    * Division follows risc0-core's `inv` convention `inv(0) = 0`
    * (risc0-core 3.0.1 `baby_bear.rs:98-107` documents allowing it), so a
    * pathological zero divisor yields the same field value as the Rust
    * verifier instead of throwing.
    */
  private def friEvalTaps(
      comboU: Array[Ext4],
      checkRow: Array[Int],
      backOne: Int,
      xBase: Int,
      z: Ext4,
      rows: Array[Array[Int]],
      tapMixPows: Array[Ext4],
      checkMixPows: Array[Ext4]): Ext4 = {
    val comboCount = taps.combosCount
    val tot = new Array[Ext4](comboCount + 1)
    var f = 0
    while (f < tot.length) { tot(f) = Ext4.Zero; f += 1 }
    val x = Ext4.fromBase(xBase)

    var ri = 0
    while (ri < taps.regs.length) {
      val reg = taps.regs(ri)
      tot(reg.combo) = tot(reg.combo) + scale(tapMixPows(ri), rows(reg.group)(reg.offset))
      ri += 1
    }
    var i = 0
    while (i < params.checkSize) {
      tot(comboCount) = tot(comboCount) + scale(checkMixPows(i), checkRow(i))
      i += 1
    }

    var ret = Ext4.Zero
    var c = 0
    while (c < comboCount) {
      val begin = taps.comboBegin(c)
      val num = tot(c) - polyEvalRange(comboU, begin, taps.comboBegin(c + 1) - begin, x)
      var divisor = Ext4.One
      var t = begin
      while (t < taps.comboBegin(c + 1)) {
        divisor = divisor * (x - scale(z, BabyBear.pow(backOne, taps.comboTaps(t).toLong)))
        t += 1
      }
      ret = ret + num * invOrZero(divisor)
      c += 1
    }
    val checkNum = tot(comboCount) - comboU(taps.totComboBacks)
    val checkDiv = x - z.pow(BigInt(params.invRate))
    ret + checkNum * invOrZero(checkDiv)
  }

  // --------------------------------------------------------------------
  // Control-inclusion proof (RV/receipt/merkle.rs:39-68)
  // --------------------------------------------------------------------

  /** Walk the receipt's control-inclusion branch from the leaf (the code
    * root, i.e. the executed program's control id) to the allowed control
    * root, pairing by the index's bit parity. Sibling words are reduced mod
    * P at the hash boundary (see class scaladoc); the index is an u32 walked
    * with unsigned shifts and no range validation, exactly as upstream.
    */
  private def controlInclusion(leafRaw: Array[Int], proof: MerkleProof): Either[String, Unit] = {
    var cur = leafRaw.map(fromRaw)
    var idx = proof.index
    var d = 0
    while (d < proof.digests.length) {
      val sibling = proof.digests(d).words.map(reduceWide)
      cur =
        if ((idx & 1) == 0) Poseidon2.hashPair(cur, sibling)
        else Poseidon2.hashPair(sibling, cur)
      idx = idx >>> 1
      d += 1
    }
    if (java.util.Arrays.equals(cur.map(toRaw), allowedControlRoot)) Right(())
    else Left("control id is not in the allowed control set")
  }

  // --------------------------------------------------------------------
  // Small helpers
  // --------------------------------------------------------------------

  /** Digest of a 16-byte protocol info string as transcript seed:
    * `hash_elem_slice(info.encode())`, one canonical element per byte
    * (ZKP/adapter.rs:94-105), re-encoded RAW for the commit boundary.
    */
  private def protocolInfoDigestRaw(info: String): Array[Int] = {
    require(info.length == 16, s"protocol info must be 16 bytes: '$info'")
    val elems = info.getBytes(java.nio.charset.StandardCharsets.US_ASCII).map(_ & 0xFF)
    Poseidon2.unpaddedHash(elems).map(toRaw)
  }
}

object SuccinctVerifier {

  /** Test-instrumentation hook: [[SuccinctVerifier.verify]] reports each
    * intermediate pipeline value (labels match the `ck` checkpoints of
    * `stark-kats/transcript_capture.tsv` where one exists). Ext values are
    * flattened `[c0,c1,c2,c3]` canonical words; digests are RAW words;
    * `"seal_output_hash_bytes"` is 32 bytes as ints; `"query"` is
    * `[queryIndex, position]`. The default does nothing.
    */
  trait Probe {
    def onCheckpoint(label: String, values: Array[Int]): Unit = ()
  }

  /** The no-op probe used by the public entry point. */
  object NoProbe extends Probe

  /** The check-poly coefficient remap (ZKP/verify/mod.rs:361). */
  private val Remap: Array[Int] = Array(0, 2, 1, 3)

  /** Extension-field basis vectors x, x^2, x^3. */
  private val Basis1: Ext4 = Ext4(0, 1, 0, 0)
  private val Basis2: Ext4 = Ext4(0, 0, 1, 0)
  private val Basis3: Ext4 = Ext4(0, 0, 0, 1)

  /** `e * s` for a canonical base scalar (upstream `ExtElem * Elem`). */
  private def scale(e: Ext4, s: Int): Ext4 =
    Ext4(fmul(e.c0, s), fmul(e.c1, s), fmul(e.c2, s), fmul(e.c3, s))

  /** risc0-core inversion convention: `inv(0) = 0` (allowed upstream). */
  private def invOrZero(e: Ext4): Ext4 = if (e.isZero) Ext4.Zero else e.inv

  /** Evaluate `coeffs[off until off+len]` at `x` (ascending powers) —
    * upstream `Verifier::poly_eval` over a subslice.
    */
  private def polyEvalRange(coeffs: Array[Ext4], off: Int, len: Int, x: Ext4): Ext4 = {
    var mulX = Ext4.One
    var tot = Ext4.Zero
    var i = 0
    while (i < len) {
      tot = tot + (coeffs(off + i) * mulX)
      mulX = mulX * x
      i += 1
    }
    tot
  }

  /** Canonical value of an ARBITRARY u32 word read as a Montgomery residue —
    * upstream `Elem::new_raw` semantics, which reduce implicitly (`w` and
    * `w + P` encode the same element).
    */
  private def reduceWide(w: Int): Int =
    fromRaw(((w & 0xFFFFFFFFL) % BabyBear.P).toInt)

  private def extWords(e: Ext4): Array[Int] = Array(e.c0, e.c1, e.c2, e.c3)

  private def extArrayWords(es: Array[Ext4]): Array[Int] = {
    val out = new Array[Int](es.length * 4)
    var i = 0
    while (i < es.length) {
      out(4 * i) = es(i).c0
      out(4 * i + 1) = es(i).c1
      out(4 * i + 2) = es(i).c2
      out(4 * i + 3) = es(i).c3
      i += 1
    }
    out
  }

  /** Parse a 64-hex-char digest into its 8 RAW u32 words (little-endian
    * bytes per word — the same order `receipt.Digest.toHex` prints).
    * Verifier-configuration input, validated by the params loader; `require`
    * is appropriate here (not proof data).
    */
  private def hexToWords(hex: String): Array[Int] = {
    require(hex.length == 64, s"digest hex must be 64 chars: $hex")
    val out = new Array[Int](8)
    var i = 0
    while (i < 8) {
      var w = 0
      var b = 3
      while (b >= 0) {
        w = (w << 8) | Integer.parseInt(hex.substring(8 * i + 2 * b, 8 * i + 2 * b + 2), 16)
        b -= 1
      }
      out(i) = w
      i += 1
    }
    out
  }
}
