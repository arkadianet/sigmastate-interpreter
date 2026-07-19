package sigma.stark.receipt

import java.nio.charset.StandardCharsets

/** SHA-256 "tagged struct" digests of RISC0 receipt claims — the claim/journal
  * binding side of the EIP-0045 `verifyStark` succinct profile.
  *
  * Faithful port of risc0-binfmt 1.2.6 `hash.rs` (`tagged_struct`,
  * `tagged_list`, `Digestible for Option/[u8]`) and `sys_state.rs`
  * (`SystemState::digest`), plus the `Digestible` impls of the zkVerify
  * verifier crate's `receipt_claim.rs` (v0.11.0, the exact crate the Rust
  * Ergo node links): `ReceiptClaim`, `Output`, `Assumption(s)`, `MaybePruned`
  * and `ExitCode::into_pair` (risc0-binfmt `exit_code.rs:64-71` — note
  * `SessionLimit -> (2, 2)`).
  *
  * The hash function is injected (`Array[Byte] => Array[Byte]`, plain
  * SHA-256) because core/shared cross-compiles to Scala.js where
  * `java.security.MessageDigest` does not exist; JVM callers pass
  * `MessageDigest.getInstance("SHA-256").digest _`. No hashing is
  * hand-rolled here.
  *
  * All functions are TOTAL over parsed receipt values: [[InnerReceipt.parse]]
  * already rejects every byte pattern these functions cannot digest (e.g. a
  * present `Input`, which is uninhabited upstream), so no error channel is
  * needed and nothing throws.
  *
  * Correctness is pinned by the claim-binding checkpoints of the REAL devnet
  * receipt's recorded transcript (`stark-kats/transcript_capture.tsv`:
  * `journal_sha256`, `post_system_state_digest`, `output_digest`,
  * `claim_digest`, `expected_claim_digest`), per the oracle-parity rule.
  */
object ClaimDigest {

  /** Plain SHA-256 over a byte string (the only primitive this scheme needs). */
  type Sha256 = Array[Byte] => Array[Byte]

  /** `Digest::ZERO` — 32 zero bytes. Callers must not mutate. */
  private val ZeroDigest: Array[Byte] = new Array[Byte](32)

  /** Serialized form of a wire [[Digest]]: the 8 u32 words in little-endian
    * byte order (risc0 `Digest::as_bytes`, the same order [[Digest.toHex]]
    * prints).
    */
  def digestBytes(d: Digest): Array[Byte] = {
    val out = new Array[Byte](32)
    var i = 0
    while (i < 8) {
      val w = d.words(i)
      out(4 * i) = (w & 0xFF).toByte
      out(4 * i + 1) = ((w >>> 8) & 0xFF).toByte
      out(4 * i + 2) = ((w >>> 16) & 0xFF).toByte
      out(4 * i + 3) = ((w >>> 24) & 0xFF).toByte
      i += 1
    }
    out
  }

  /** risc0-binfmt `tagged_struct`:
    * `sha256( sha256(tag) ‖ down_0 ‖ … ‖ down_{n-1} ‖ data words LE ‖ n as u16 LE )`.
    * `data` entries are u32s held as raw `Int` bits.
    */
  def taggedStruct(sha256: Sha256, tag: String, down: Seq[Array[Byte]], data: Seq[Int]): Array[Byte] = {
    val tagDigest = sha256(tag.getBytes(StandardCharsets.UTF_8))
    val buf = new java.io.ByteArrayOutputStream(32 * (down.length + 1) + 4 * data.length + 2)
    buf.write(tagDigest, 0, tagDigest.length)
    down.foreach(d => buf.write(d, 0, d.length))
    data.foreach { w =>
      buf.write(w & 0xFF)
      buf.write((w >>> 8) & 0xFF)
      buf.write((w >>> 16) & 0xFF)
      buf.write((w >>> 24) & 0xFF)
    }
    // down_count as u16 LE. Parsed receipts can never reach 2^16 digests
    // (upstream try_into::<u16>() would panic first; our callers pass fixed
    // small lists and per-assumption cons cells).
    buf.write(down.length & 0xFF)
    buf.write((down.length >>> 8) & 0xFF)
    sha256(buf.toByteArray)
  }

  /** `SystemState::digest`: `tagged_struct("risc0.SystemState", [merkle_root], [pc])`. */
  def systemStateDigest(sha256: Sha256, s: SystemState): Array[Byte] =
    taggedStruct(sha256, "risc0.SystemState", Seq(digestBytes(s.merkleRoot)), Seq(s.pc))

  /** `Assumption::digest`: `tagged_struct("risc0.Assumption", [claim, control_root], [])`. */
  def assumptionDigest(sha256: Sha256, a: Assumption): Array[Byte] =
    taggedStruct(sha256, "risc0.Assumption",
      Seq(digestBytes(a.claim), digestBytes(a.controlRoot)), Seq.empty)

  /** `Assumptions::digest`: `tagged_list("risc0.Assumptions", item digests)` —
    * a right fold from `Digest::ZERO` of
    * `tagged_struct(tag, [head, tail], [])` cons cells (risc0-binfmt
    * `hash.rs:94-109`); the empty list digests to zero.
    */
  def assumptionsDigest(sha256: Sha256, as: Assumptions): Array[Byte] =
    as.items.foldRight(ZeroDigest) { (item, tail) =>
      val head = item match {
        case MaybePruned.Value(a)  => assumptionDigest(sha256, a)
        case MaybePruned.Pruned(d) => digestBytes(d)
      }
      taggedStruct(sha256, "risc0.Assumptions", Seq(head, tail), Seq.empty)
    }

  /** `Output::digest`: `tagged_struct("risc0.Output", [journal, assumptions], [])`;
    * a journal value digests as plain `sha256(bytes)` (risc0-binfmt
    * `Digestible for [u8]`).
    */
  def outputDigest(sha256: Sha256, o: Output): Array[Byte] = {
    val journal = o.journal match {
      case MaybePruned.Value(bytes) => sha256(bytes)
      case MaybePruned.Pruned(d)    => digestBytes(d)
    }
    val assumptions = o.assumptions match {
      case MaybePruned.Value(as) => assumptionsDigest(sha256, as)
      case MaybePruned.Pruned(d) => digestBytes(d)
    }
    taggedStruct(sha256, "risc0.Output", Seq(journal, assumptions), Seq.empty)
  }

  /** `ExitCode::into_pair` (risc0-binfmt `exit_code.rs:64-71`). */
  def exitCodePair(e: ExitCode): (Int, Int) = e match {
    case ExitCode.Halted(user) => (0, user)
    case ExitCode.Paused(user) => (1, user)
    case ExitCode.SystemSplit  => (2, 0)
    case ExitCode.SessionLimit => (2, 2)
  }

  /** `ReceiptClaim::digest`:
    * `tagged_struct("risc0.ReceiptClaim", [input, pre, post, output], [sys_exit, user_exit])`.
    * `Option` fields digest as the value's digest or `Digest::ZERO` when
    * `None` (risc0-binfmt `Digestible for Option`).
    */
  def receiptClaimDigest(sha256: Sha256, c: ReceiptClaim): Array[Byte] = {
    val (sysExit, userExit) = exitCodePair(c.exitCode)
    val input = c.input match {
      // `Input` is uninhabited (and the parser rejects a present one), so a
      // parsed Value is always None.
      case MaybePruned.Value(_)  => ZeroDigest
      case MaybePruned.Pruned(d) => digestBytes(d)
    }
    val pre = c.pre match {
      case MaybePruned.Value(s)  => systemStateDigest(sha256, s)
      case MaybePruned.Pruned(d) => digestBytes(d)
    }
    val post = c.post match {
      case MaybePruned.Value(s)  => systemStateDigest(sha256, s)
      case MaybePruned.Pruned(d) => digestBytes(d)
    }
    val output = c.output match {
      case MaybePruned.Value(Some(o)) => outputDigest(sha256, o)
      case MaybePruned.Value(None)    => ZeroDigest
      case MaybePruned.Pruned(d)      => digestBytes(d)
    }
    taggedStruct(sha256, "risc0.ReceiptClaim", Seq(input, pre, post, output), Seq(sysExit, userExit))
  }

  /** Digest of a receipt's possibly pruned claim (`MaybePruned::digest`). */
  def claimDigest(sha256: Sha256, claim: MaybePruned[ReceiptClaim]): Array[Byte] = claim match {
    case MaybePruned.Value(c)  => receiptClaimDigest(sha256, c)
    case MaybePruned.Pruned(d) => digestBytes(d)
  }

  /** Digest of the EXPECTED claim of a successful execution —
    * `ReceiptClaim::ok(image_id, Pruned(journal_digest))` (zkVerify
    * `receipt_claim.rs:74-92` / `receipt.rs:86`): `pre = Pruned(image_id)`,
    * `post = SystemState { pc: 0, merkle_root: ZERO }`,
    * `exit_code = Halted(0)`, `input = None`,
    * `output = Some(Output { journal: Pruned(journal_digest),
    * assumptions: Pruned(ZERO) })`.
    *
    * `imageId32` must be 32 bytes (caller-validated); `journalDigest` is
    * `sha256(journal bytes)`.
    */
  def expectedOkClaimDigest(sha256: Sha256, imageId32: Array[Byte], journalDigest: Array[Byte]): Array[Byte] = {
    val post = taggedStruct(sha256, "risc0.SystemState", Seq(ZeroDigest), Seq(0))
    val output = taggedStruct(sha256, "risc0.Output", Seq(journalDigest, ZeroDigest), Seq.empty)
    taggedStruct(sha256, "risc0.ReceiptClaim", Seq(ZeroDigest, imageId32, post, output), Seq(0, 0))
  }
}
