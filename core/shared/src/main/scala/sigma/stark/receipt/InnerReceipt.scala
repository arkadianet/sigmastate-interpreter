package sigma.stark.receipt

import scala.util.control.NonFatal

/** A 256-bit RISC0 digest: 8 u32 words held as raw `Int` bits (unsigned value
  * of word `i` = `words(i) & 0xFFFFFFFFL`). The serialized form (and
  * [[toHex]]) is the 32 bytes of the words in little-endian order — the same
  * byte order risc0's own `Digest` Display uses, so hex here compares
  * directly against the oracle dump.
  */
final case class Digest(words: Array[Int]) {
  override def equals(other: Any): Boolean = other match {
    case that: Digest => java.util.Arrays.equals(words, that.words)
    case _            => false
  }
  override def hashCode(): Int = java.util.Arrays.hashCode(words)

  def toHex: String = {
    val sb = new StringBuilder(64)
    var i = 0
    while (i < words.length) {
      val w = words(i)
      var b = 0
      while (b < 4) {
        sb.append("%02x".format((w >>> (8 * b)) & 0xFF))
        b += 1
      }
      i += 1
    }
    sb.toString
  }
  override def toString: String = s"Digest(${toHex})"
}

/** Mirror of risc0's `MaybePruned<T>`: either the full value or a digest
  * committing to it (bincode enum: u32 tag 0 = Value, 1 = Pruned).
  */
sealed trait MaybePruned[+T]
object MaybePruned {
  final case class Value[+T](value: T) extends MaybePruned[T]
  final case class Pruned(digest: Digest) extends MaybePruned[Nothing]
}

/** Mirror of risc0-binfmt's `SystemState`. `pc` is a u32 held as raw `Int`
  * bits (unsigned value = `pc & 0xFFFFFFFFL`).
  */
final case class SystemState(pc: Int, merkleRoot: Digest)

/** Mirror of risc0-binfmt's `ExitCode` (bincode enum: u32 tag 0..3; Halted
  * and Paused carry a u32 user exit code, held as raw `Int` bits).
  */
sealed trait ExitCode
object ExitCode {
  final case class Halted(user: Int) extends ExitCode
  final case class Paused(user: Int) extends ExitCode
  case object SystemSplit extends ExitCode
  case object SessionLimit extends ExitCode
}

/** Mirror of risc0's `Input` — deliberately uninhabited (the Rust type has an
  * uninhabited private field), so a receipt whose bytes claim a present input
  * value is malformed and rejected at parse time, exactly as Rust serde does.
  */
sealed trait Input

/** Mirror of risc0's `Assumption`: a claim digest and the control root that
  * can resolve it.
  */
final case class Assumption(claim: Digest, controlRoot: Digest)

/** Mirror of risc0's `Assumptions` (a newtype over the list). */
final case class Assumptions(items: Vector[MaybePruned[Assumption]])

/** Mirror of risc0's `Output`: the journal and the assumptions made while
  * proving it.
  */
final case class Output(
    journal: MaybePruned[Array[Byte]],
    assumptions: MaybePruned[Assumptions]
)

/** Mirror of risc0's `ReceiptClaim` — the public statement a receipt proves. */
final case class ReceiptClaim(
    pre: MaybePruned[SystemState],
    post: MaybePruned[SystemState],
    exitCode: ExitCode,
    input: MaybePruned[Option[Input]],
    output: MaybePruned[Option[Output]]
)

/** Mirror of risc0's control-ID `MerkleProof`. `index` is a u32 held as raw
  * `Int` bits.
  */
final case class MerkleProof(index: Int, digests: Vector[Digest])

/** Mirror of risc0's `SuccinctReceipt<ReceiptClaim>` — the seal (STARK proof
  * of the recursion circuit) plus the claim it attests to.
  *
  * `seal` holds u32 words as raw `Int` bits (unsigned value of word `i` =
  * `seal(i) & 0xFFFFFFFFL`); note that `Array` fields make the default case
  * class equality reference-based — compare fields explicitly where needed.
  */
final case class SuccinctReceipt(
    seal: Array[Int],
    controlId: Digest,
    claim: MaybePruned[ReceiptClaim],
    hashfn: String,
    verifierParameters: Digest,
    controlInclusionProof: MerkleProof
)

/** Mirror of risc0's `InnerReceipt` enum, restricted to what the EIP-0045
  * `verifyStark` succinct profile accepts: only the `Succinct` variant parses;
  * `Composite` (variant 0) is recognized and rejected with a clear message.
  *
  * Wire format: bincode 1.x legacy/DEFAULT config — see [[BincodeReader]].
  * Parsing is TOTAL: [[InnerReceipt.parse]] returns `Left` on any malformed
  * input and never throws (a consensus verifier must reject, not crash);
  * every length is capped by the remaining input before allocation.
  *
  * The structure and every reject vector are pinned against an external
  * oracle — `risc0_verifier` + `bincode` themselves, captured by
  * `stark-kat/src/bin/receipt_dump.rs` into
  * `core/jvm/src/test/resources/stark-kats/receipt_struct.tsv` — never
  * against this code (oracle-parity rule).
  */
sealed trait InnerReceipt
object InnerReceipt {
  final case class Succinct(receipt: SuccinctReceipt) extends InnerReceipt

  /** Parse a bincode-serialized `InnerReceipt`.
    *
    * Trailing bytes after a complete receipt are ACCEPTED, mirroring the Rust
    * oracle: bincode 1.x's legacy `bincode::deserialize` (what risc0 /
    * risc0-verifier and the Rust Ergo node use) is configured with
    * `allow_trailing_bytes` — recorded as `trailing_bytes_allowed` in the
    * oracle dump. Being stricter here would be a consensus split against the
    * Rust node.
    */
  def parse(bytes: Array[Byte]): Either[String, InnerReceipt] =
    if (bytes == null) Left("null input")
    else {
      try {
        val r = new BincodeReader(bytes)
        val tag = r.u32("InnerReceipt variant tag")
        if (tag == 1) Right(Succinct(parseSuccinct(r)))
        else if (tag == 0)
          Left("InnerReceipt::Composite is not supported by the succinct verifyStark profile")
        else Left(s"invalid InnerReceipt variant tag ${tag & 0xFFFFFFFFL}")
      } catch {
        case e: BincodeReader.ParseException => Left(e.getMessage)
        case NonFatal(e) => Left(s"unexpected parse failure: $e")
      }
    }

  private def parseSuccinct(r: BincodeReader): SuccinctReceipt = {
    val sealLen = r.length("seal", 4)
    val seal = new Array[Int](sealLen)
    var i = 0
    while (i < sealLen) {
      seal(i) = r.u32("seal word")
      i += 1
    }
    val controlId = digest(r, "control_id")
    val claim = maybePruned(r, "claim")(parseReceiptClaim)
    val hashfn = r.string("hashfn")
    val verifierParameters = digest(r, "verifier_parameters")
    val proof = parseMerkleProof(r)
    SuccinctReceipt(seal, controlId, claim, hashfn, verifierParameters, proof)
  }

  private def digest(r: BincodeReader, what: String): Digest = {
    val words = new Array[Int](8)
    var i = 0
    while (i < 8) {
      words(i) = r.u32(what)
      i += 1
    }
    Digest(words)
  }

  private def maybePruned[T](r: BincodeReader, what: String)(
      value: BincodeReader => T): MaybePruned[T] =
    r.u32(s"$what MaybePruned tag") match {
      case 0 => MaybePruned.Value(value(r))
      case 1 => MaybePruned.Pruned(digest(r, s"$what pruned digest"))
      case t => r.fail(s"invalid $what MaybePruned tag ${t & 0xFFFFFFFFL}")
    }

  private def option[T](r: BincodeReader, what: String)(
      value: BincodeReader => T): Option[T] =
    r.u8(s"$what Option tag") match {
      case 0 => None
      case 1 => Some(value(r))
      case t => r.fail(s"invalid $what Option tag $t")
    }

  private def parseReceiptClaim(r: BincodeReader): ReceiptClaim = {
    val pre = maybePruned(r, "pre")(parseSystemState)
    val post = maybePruned(r, "post")(parseSystemState)
    val exitCode = parseExitCode(r)
    val input = maybePruned(r, "input") { rr =>
      option[Input](rr, "input")(_.fail("Input is uninhabited but present"))
    }
    val output = maybePruned(r, "output") { rr =>
      option(rr, "output")(parseOutput)
    }
    ReceiptClaim(pre, post, exitCode, input, output)
  }

  private def parseSystemState(r: BincodeReader): SystemState =
    SystemState(r.u32("pc"), digest(r, "merkle_root"))

  private def parseExitCode(r: BincodeReader): ExitCode =
    r.u32("ExitCode variant tag") match {
      case 0 => ExitCode.Halted(r.u32("Halted user exit code"))
      case 1 => ExitCode.Paused(r.u32("Paused user exit code"))
      case 2 => ExitCode.SystemSplit
      case 3 => ExitCode.SessionLimit
      case t => r.fail(s"invalid ExitCode variant tag ${t & 0xFFFFFFFFL}")
    }

  private def parseOutput(r: BincodeReader): Output = {
    val journal = maybePruned(r, "journal") { rr =>
      val n = rr.length("journal", 1)
      rr.bytesExact(n, "journal")
    }
    val assumptions = maybePruned(r, "assumptions") { rr =>
      // Minimum serialized size of MaybePruned[Assumption] = 4 (tag) + 32.
      val n = rr.length("assumptions", 36)
      val items = Vector.newBuilder[MaybePruned[Assumption]]
      var i = 0
      while (i < n) {
        items += maybePruned(rr, "assumption") { r3 =>
          Assumption(digest(r3, "assumption claim"), digest(r3, "assumption control_root"))
        }
        i += 1
      }
      Assumptions(items.result())
    }
    Output(journal, assumptions)
  }

  private def parseMerkleProof(r: BincodeReader): MerkleProof = {
    val index = r.u32("merkle index")
    val n = r.length("merkle digests", 32)
    val digests = Vector.newBuilder[Digest]
    var i = 0
    while (i < n) {
      digests += digest(r, "merkle digest")
      i += 1
    }
    MerkleProof(index, digests.result())
  }
}
