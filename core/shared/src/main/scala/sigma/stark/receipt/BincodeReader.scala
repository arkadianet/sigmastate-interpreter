package sigma.stark.receipt

import java.nio.charset.{CharacterCodingException, CodingErrorAction, StandardCharsets}
import java.nio.ByteBuffer

/** Minimal reader for the subset of bincode 1.x (legacy/DEFAULT config) that
  * the RISC0 `InnerReceipt` wire format uses, verified against the actual
  * fixture bytes by `stark-kat/src/bin/receipt_dump.rs` (its offset
  * arithmetic must account for every byte of the real receipt or it aborts):
  *
  *   - little-endian, FIXED-width integers (no varint),
  *   - enum variant index as u32,
  *   - `Vec<T>` / `String` as u64 element/byte count + payload,
  *   - `Option<T>` as a single 0/1 byte (+ payload),
  *   - `Digest` as a transparent newtype over `[u32; 8]` — exactly 32 bytes,
  *     NO length prefix (fixed-size array).
  *
  * Every read is bounds-checked and every length is capped by the remaining
  * input before any allocation, so attacker-controlled lengths cannot cause
  * unbounded allocation. Failures raise the private [[BincodeReader.ParseException]],
  * which `InnerReceipt.parse` converts to `Left` — no exception escapes the
  * public API.
  */
private[receipt] final class BincodeReader(bytes: Array[Byte]) {
  private var pos: Int = 0

  def remaining: Int = bytes.length - pos

  def fail(msg: String): Nothing =
    throw new BincodeReader.ParseException(s"$msg (at byte $pos of ${bytes.length})")

  private def need(n: Int, what: String): Unit =
    if (n > remaining) fail(s"truncated input: need $n more byte(s) for $what")

  /** One byte as an unsigned value in `[0, 255]`. */
  def u8(what: String): Int = {
    need(1, what)
    val b = bytes(pos) & 0xFF
    pos += 1
    b
  }

  /** Little-endian u32 as raw `Int` bits (unsigned value = `x & 0xFFFFFFFFL`). */
  def u32(what: String): Int = {
    need(4, what)
    val x = (bytes(pos) & 0xFF) |
      ((bytes(pos + 1) & 0xFF) << 8) |
      ((bytes(pos + 2) & 0xFF) << 16) |
      ((bytes(pos + 3) & 0xFF) << 24)
    pos += 4
    x
  }

  /** Little-endian u64 as raw `Long` bits (values >= 2^63 come out negative). */
  def u64(what: String): Long = {
    need(8, what)
    var x = 0L
    var i = 7
    while (i >= 0) {
      x = (x << 8) | (bytes(pos + i) & 0xFFL)
      i -= 1
    }
    pos += 8
    x
  }

  /** A u64 element count for `elemSize`-byte elements, validated against the
    * remaining input BEFORE any allocation: `count * elemSize` must fit in
    * what is left, so the returned value is always a safe `Int`.
    */
  def length(what: String, elemSize: Int): Int = {
    val n = u64(s"$what length")
    // Negative raw bits mean an unsigned value >= 2^63 — reject outright.
    if (n < 0L || n > (remaining / elemSize).toLong)
      fail(s"$what length $n exceeds remaining input")
    n.toInt
  }

  /** Exactly `n` raw bytes (already validated by the caller via [[length]]). */
  def bytesExact(n: Int, what: String): Array[Byte] = {
    need(n, what)
    val out = java.util.Arrays.copyOfRange(bytes, pos, pos + n)
    pos += n
    out
  }

  /** A bincode `String`: u64 byte length + strict UTF-8 (mirrors serde/bincode,
    * which rejects invalid UTF-8 rather than substituting replacement chars).
    */
  def string(what: String): String = {
    val n = length(what, 1)
    val raw = bytesExact(n, what)
    val decoder = StandardCharsets.UTF_8
      .newDecoder()
      .onMalformedInput(CodingErrorAction.REPORT)
      .onUnmappableCharacter(CodingErrorAction.REPORT)
    try decoder.decode(ByteBuffer.wrap(raw)).toString
    catch {
      case _: CharacterCodingException => fail(s"$what is not valid UTF-8")
    }
  }
}

private[receipt] object BincodeReader {
  /** Internal control-flow signal only — always caught by `InnerReceipt.parse`. */
  final class ParseException(message: String) extends RuntimeException(message)
}
