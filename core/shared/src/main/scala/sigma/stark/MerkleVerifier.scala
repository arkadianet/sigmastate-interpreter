package sigma.stark

/** Merkle branch verifier — mirror of risc0-zkp
  * `verify::merkle::MerkleTreeVerifier` with the Poseidon2 hash suite.
  *
  * Version note: risc0-zkp 1.2.6 and 3.0.4 (the version the node's succinct
  * verify path links) are value-identical here — same tree shape, same
  * hashing, same transcript coupling; 3.0.4 additionally validates wire
  * digests (`HashFn::is_digest_valid`, all words `< P`) and returns
  * `ReceiptFormatError` where 1.2.6 panicked. This port follows the 3.0.4
  * semantics.
  *
  * Tree shape (upstream `MerkleTreeParams`): `rowSize` leaves (a power of
  * two), each leaf hashing `colSize` field elements; `topSize = 2^t` where
  * `t` is the largest layer index (`< layers`) with `2^t <= queries` — the
  * layer above which hashes are checked only once. Virtual node `i` has
  * children `2i` / `2i+1`; the root is node 1; the top row occupies nodes
  * `[topSize, 2*topSize)` and comes from the proof stream, nodes
  * `[1, topSize)` are recomputed from it at construction.
  *
  * Transcript protocol (this defines the Fiat-Shamir coupling, ported
  * exactly): construction reads the `topSize` top-row digests from the IOP,
  * folds them up to the root, and commits ONLY the root to the rng.
  * [[verify]] reads the row and path digests without touching the rng.
  *
  * Wire-form decisions (each traced to the upstream flow):
  *  - Digests are held and compared in RAW (Montgomery) word form — upstream
  *    compares `Digest` words directly and never decodes them.
  *  - Node hashing converts deliberately at the hash boundary: upstream
  *    `hash_pair` reinterprets raw digest words as field elements
  *    (`Elem::new_raw`) and sponges them, so [[hashPairRaw]] maps raw ->
  *    canonical ([[BabyBear.fromRaw]]) for [[Poseidon2.hashPair]] and
  *    re-encodes the digest output with [[BabyBear.toRaw]] (upstream
  *    `to_digest` stores `as_u32_montgomery`).
  *  - Leaf hashing consumes the row via `ReadIop.readFieldElemSlice`
  *    (canonical values — upstream `hash_elem_slice` sponges the elements
  *    themselves), then re-encodes the digest to raw form.
  *  - Wire digest words are validated `< P` exactly where risc0-zkp 3.0.4
  *    checks `is_digest_valid` and returns `ReceiptFormatError`: the top row
  *    (validated pairwise before `hash_pair` when `topSize > 1`) and every
  *    path digest in [[verify]]. For the `topSize == 1` corner upstream (both
  *    versions) commits the raw top word to the rng unchecked; an unreduced
  *    word there can never equal a recomputed digest word (hash outputs are
  *    reduced), so every such proof is rejected by upstream too — rejecting
  *    at construction preserves accept/reject parity while keeping the
  *    canonical-form rng state sound.
  *
  * Rejection style: `Either[String, _]`, never throwing on malformed proof
  * bytes; `require` guards only verifier-chosen parameters.
  */
final class MerkleVerifier private (
    val rowSize: Int,
    val colSize: Int,
    topSize: Int,
    top: Array[Array[Int]],
    rest: Array[Array[Int]]
) {
  import MerkleVerifier.hashPairRaw

  /** Root digest in RAW word form (virtual node 1). */
  def rootRaw: Array[Int] = if (topSize == 1) top(0) else rest(0)

  /** Verify one branch read from `iop` against row `idx`; returns the
    * CANONICAL row values on success. Mirror of upstream `verify`: rejects
    * an out-of-range index, reads `colSize` elements (leaf), then one
    * "other" digest per level below the top row, ascending with
    * left/right order decided by the index's low bit.
    */
  def verify(iop: ReadIop, idx: Int): Either[String, Array[Int]] = {
    if (idx < 0 || idx >= rowSize)
      return Left(s"merkle query out of range: idx $idx, rows $rowSize")
    iop.readFieldElemSlice(colSize) match {
      case None => Left("merkle branch: bad row data (truncated or word >= P)")
      case Some(row) =>
        var cur = Poseidon2.unpaddedHash(row).map(BabyBear.toRaw)
        var i = idx + rowSize
        var failed: String = null
        while (failed == null && i >= 2 * topSize) {
          iop.readPodSlice(1) match {
            case None => failed = "merkle branch: truncated path digest"
            case Some(digests) =>
              val other = digests(0)
              if (!MerkleVerifier.allReduced(other))
                failed = "merkle branch: unreduced path digest word"
              else {
                val lowBit = i & 1
                i /= 2
                cur = if (lowBit == 1) hashPairRaw(other, cur) else hashPairRaw(cur, other)
              }
          }
        }
        if (failed != null) Left(failed)
        else {
          val present = if (i >= topSize) top(i - topSize) else rest(i - 1)
          if (java.util.Arrays.equals(present, cur)) Right(row)
          else Left("merkle branch: root path mismatch")
        }
    }
  }
}

object MerkleVerifier {

  /** Construct by reading the top row from `iop` and committing the root —
    * upstream `MerkleTreeVerifier::new`. `rowSize` must be a power of two
    * and `colSize`/`queries` positive (verifier parameters, not proof
    * data); a malformed proof stream yields `Left`.
    */
  def create(
      iop: ReadIop,
      rowSize: Int,
      colSize: Int,
      queries: Int): Either[String, MerkleVerifier] = {
    require(rowSize > 0 && (rowSize & (rowSize - 1)) == 0, s"rowSize not a power of 2: $rowSize")
    require(colSize > 0, s"colSize must be positive: $colSize")
    require(queries > 0, s"queries must be positive: $queries")

    // Upstream MerkleTreeParams::new: the top layer is the deepest layer
    // (strictly below the leaves) of size at most `queries`.
    val layers = 31 - Integer.numberOfLeadingZeros(rowSize)
    var topLayer = 0
    var i = 1
    while (i < layers && (1 << i) <= queries) { topLayer = i; i += 1 }
    val topSize = 1 << topLayer

    iop.readPodSlice(topSize) match {
      case None => Left("merkle top row: truncated proof")
      case Some(top) =>
        if (!top.forall(allReduced))
          Left("merkle top row: unreduced digest word")
        else {
          // Fold the top row up to the root: children of virtual node i are
          // at 2i / 2i+1; rest(i - 1) holds node i for i in [1, topSize).
          val rest = new Array[Array[Int]](topSize - 1)
          var n = topSize - 1
          while (n >= topSize / 2 && n >= 1) {
            rest(n - 1) = hashPairRaw(top(2 * n - topSize), top(2 * n + 1 - topSize))
            n -= 1
          }
          while (n >= 1) {
            rest(n - 1) = hashPairRaw(rest(2 * n - 1), rest(2 * n))
            n -= 1
          }
          val verifier = new MerkleVerifier(rowSize, colSize, topSize, top, rest)
          iop.commit(verifier.rootRaw)
          Right(verifier)
        }
    }
  }

  /** True iff every word is a reduced residue (`< P` unsigned). */
  private def allReduced(digestRaw: Array[Int]): Boolean = {
    var i = 0
    while (i < digestRaw.length) {
      val w = digestRaw(i)
      if (w < 0 || w >= BabyBear.P) return false
      i += 1
    }
    true
  }

  /** Node compression over RAW digests — upstream `hash_pair` reinterprets
    * raw words as elements and sponges them; output re-encoded to raw.
    */
  private def hashPairRaw(aRaw: Array[Int], bRaw: Array[Int]): Array[Int] =
    Poseidon2
      .hashPair(aRaw.map(BabyBear.fromRaw), bRaw.map(BabyBear.fromRaw))
      .map(BabyBear.toRaw)
}
