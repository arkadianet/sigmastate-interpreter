package sigma.stark

import BabyBear.{add => fadd}

/** The Fiat-Shamir transcript RNG of the stock RISC0 succinct profile —
  * mirror of risc0-zkp 1.2.6 `Poseidon2Rng`.
  *
  * A width-24 Poseidon2 sponge in duplex mode:
  *  - `mix(digest)`: if currently squeezing, permute first; add the 8
  *    digest words into cells 0..7; permute.
  *  - `randomElem()`: refill (permute) after 16 draws; return the next cell.
  *  - `randomBits(n)`: draw FOUR elements, keep the first non-zero (in
  *    draw order), mask to `n` low bits — upstream's exact (quirky)
  *    zero-avoidance; all four draws consume pool slots regardless.
  *  - `randomExtElem()`: four sequential draws as Ext4 coefficients.
  *
  * Digest words arrive as already-reduced field elements (upstream uses
  * `new_raw` + `is_reduced` invariants on transcript digests).
  * Correctness is pinned by an op-script KAT recorded from risc0-zkp's own
  * Rng (`stark-kats/poseidon2_rng.tsv`).
  */
final class Poseidon2Rng {
  private val cells = new Array[Int](Poseidon2Constants.Cells)
  private var poolUsed = 0

  /** Absorb a RISC0 digest. `digestWords` are RAW digest words as they
    * appear on the wire — risc0 stores Montgomery residues in digests and
    * adds them with `Elem::new_raw`, so each word is converted to its
    * canonical value ([[BabyBear.fromRaw]]) before entering this
    * canonical-form state.
    */
  def mix(digestWords: Array[Int]): Unit = {
    require(digestWords.length == Poseidon2.CellsOut, "digest is 8 words")
    if (poolUsed != 0) {
      Poseidon2.mix(cells)
      poolUsed = 0
    }
    var i = 0
    while (i < Poseidon2.CellsOut) {
      cells(i) = fadd(cells(i), BabyBear.fromRaw(digestWords(i)))
      i += 1
    }
    Poseidon2.mix(cells)
  }

  def randomElem(): Int = {
    if (poolUsed == Poseidon2.CellsRate) {
      Poseidon2.mix(cells)
      poolUsed = 0
    }
    val out = cells(poolUsed)
    poolUsed += 1
    out
  }

  def randomBits(bits: Int): Int = {
    var v = randomElem()
    var i = 0
    while (i < 3) {
      val nv = randomElem()
      if (v == 0) v = nv
      i += 1
    }
    (((1L << bits) - 1) & (v.toLong & 0xFFFFFFFFL)).toInt
  }

  def randomExtElem(): Ext4 =
    Ext4(randomElem(), randomElem(), randomElem(), randomElem())
}
