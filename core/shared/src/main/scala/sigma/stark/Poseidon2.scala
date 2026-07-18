package sigma.stark

import BabyBear.{add => fadd, mul => fmul}
import Poseidon2Constants._

/** The Poseidon2-BabyBear width-24 permutation used by the stock RISC0
  * verifier profile's Merkle commitments (EIP-0045 `verifyStark`).
  *
  * Faithful port of risc0-zkp 1.2.6 `core::hash::poseidon2::poseidon2_mix`:
  * initial external linear layer, `RoundsHalfFull` full rounds (constants,
  * x^7 s-box on every cell, external matrix), `RoundsPartial` partial rounds
  * (single constant, x^7 on cell 0, internal matrix), `RoundsHalfFull` full
  * rounds. The external matrix multiply uses the 4x4-circulant decomposition
  * of the Poseidon2 paper (appendix B); the internal matrix has all-ones
  * off-diagonal with `MIntDiag` on the diagonal. Constants come from
  * [[Poseidon2Constants]], extracted programmatically from risc0-zkp.
  *
  * Correctness is pinned by permutation Known Answer Tests generated from
  * risc0-zkp itself (`stark-kats/poseidon2_perm.tsv`).
  */
object Poseidon2 {

  /** x^7 over BabyBear. */
  private def sbox(x: Int): Int = {
    val x2 = fmul(x, x)
    val x4 = fmul(x2, x2)
    fmul(fmul(x4, x2), x)
  }

  /** 4x4 circulant block multiply (Poseidon2 paper, appendix B). */
  private def circulant4(x0: Int, x1: Int, x2: Int, x3: Int): (Int, Int, Int, Int) = {
    val t0 = fadd(x0, x1)
    val t1 = fadd(x2, x3)
    val t2 = fadd(fmul(2, x1), t1)
    val t3 = fadd(fmul(2, x3), t0)
    val t4 = fadd(fmul(4, t1), t3)
    val t5 = fadd(fmul(4, t0), t2)
    val t6 = fadd(t3, t5)
    val t7 = fadd(t2, t4)
    (t6, t5, t7, t4)
  }

  private def multiplyByMExt(cells: Array[Int]): Unit = {
    val old = cells.clone()
    val tmp = new Array[Int](4)
    java.util.Arrays.fill(cells, 0)
    var i = 0
    while (i < Cells / 4) {
      val (o0, o1, o2, o3) =
        circulant4(old(i * 4), old(i * 4 + 1), old(i * 4 + 2), old(i * 4 + 3))
      val out = Array(o0, o1, o2, o3)
      var j = 0
      while (j < 4) {
        tmp(j) = fadd(tmp(j), out(j))
        cells(i * 4 + j) = fadd(cells(i * 4 + j), out(j))
        j += 1
      }
      i += 1
    }
    i = 0
    while (i < Cells) {
      cells(i) = fadd(cells(i), tmp(i % 4))
      i += 1
    }
  }

  private def multiplyByMInt(cells: Array[Int]): Unit = {
    var sum = 0
    var i = 0
    while (i < Cells) { sum = fadd(sum, cells(i)); i += 1 }
    i = 0
    while (i < Cells) {
      cells(i) = fadd(sum, fmul(MIntDiag(i), cells(i)))
      i += 1
    }
  }

  private def fullRound(cells: Array[Int], round: Int): Unit = {
    var i = 0
    while (i < Cells) {
      cells(i) = sbox(fadd(cells(i), RoundConstants(round * Cells + i)))
      i += 1
    }
    multiplyByMExt(cells)
  }

  private def partialRound(cells: Array[Int], round: Int): Unit = {
    cells(0) = sbox(fadd(cells(0), RoundConstants(round * Cells)))
    multiplyByMInt(cells)
  }

  /** Digest length in field elements. */
  final val CellsOut: Int = 8

  /** Sponge rate in field elements. */
  final val CellsRate: Int = 16

  /** Unpadded sponge hash — mirror of risc0-zkp `unpadded_hash`:
    * overwrite-absorb `CellsRate` elements per block, permute, zero-pad the
    * final partial block (also hashing an empty input as one zero block);
    * digest is the first [[CellsOut]] cells. NOTE (as upstream documents):
    * collision resistance holds only among equal-length inputs.
    */
  def unpaddedHash(input: Array[Int]): Array[Int] = {
    val state = new Array[Int](Cells)
    var unmixed = 0
    var i = 0
    while (i < input.length) {
      state(unmixed) = input(i)
      unmixed += 1
      if (unmixed == CellsRate) { mix(state); unmixed = 0 }
      i += 1
    }
    if (unmixed != 0 || input.length == 0) {
      var j = unmixed
      while (j < CellsRate) { state(j) = 0; j += 1 }
      mix(state)
    }
    java.util.Arrays.copyOfRange(state, 0, CellsOut)
  }

  /** Merkle node compression — `unpadded_hash` of two 8-element digests
    * (RISC0 `Poseidon2HashFn.hash_pair`).
    */
  def hashPair(a: Array[Int], b: Array[Int]): Array[Int] = {
    require(a.length == CellsOut && b.length == CellsOut, "digests are 8 elements")
    unpaddedHash(a ++ b)
  }

  /** The raw sponge mixing function; permutes `cells` (length [[Cells]])
    * in place. Mirror of risc0-zkp `poseidon2_mix`.
    */
  def mix(cells: Array[Int]): Unit = {
    require(cells.length == Cells, s"expected $Cells cells, got ${cells.length}")
    var round = 0
    multiplyByMExt(cells)
    var i = 0
    while (i < RoundsHalfFull) { fullRound(cells, round); round += 1; i += 1 }
    i = 0
    while (i < RoundsPartial) { partialRound(cells, round); round += 1; i += 1 }
    i = 0
    while (i < RoundsHalfFull) { fullRound(cells, round); round += 1; i += 1 }
  }
}
