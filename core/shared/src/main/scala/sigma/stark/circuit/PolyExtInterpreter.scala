package sigma.stark.circuit

import sigma.stark.{BabyBear, Ext4}

/** Interpreter for the recursion circuit's constraint program — faithful
  * port of risc0-zkp 3.0.4 `src/adapter.rs` `PolyExtStepDef::step`
  * (`PolyExtExecutor::run`).
  *
  * The program is a straight-line pass over [[PolyExtTable]] ops driving two
  * append-only stacks: `fp` of Ext4 values and `mix` of `(tot, mul)` Ext4
  * pairs. The result is `mix(ret)` — its `tot` component is the mixed
  * constraint-polynomial evaluation `verify_validity` compares against the
  * recombined check polynomial.
  *
  * Correctness is pinned by the transcript-capture KAT of the real devnet
  * receipt (`stark-kats/transcript_capture.tsv` checkpoints `poly_mix`,
  * `out`, `mix`, `eval_u` → `result`), per the oracle-parity rule.
  *
  * Kept allocation-light for the consensus path: three preallocated arrays
  * and an index-based while loop; the only per-op allocations are the
  * immutable [[Ext4]] results themselves.
  */
object PolyExtInterpreter {

  /** Mirror of risc0-zkp's `MixState`: the running `(tot, mul)` pair of a
    * constraint chain.
    */
  final case class MixState(tot: Ext4, mul: Ext4)

  /** Run the program. Mirrors the Rust signature
    * `step(mix: &ExtElem, u: &[ExtElem], args: &[&[Elem]]) -> MixState`:
    *
    * @param table   the parsed op table
    * @param polyMix the transcript-drawn constraint mixer (`poly_mix`)
    * @param u       the tapped evaluations `eval_u`, one Ext4 per tap, in
    *                canonical tap order; coefficients must be canonical
    *                (`[0, P)`)
    * @param args    the global buffers, canonical base-field values;
    *                `args(0)` = out globals (OUT_SIZE = 32),
    *                `args(1)` = accum-mix globals (MIX_SIZE = 20) — exactly
    *                what `verify` passes as `&[out, &mix]`
    * @return `Right(MixState)` on success; `Left` for any malformed access
    *         (tap index outside `u`, global outside `args`, non-canonical
    *         global value, stack-shape mismatch) — never throws.
    */
  def step(
      table: PolyExtTable,
      polyMix: Ext4,
      u: Array[Ext4],
      args: Array[Array[Int]]
  ): Either[String, MixState] = {
    val ops = table.ops
    val fp = new Array[Ext4](table.fpVars)
    val mixTot = new Array[Ext4](table.mixVars)
    val mixMul = new Array[Ext4](table.mixVars)
    var fpN = 0
    var mixN = 0

    var i = 0
    while (i < ops.length) {
      ops(i) match {
        case PolyExtOp.Const(v) =>
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          // from_u64 semantics: reduce the raw u32 mod P.
          fp(fpN) = Ext4.fromBase((v % BabyBear.P).toInt)
          fpN += 1
        case PolyExtOp.ConstExt(c0, c1, c2, c3) =>
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          fp(fpN) = Ext4(
            (c0 % BabyBear.P).toInt, (c1 % BabyBear.P).toInt,
            (c2 % BabyBear.P).toInt, (c3 % BabyBear.P).toInt)
          fpN += 1
        case PolyExtOp.Get(tap) =>
          if (tap >= u.length) return Left(s"op $i: Get($tap) outside u (${u.length} taps)")
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          fp(fpN) = u(tap)
          fpN += 1
        case PolyExtOp.GetGlobal(arg, offset) =>
          if (arg >= args.length) return Left(s"op $i: GetGlobal arg $arg outside args (${args.length})")
          if (offset >= args(arg).length)
            return Left(s"op $i: GetGlobal($arg, $offset) outside buffer (${args(arg).length})")
          val v = args(arg)(offset)
          if (v < 0 || v >= BabyBear.P)
            return Left(s"op $i: GetGlobal($arg, $offset) value $v not a canonical field element")
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          fp(fpN) = Ext4.fromBase(v)
          fpN += 1
        case PolyExtOp.Add(a, b) =>
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          fp(fpN) = fp(a) + fp(b)
          fpN += 1
        case PolyExtOp.Sub(a, b) =>
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          fp(fpN) = fp(a) - fp(b)
          fpN += 1
        case PolyExtOp.Mul(a, b) =>
          if (fpN >= fp.length) return Left(s"op $i: fp stack overflow")
          fp(fpN) = fp(a) * fp(b)
          fpN += 1
        case PolyExtOp.True =>
          if (mixN >= mixTot.length) return Left(s"op $i: mix stack overflow")
          mixTot(mixN) = Ext4.Zero
          mixMul(mixN) = Ext4.One
          mixN += 1
        case PolyExtOp.AndEqz(chain, inner) =>
          if (mixN >= mixTot.length) return Left(s"op $i: mix stack overflow")
          mixTot(mixN) = mixTot(chain) + mixMul(chain) * fp(inner)
          mixMul(mixN) = mixMul(chain) * polyMix
          mixN += 1
        case PolyExtOp.AndCond(chain, cond, inner) =>
          if (mixN >= mixTot.length) return Left(s"op $i: mix stack overflow")
          mixTot(mixN) = mixTot(chain) + fp(cond) * mixTot(inner) * mixMul(chain)
          mixMul(mixN) = mixMul(chain) * mixMul(inner)
          mixN += 1
      }
      i += 1
    }

    // Mirror upstream's post-run stack-shape assertions (as Left, not panic).
    if (fpN != table.fpVars)
      Left(s"fp stack ended at $fpN, expected ${table.fpVars}")
    else if (mixN != table.mixVars)
      Left(s"mix stack ended at $mixN, expected ${table.mixVars}")
    else if (table.ret >= mixN)
      Left(s"ret ${table.ret} outside mix stack ($mixN)")
    else
      Right(MixState(mixTot(table.ret), mixMul(table.ret)))
  }
}
