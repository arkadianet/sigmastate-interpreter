//! circuit_extract — serialize the RISC0 recursion circuit's verifier data
//! tables for the EIP-0045 JVM verifier.
//!
//! Emits (to `core/jvm/src/test/resources/stark-kats/`):
//!   - `circuit_taps.tsv`        — the full recursion-circuit tap set
//!     (643 taps / 163 registers, groups accum=12, code=23, data=128 cols)
//!     plus every `TapSet` field the verifier consumes (combo tables etc.).
//!   - `circuit_polyext_ops.tsv` — the complete `PolyExtStepDef` op table
//!     (12,359 stack-machine ops, ret = 1228): the recursion circuit's
//!     entire constraint polynomial as data.
//!   - `circuit_params.tsv`      — v3_0 succinct verifier-context parameters:
//!     allowed control root + control-ID lists, info strings, po2 range,
//!     FRI parameters.
//!
//! Oracles (external, per the oracle-parity rule):
//!   - taps: `risc0_circuit_recursion::CIRCUIT.get_taps()` (public API).
//!   - ops:  vendored copy of risc0-circuit-recursion 4.0.4 `poly_ext.rs`
//!     (the module is private upstream); equivalence with the crate's own
//!     private table is asserted below by evaluating both on identical
//!     pseudo-random inputs.
//!   - control IDs / root: `risc0_circuit_recursion::control_id` (public).
//!   - constants: risc0-zkp 3.0.4 public consts; the two private consts
//!     (`FRI_MIN_DEGREE`, `FRI_FOLD_PO2`) are hardcoded with citation.
//!
//! Determinism: everything derives from crate constants (the cross-check
//! inputs come from a fixed LCG seed) — re-running is byte-identical.

#[path = "../vendored/recursion_poly_ext.rs"]
mod recursion_poly_ext;

use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use blake2::digest::{consts::U32, Digest as _};
use blake2::Blake2b;
use risc0_circuit_recursion::CIRCUIT;
use risc0_zkp_v3::adapter::{
    CircuitInfo, PolyExt, PolyExtStep, TapsProvider, PROOF_SYSTEM_INFO, REGISTER_GROUP_ACCUM,
    REGISTER_GROUP_CODE, REGISTER_GROUP_DATA,
};
use risc0_zkp_v3::field::baby_bear::{BabyBear, BabyBearElem, BabyBearExtElem, P};
use risc0_zkp_v3::field::{Elem, ExtElem};
use risc0_zkp_v3::{FRI_FOLD, INV_RATE, MAX_CYCLES_PO2, MIN_CYCLES_PO2, QUERIES};

type Blake2b256 = Blake2b<U32>;

const OUT_DIR: &str = "../core/jvm/src/test/resources/stark-kats";

/// Report/EIP expectations, asserted against the live crates below.
const EXPECT_NUM_TAPS: usize = 643;
const EXPECT_REG_COUNT: usize = 163;
const EXPECT_GROUP_SIZES: [usize; 3] = [12, 23, 128]; // accum, code, data
const EXPECT_OPS: usize = 12_359;
const EXPECT_RET: usize = 1228;
// NOTE: the architecture report (agentB) said 28; the crate actually lists 27
// (identity + join/join_povw/join_unwrap_povw + lift po2 14-22 + lift_povw
// po2 14-22 + resolve/resolve_povw/resolve_unwrap_povw + union + unwrap_povw
// = 1+3+9+9+3+1+1). The code is authoritative.
const EXPECT_ALLOWED_CONTROL_IDS: usize = 27;

/// Private consts in risc0-zkp 3.0.4 src/lib.rs:48,54 — not importable, so
/// hardcoded here with citation (the only two non-extracted values).
const FRI_FOLD_PO2: usize = 4;
const FRI_MIN_DEGREE: usize = 256;

/// Deterministic 32-bit LCG (same constants as main.rs) for cross-check
/// inputs — no RNG dependency, byte-identical re-runs.
struct Lcg(u64);
impl Lcg {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 32) as u32
    }
    fn next_fe(&mut self) -> BabyBearElem {
        BabyBearElem::new(self.next_u32() % P)
    }
    fn next_ext(&mut self) -> BabyBearExtElem {
        BabyBearExtElem::from_subelems((0..4).map(|_| self.next_fe()))
    }
}

fn gen_taps(out: &Path) {
    let taps = CIRCUIT.get_taps();

    // ----- structural assertions (sizes from the architecture report) -----
    assert_eq!(taps.num_groups(), 3, "group count");
    assert_eq!(taps.group_names, &["accum", "code", "data"], "group names");
    assert_eq!(taps.tap_size(), EXPECT_NUM_TAPS, "total taps");
    assert_eq!(taps.reg_count, EXPECT_REG_COUNT, "register count");
    for (gid, expect) in EXPECT_GROUP_SIZES.iter().enumerate() {
        assert_eq!(taps.group_size(gid), *expect, "group {gid} column count");
    }
    assert_eq!(taps.combos_count, 5, "combos_count");
    assert_eq!(taps.combo_begin, &[0u16, 1, 3, 9, 15, 20], "combo_begin");
    assert_eq!(taps.tot_combo_backs, 20, "tot_combo_backs");
    assert_eq!(
        taps.group_begin,
        &[0usize, 16, 39, 643],
        "group_begin (accum/code/data tap ranges)"
    );

    let join = |it: &mut dyn Iterator<Item = String>| it.collect::<Vec<_>>().join(",");

    let mut s = String::from(
        "# circuit_taps.tsv — recursion circuit TapSet (RISC0 circuit v3.0 succinct path)\n\
         # Oracle: risc0-circuit-recursion 4.0.4 CIRCUIT.get_taps() (risc0-zkp 3.0.4 TapSet).\n\
         # Rows: `meta\\t<key>\\t<comma-list>` then `tap\\t<idx>\\t<group>\\t<offset>\\t<back>\\t<combo>\\t<skip>`.\n\
         # See circuit_tables.md for the full schema.\n",
    );
    let _ = writeln!(s, "meta\tgroup_names\t{}", taps.group_names.join(","));
    let _ = writeln!(
        s,
        "meta\tgroup_begin\t{}",
        join(&mut taps.group_begin.iter().map(|v| v.to_string()))
    );
    let _ = writeln!(
        s,
        "meta\tgroup_size\t{}",
        join(&mut (0..3).map(|g| taps.group_size(g).to_string()))
    );
    let _ = writeln!(s, "meta\treg_count\t{}", taps.reg_count);
    let _ = writeln!(s, "meta\tcombos_count\t{}", taps.combos_count);
    let _ = writeln!(
        s,
        "meta\tcombo_begin\t{}",
        join(&mut taps.combo_begin.iter().map(|v| v.to_string()))
    );
    let _ = writeln!(
        s,
        "meta\tcombo_taps\t{}",
        join(&mut taps.combo_taps.iter().map(|v| v.to_string()))
    );
    let _ = writeln!(s, "meta\ttot_combo_backs\t{}", taps.tot_combo_backs);

    for (idx, tap) in taps.taps.iter().enumerate().take(taps.tap_size()) {
        let _ = writeln!(
            s,
            "tap\t{idx}\t{}\t{}\t{}\t{}\t{}",
            tap.group, tap.offset, tap.back, tap.combo, tap.skip
        );
    }
    fs::write(out.join("circuit_taps.tsv"), &s).expect("write circuit_taps.tsv");
    println!(
        "wrote circuit_taps.tsv: {} taps, {} regs, group sizes {:?}",
        taps.tap_size(),
        taps.reg_count,
        EXPECT_GROUP_SIZES
    );
}

/// One serialized op: mnemonic + operands. Wildcard arm required —
/// `PolyExtStep` is #[non_exhaustive]; an unknown variant must fail loudly,
/// never be skipped (the table is consensus data).
fn serialize_op(op: &PolyExtStep) -> (&'static str, Vec<u64>) {
    match op {
        PolyExtStep::Const(v) => ("Const", vec![*v as u64]),
        PolyExtStep::ConstExt(x0, x1, x2, x3) => (
            "ConstExt",
            vec![*x0 as u64, *x1 as u64, *x2 as u64, *x3 as u64],
        ),
        PolyExtStep::Get(tap) => ("Get", vec![*tap as u64]),
        PolyExtStep::GetGlobal(base, offset) => ("GetGlobal", vec![*base as u64, *offset as u64]),
        PolyExtStep::Add(a, b) => ("Add", vec![*a as u64, *b as u64]),
        PolyExtStep::Sub(a, b) => ("Sub", vec![*a as u64, *b as u64]),
        PolyExtStep::Mul(a, b) => ("Mul", vec![*a as u64, *b as u64]),
        PolyExtStep::True => ("True", vec![]),
        PolyExtStep::AndEqz(chain, inner) => ("AndEqz", vec![*chain as u64, *inner as u64]),
        PolyExtStep::AndCond(chain, cond, inner) => {
            ("AndCond", vec![*chain as u64, *cond as u64, *inner as u64])
        }
        other => {
            panic!("unknown PolyExtStep variant {other:?} — regenerate against this crate version")
        }
    }
}

fn gen_polyext_ops(out: &Path) {
    let def = &recursion_poly_ext::DEF;

    // ----- structural assertions -----
    assert_eq!(def.block.len(), EXPECT_OPS, "op count");
    assert_eq!(def.ret, EXPECT_RET, "ret index");
    let mix_vars = def.ret + 1;
    let fp_vars = def.block.len() - mix_vars;
    assert_eq!(mix_vars, 1229, "mix-var count");
    assert_eq!(fp_vars, 11_130, "fp-var count");

    // Opcode histogram (report: Const 284, Get 669, GetGlobal 52, Add 4061,
    // Sub 1385, Mul 4679, True 1, AndEqz 1076, AndCond 152, ConstExt 0).
    let mut hist: std::collections::BTreeMap<&'static str, usize> = Default::default();
    let mut canonical = String::new();
    let mut rows = String::new();
    for (idx, op) in def.block.iter().enumerate() {
        let (name, operands) = serialize_op(op);
        *hist.entry(name).or_default() += 1;
        let ops_joined = operands
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(canonical, "{name}:{ops_joined}");
        let _ = writeln!(rows, "op\t{idx}\t{name}\t{ops_joined}");
    }
    let expected_hist: &[(&str, usize)] = &[
        ("Add", 4061),
        ("AndCond", 152),
        ("AndEqz", 1076),
        ("Const", 284),
        ("Get", 669),
        ("GetGlobal", 52),
        ("Mul", 4679),
        ("Sub", 1385),
        ("True", 1),
    ];
    let got_hist: Vec<(&str, usize)> = hist.iter().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(got_hist, expected_hist, "opcode histogram");

    // GetGlobal args must only reference out (arg 0, 32 elems) and mix
    // (arg 1, 20 elems) — the verifier passes &[out, &mix].
    for op in def.block {
        if let PolyExtStep::GetGlobal(base, offset) = op {
            match base {
                0 => assert!(*offset < 32, "GetGlobal(0, {offset}) out of out range"),
                1 => assert!(*offset < 20, "GetGlobal(1, {offset}) out of mix range"),
                _ => panic!("GetGlobal arg {base} unknown"),
            }
        }
    }

    let table_hash = hex::encode(Blake2b256::digest(canonical.as_bytes()));

    // ----- vendored-table equivalence vs the crate's own private table -----
    // CIRCUIT.poly_ext (pub trait) evaluates risc0-circuit-recursion's
    // private DEF; our vendored DEF must produce identical MixState on
    // identical inputs. 8 pseudo-random cases (fixed seed) + 1 all-zero case.
    let mut lcg = Lcg(0xE1900045_0000000A);
    for case in 0..9 {
        let (poly_mix, u, out_args, mix_args): (
            BabyBearExtElem,
            Vec<BabyBearExtElem>,
            Vec<BabyBearElem>,
            Vec<BabyBearElem>,
        ) = if case == 0 {
            (
                BabyBearExtElem::ZERO,
                vec![BabyBearExtElem::ZERO; EXPECT_NUM_TAPS],
                vec![BabyBearElem::ZERO; 32],
                vec![BabyBearElem::ZERO; 20],
            )
        } else {
            (
                lcg.next_ext(),
                (0..EXPECT_NUM_TAPS).map(|_| lcg.next_ext()).collect(),
                (0..32).map(|_| lcg.next_fe()).collect(),
                (0..20).map(|_| lcg.next_fe()).collect(),
            )
        };
        let args: &[&[BabyBearElem]] = &[&out_args, &mix_args];
        let ours = def.step::<BabyBear>(&poly_mix, &u, args);
        let theirs = CIRCUIT.poly_ext(&poly_mix, &u, args);
        assert_eq!(
            ours.tot, theirs.tot,
            "vendored DEF diverges from CIRCUIT.poly_ext (tot, case {case})"
        );
        assert_eq!(
            ours.mul, theirs.mul,
            "vendored DEF diverges from CIRCUIT.poly_ext (mul, case {case})"
        );
    }
    println!("vendored DEF == CIRCUIT.poly_ext on 9 cross-check cases");

    let mut s = String::from(
        "# circuit_polyext_ops.tsv — recursion circuit constraint system as data\n\
         # Oracle: risc0-circuit-recursion 4.0.4 poly_ext.rs `DEF` (vendored copy,\n\
         # asserted equivalent to the crate's own private table at generation time).\n\
         # Interpreter semantics: risc0-zkp 3.0.4 src/adapter.rs PolyExtStepDef::step.\n\
         # Rows: `meta\\t<key>\\t<value>` then `op\\t<idx>\\t<mnemonic>\\t<comma-operands>`.\n\
         # See circuit_tables.md for the full schema + interpreter contract.\n",
    );
    let _ = writeln!(s, "meta\tops_count\t{}", def.block.len());
    let _ = writeln!(s, "meta\tret\t{}", def.ret);
    let _ = writeln!(s, "meta\tfp_vars\t{fp_vars}");
    let _ = writeln!(s, "meta\tmix_vars\t{mix_vars}");
    let _ = writeln!(
        s,
        "meta\topcode_histogram\t{}",
        expected_hist
            .iter()
            .map(|(k, v)| format!("{k}={v}"))
            .collect::<Vec<_>>()
            .join(",")
    );
    let _ = writeln!(s, "meta\tblake2b256\t{table_hash}");
    s.push_str(&rows);
    fs::write(out.join("circuit_polyext_ops.tsv"), &s).expect("write circuit_polyext_ops.tsv");
    println!(
        "wrote circuit_polyext_ops.tsv: {} ops, ret={}, blake2b256={}",
        def.block.len(),
        def.ret,
        table_hash
    );
}

fn gen_params(out: &Path) {
    use risc0_circuit_recursion::control_id::{
        ALLOWED_CONTROL_IDS, ALLOWED_CONTROL_ROOT, MIN_LIFT_PO2, POSEIDON2_CONTROL_IDS,
    };

    assert_eq!(
        ALLOWED_CONTROL_IDS.len(),
        EXPECT_ALLOWED_CONTROL_IDS,
        "allowed control-ID count"
    );
    assert_eq!(
        hex::encode(ALLOWED_CONTROL_ROOT.as_bytes()),
        "a54dc85ac99f851c92d7c96d7318af41dbe7c0194edfcc37eb4d422a998c1f56",
        "allowed control root (report §3)"
    );

    let circuit_info = <risc0_circuit_recursion::CircuitImpl as CircuitInfo>::CIRCUIT_INFO;
    assert_eq!(format!("{PROOF_SYSTEM_INFO}"), "RISC0_STARK:v1__");
    assert_eq!(format!("{circuit_info}"), "RECURSION:rev1v1");
    let output_size = <risc0_circuit_recursion::CircuitImpl as CircuitInfo>::OUTPUT_SIZE;
    let mix_size = <risc0_circuit_recursion::CircuitImpl as CircuitInfo>::MIX_SIZE;
    assert_eq!(output_size, 32);
    assert_eq!(mix_size, 20);
    assert_eq!(QUERIES, 50);
    assert_eq!(INV_RATE, 4);
    assert_eq!(FRI_FOLD, 16);
    assert_eq!(MAX_CYCLES_PO2, 24);

    let ext_size = <BabyBearExtElem as ExtElem>::EXT_SIZE;
    assert_eq!(ext_size, 4);
    let check_size = INV_RATE * ext_size;

    let mut s = String::from(
        "# circuit_params.tsv — v3_0 succinct verifier-context parameters\n\
         # Oracles: risc0-circuit-recursion 4.0.4 control_id.rs + info.rs;\n\
         # risc0-zkp 3.0.4 lib.rs / adapter.rs. FRI_MIN_DEGREE and FRI_FOLD_PO2 are\n\
         # private consts (risc0-zkp 3.0.4 src/lib.rs:54,48) hardcoded with citation.\n\
         # Rows: `param\\t<key>\\t<value>`, `control_id\\t<idx>\\t<hex32>`,\n\
         # `named_control_id\\t<name>\\t<hex32>`. See circuit_tables.md.\n",
    );
    let mut p = |k: &str, v: String| {
        let _ = writeln!(s, "param\t{k}\t{v}");
    };
    p("proof_system_info", format!("{PROOF_SYSTEM_INFO}"));
    p("circuit_info", format!("{circuit_info}"));
    p("output_size", output_size.to_string());
    p("mix_size", mix_size.to_string());
    p("queries", QUERIES.to_string());
    p("inv_rate", INV_RATE.to_string());
    p("ext_size", ext_size.to_string());
    p("check_size", check_size.to_string());
    p("fri_fold", FRI_FOLD.to_string());
    p("fri_fold_po2", FRI_FOLD_PO2.to_string());
    p("fri_min_degree", FRI_MIN_DEGREE.to_string());
    p("min_cycles_po2", MIN_CYCLES_PO2.to_string());
    p("max_cycles_po2", MAX_CYCLES_PO2.to_string());
    p("min_lift_po2", MIN_LIFT_PO2.to_string());
    p("hashfn", "poseidon2".to_string());
    p(
        "allowed_control_root",
        hex::encode(ALLOWED_CONTROL_ROOT.as_bytes()),
    );
    p(
        "allowed_control_ids_count",
        ALLOWED_CONTROL_IDS.len().to_string(),
    );
    for (idx, id) in ALLOWED_CONTROL_IDS.iter().enumerate() {
        let _ = writeln!(s, "control_id\t{idx}\t{}", hex::encode(id.as_bytes()));
    }
    for (name, id) in POSEIDON2_CONTROL_IDS.iter() {
        let _ = writeln!(
            s,
            "named_control_id\t{name}\t{}",
            hex::encode(id.as_bytes())
        );
    }
    fs::write(out.join("circuit_params.tsv"), &s).expect("write circuit_params.tsv");
    println!(
        "wrote circuit_params.tsv: control root + {} allowed IDs + {} named IDs",
        ALLOWED_CONTROL_IDS.len(),
        POSEIDON2_CONTROL_IDS.len()
    );

    // Consistency: REGISTER_GROUP_* ids used by the verify driver.
    assert_eq!(REGISTER_GROUP_ACCUM, 0);
    assert_eq!(REGISTER_GROUP_CODE, 1);
    assert_eq!(REGISTER_GROUP_DATA, 2);
}

fn main() {
    let out = Path::new(OUT_DIR);
    fs::create_dir_all(out).expect("mkdir out");
    gen_taps(out);
    gen_polyext_ops(out);
    gen_params(out);
    println!("circuit tables extracted + size-asserted");
}
