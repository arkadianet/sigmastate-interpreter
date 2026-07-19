//! KAT generator for the EIP-0045 verifyStark JVM `ReadIop` /
//! `MerkleVerifier` (transcript-over-proof-stream + Merkle branch checks).
//!
//! Every vector is produced by risc0-zkp 1.2.6 ITSELF (prover side:
//! `MerkleTreeProver` + `WriteIOP`; oracle side: `ReadIOP` +
//! `MerkleTreeVerifier`) — never by the Scala code under test. The
//! crate-private prover/verifier types are reached through the vendored
//! visibility-only patch in `vendor/risc0-zkp-1.2.6` (see Cargo.toml
//! `[patch.crates-io]`; grep "PATCHED").
//!
//! Sanity rule: every emitted vector — positive AND negative — is replayed
//! through risc0-zkp's OWN ReadIOP/MerkleTreeVerifier before being written
//! (assert!), mirroring the oracle-confirmed receipt mutations in main.rs.
//!
//! Determinism: no RNG — inputs derive from fixed LCG seeds so re-running
//! the generator reproduces byte-identical vectors.
//!
//! Version note: these vectors are generated with risc0-zkp 1.2.6, and are
//! byte-valid for 3.0.4 (the version the node's succinct verify path
//! links): `prove/write_iop.rs`, `core/hash/poseidon2/rng.rs` and
//! `core/digest.rs` are byte-identical between the two versions, the
//! Poseidon2 permutation/constants and `prove/merkle.rs` proof streams are
//! unchanged (doc/test-only diffs), and `verify/{read_iop,merkle}.rs`
//! differ only in error plumbing (1.2.6 panics -> 3.0.4
//! `VerificationError::ReceiptFormatError`, plus explicit
//! `is_digest_valid` word checks) — the semantics the Scala port follows.
//!
//! Wire-form notes (the raw/canonical Montgomery trap):
//!  - Digest words on the wire are RAW Montgomery residues
//!    (`Digest::as_words` == `Elem::as_u32_montgomery`).
//!  - Field elements on the wire are ALSO raw Montgomery residues:
//!    `write_field_elem_slice` emits `Elem::as_u32_slice` (the internal
//!    Montgomery repr) and `read_field_elem_slice` is a checked cast that
//!    only requires `word < P`.
//!  - This file records field-element VALUES in canonical form
//!    (`Elem::as_u32`) and digests in RAW form, matching the Scala API
//!    boundary under test.

use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::Path;

use risc0_core::field::baby_bear::{BabyBear, BabyBearElem, P};
use risc0_core::field::ExtElem;
use risc0_zkp::core::digest::Digest;
use risc0_zkp::core::hash::poseidon2::Poseidon2HashSuite;
use risc0_zkp::core::log2_ceil;
use risc0_zkp::hal::cpu::CpuHal;
use risc0_zkp::hal::Hal;
use risc0_zkp::prove::merkle::MerkleTreeProver;
use risc0_zkp::prove::write_iop::WriteIOP;
use risc0_zkp::verify::{MerkleTreeVerifier, ReadIOP};

const OUT_DIR: &str = "../core/jvm/src/test/resources/stark-kats";

/// Deterministic 32-bit LCG (Numerical Recipes constants) — same generator
/// as main.rs, different seeds.
struct Lcg(u64);
impl Lcg {
    fn next_u32(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 32
    }
    fn next_fe(&mut self) -> u32 {
        (self.next_u32() % P as u64) as u32
    }
}

fn join_u32(words: &[u32]) -> String {
    words
        .iter()
        .map(|w| w.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn canon(elems: &[BabyBearElem]) -> Vec<u32> {
    elems.iter().map(|&e| u32::from(e)).collect()
}

// ---------------------------------------------------------------------------
// Part A: pure ReadIOP transcript script
// ---------------------------------------------------------------------------

/// One transcript operation with its oracle-expected outcome.
enum Op {
    /// `read_u32s(n)` — raw words, no validation.
    U32s(Vec<u32>),
    /// `read_field_elem_slice(n)` — expected CANONICAL values.
    Elems(Vec<u32>),
    /// `read_pod_slice::<Digest>(n)` — expected RAW digest words (8n).
    Pod(Vec<u32>),
    /// `commit(digest)` — RAW digest words mixed into the Fiat-Shamir rng.
    Commit([u32; 8]),
    /// `random_elem()` — expected CANONICAL value.
    RndElem(u32),
    /// `random_bits(bits)` — expected value.
    RndBits(usize, u32),
    /// `random_ext_elem()` — expected CANONICAL coefficients [c0..c3].
    RndExt([u32; 4]),
}

fn gen_readiop_script(out: &Path) {
    let suite = Poseidon2HashSuite::new_suite();
    let hashfn = suite.hashfn.as_ref();
    let mut lcg = Lcg(0xE1900045_00000006);

    let mut iop = WriteIOP::<BabyBear>::new(suite.rng.as_ref());
    let mut ops: Vec<Op> = Vec::new();

    // 1. Raw u32 words, deliberately including >= P, >= 2^31 and the INVALID
    //    bit pattern 0xffffffff: read_u32s performs NO field validation.
    let raw_words: Vec<u32> = vec![0, 1, P, 0x8000_0000, 0xffff_ffff];
    iop.write_u32_slice(&raw_words);
    ops.push(Op::U32s(raw_words.clone()));

    // 2. Commit a digest that is NOT in the stream (the "locally recomputed
    //    root" pattern) and draw challenges.
    let d0_elems: Vec<BabyBearElem> = (0..11).map(|_| BabyBearElem::new(lcg.next_fe())).collect();
    let d0 = hashfn.hash_elem_slice(&d0_elems);
    iop.commit(&d0);
    ops.push(Op::Commit(*d0.as_words().first_chunk::<8>().unwrap()));
    for _ in 0..2 {
        let v = iop.random_elem();
        ops.push(Op::RndElem(u32::from(v)));
    }
    let b = iop.random_bits(27);
    ops.push(Op::RndBits(27, b));

    // 3. Field elements over the wire, with canonical edge values 0 and P-1:
    //    the wire words are Montgomery residues; expected values canonical.
    let elems: Vec<BabyBearElem> = [0u32, P - 1, 1, 1234567]
        .iter()
        .map(|&v| BabyBearElem::new(v))
        .chain((0..2).map(|_| BabyBearElem::new(lcg.next_fe())))
        .collect();
    iop.write_field_elem_slice::<BabyBearElem>(&elems);
    ops.push(Op::Elems(canon(&elems)));
    let e = iop.random_ext_elem();
    let sub = e.subelems();
    ops.push(Op::RndExt([
        u32::from(sub[0]),
        u32::from(sub[1]),
        u32::from(sub[2]),
        u32::from(sub[3]),
    ]));

    // 4. Two digests written to the stream, then commit the first — the
    //    "read a control-root from the proof, then bind it" pattern.
    let d1 = hashfn.hash_elem_slice(&[BabyBearElem::new(lcg.next_fe())]);
    let d2 = hashfn.hash_elem_slice(&[BabyBearElem::new(lcg.next_fe())]);
    iop.write_pod_slice(&[*d1, *d2]);
    let mut pod_words = d1.as_words().to_vec();
    pod_words.extend_from_slice(d2.as_words());
    ops.push(Op::Pod(pod_words));
    iop.commit(&d1);
    ops.push(Op::Commit(*d1.as_words().first_chunk::<8>().unwrap()));
    let b = iop.random_bits(16);
    ops.push(Op::RndBits(16, b));
    let v = iop.random_elem();
    ops.push(Op::RndElem(u32::from(v)));

    // 5. Trailing raw words + final commit + draw: the mix-after-squeeze path.
    let tail: Vec<u32> = (0..3).map(|_| lcg.next_u32() as u32).collect();
    iop.write_u32_slice(&tail);
    ops.push(Op::U32s(tail.clone()));
    iop.commit(&d2);
    ops.push(Op::Commit(*d2.as_words().first_chunk::<8>().unwrap()));
    let v = iop.random_elem();
    ops.push(Op::RndElem(u32::from(v)));

    let proof = iop.proof.clone();

    // Oracle sanity: replay the whole script through risc0-zkp's OWN ReadIOP.
    {
        let mut r = ReadIOP::<BabyBear>::new(&proof, suite.rng.as_ref());
        for op in &ops {
            match op {
                Op::U32s(exp) => assert_eq!(r.read_u32s(exp.len()), exp.as_slice()),
                Op::Elems(exp) => {
                    let got = r.read_field_elem_slice::<BabyBearElem>(exp.len());
                    assert_eq!(canon(got), *exp);
                }
                Op::Pod(exp) => {
                    let got: &[Digest] = r.read_pod_slice(exp.len() / 8);
                    let words: Vec<u32> =
                        got.iter().flat_map(|d| d.as_words().to_vec()).collect();
                    assert_eq!(words, *exp);
                }
                Op::Commit(words) => r.commit(&Digest::from(*words)),
                Op::RndElem(exp) => assert_eq!(u32::from(r.random_elem()), *exp),
                Op::RndBits(bits, exp) => assert_eq!(r.random_bits(*bits), *exp),
                Op::RndExt(exp) => {
                    let e = r.random_ext_elem();
                    let got: Vec<u32> = e.subelems().iter().map(|&x| u32::from(x)).collect();
                    assert_eq!(got, exp.to_vec());
                }
            }
        }
        r.verify_complete();
    }

    let mut s = String::from(
        "# ReadIOP transcript script. Oracle: risc0-zkp 1.2.6 WriteIOP/ReadIOP (Poseidon2 rng).\n\
         # proof: full word stream. ops: u32s:<n> -> raw words | elems:<n> -> canonical values |\n\
         # pod:<n digests> -> raw words | commit:<8 raw words> | elem -> canonical |\n\
         # bits:<n> -> value | ext -> canonical c0,c1,c2,c3 | complete\n",
    );
    s.push_str(&format!("proof:{}\n", join_u32(&proof)));
    for op in &ops {
        match op {
            Op::U32s(w) => s.push_str(&format!("u32s:{} -> {}\n", w.len(), join_u32(w))),
            Op::Elems(v) => s.push_str(&format!("elems:{} -> {}\n", v.len(), join_u32(v))),
            Op::Pod(w) => s.push_str(&format!("pod:{} -> {}\n", w.len() / 8, join_u32(w))),
            Op::Commit(w) => s.push_str(&format!("commit:{}\n", join_u32(w))),
            Op::RndElem(v) => s.push_str(&format!("elem -> {v}\n")),
            Op::RndBits(b, v) => s.push_str(&format!("bits:{b} -> {v}\n")),
            Op::RndExt(c) => s.push_str(&format!("ext -> {}\n", join_u32(c))),
        }
    }
    s.push_str("complete\n");
    fs::write(out.join("readiop_script.tsv"), s).expect("write readiop tsv");
    println!("wrote readiop_script.tsv (oracle-replayed)");
}

// ---------------------------------------------------------------------------
// Part B: Merkle tree vectors
// ---------------------------------------------------------------------------

struct TreeVec {
    rows: usize,
    cols: usize,
    queries: usize,
    proof: Vec<u32>,
    root: [u32; 8],
    /// Per query: (row index drawn from the transcript rng, canonical row).
    query_rows: Vec<(usize, Vec<u32>)>,
}

/// Full oracle replay of a tree vector against its recorded expectations.
/// `wrong_query`: if set, that query verifies with `(idx + 1) % rows`
/// (the upstream bad-query pattern) and the replay "passes" only if the
/// oracle verifier ACCEPTS the wrong row. Returns false on any panic,
/// mismatch with the recorded expectations, or verification error.
fn oracle_replay_ok(v: &TreeVec, proof: &[u32], wrong_query: Option<usize>) -> bool {
    let suite = Poseidon2HashSuite::new_suite();
    let hashfn = suite.hashfn.as_ref();
    catch_unwind(AssertUnwindSafe(|| {
        let mut iop = ReadIOP::<BabyBear>::new(proof, suite.rng.as_ref());
        let verifier = MerkleTreeVerifier::new(&mut iop, hashfn, v.rows, v.cols, v.queries);
        if verifier.root().as_words() != v.root {
            return false;
        }
        for (q, (exp_idx, exp_row)) in v.query_rows.iter().enumerate() {
            let mut idx = iop.random_bits(log2_ceil(v.rows)) as usize;
            if idx != *exp_idx {
                return false;
            }
            if wrong_query == Some(q) {
                idx = (idx + 1) % v.rows;
            }
            match verifier.verify(&mut iop, hashfn, idx) {
                Ok(row) => {
                    if wrong_query.is_none() && canon(row) != *exp_row {
                        return false;
                    }
                }
                Err(_) => return false,
            }
            if wrong_query == Some(q) {
                // Desynced after a wrong-row read; stop like upstream's test.
                return true;
            }
        }
        iop.verify_complete();
        true
    }))
    .unwrap_or(false)
}

fn gen_tree(rows: usize, cols: usize, queries: usize, lcg: &mut Lcg) -> TreeVec {
    let suite = Poseidon2HashSuite::new_suite();
    let hal = CpuHal::new(suite);
    let hs = hal.get_hash_suite();
    let rng_factory = hs.rng.clone();

    // Matrix layout is column-major over rows: value of (row r, col c) lives
    // at index r + c*rows; a leaf hashes its row's `cols` values in column
    // order (exactly the order `prove` writes them).
    let data: Vec<BabyBearElem> = (0..rows * cols)
        .map(|_| BabyBearElem::new(lcg.next_fe()))
        .collect();
    let matrix = hal.copy_from_elem("matrix", &data);
    let prover = MerkleTreeProver::new(&hal, &matrix, rows, cols, queries);

    let mut iop = WriteIOP::<BabyBear>::new(rng_factory.as_ref());
    prover.commit(&mut iop);
    let mut query_rows = Vec::new();
    for _ in 0..queries {
        let idx = iop.rng.random_bits(log2_ceil(rows)) as usize;
        let row = prover.prove(&hal, &mut iop, idx);
        query_rows.push((idx, canon(&row)));
    }
    let v = TreeVec {
        rows,
        cols,
        queries,
        proof: iop.proof.clone(),
        root: *prover.root().as_words().first_chunk::<8>().unwrap(),
        query_rows,
    };
    // Oracle sanity: the positive vector must replay green through
    // risc0-zkp's own MerkleTreeVerifier.
    assert!(
        oracle_replay_ok(&v, &v.proof, None),
        "positive vector failed oracle replay ({rows}x{cols} q{queries})"
    );
    v
}

fn gen_merkle(out: &Path) {
    let mut lcg = Lcg(0xE1900045_00000007);
    let configs: &[(usize, usize, usize)] =
        &[(1, 1, 1), (4, 4, 2), (8, 3, 2), (16, 5, 4), (64, 4, 4)];

    let mut s = String::from(
        "# Merkle tree branch vectors. Oracle: risc0-zkp 1.2.6 MerkleTreeProver/MerkleTreeVerifier\n\
         # (Poseidon2 suite). Per tree: proof = full IOP word stream (top row digests, then per\n\
         # query: row elems + path digests); root = 8 RAW digest words; query:<idx> -> canonical\n\
         # row values, where <idx> = random_bits(log2_ceil(rows)) drawn from the transcript rng\n\
         # AFTER the root commit. Negative vectors are oracle-confirmed rejects:\n\
         # badword:<word_idx>,<xor> (xor one proof word) | truncate:<words kept> |\n\
         # badquery:<q> (verify query q with (idx+1)%rows).\n",
    );

    for &(rows, cols, queries) in configs {
        let v = gen_tree(rows, cols, queries, &mut lcg);
        s.push_str(&format!("tree:{rows},{cols},{queries}\n"));
        s.push_str(&format!("proof:{}\n", join_u32(&v.proof)));
        s.push_str(&format!("root:{}\n", join_u32(&v.root)));
        for (idx, row) in &v.query_rows {
            s.push_str(&format!("query:{idx} -> {}\n", join_u32(row)));
        }
        s.push_str("complete\n");

        // Negative vectors — every one oracle-confirmed as a reject before
        // being emitted (assert!).
        let top_size = top_size_of(rows, queries);
        let mut badwords: Vec<(usize, u32)> = vec![
            // First word of the top row (corrupts a committed digest -> root).
            (0, 1),
            // Last word of the stream (a path digest word, or row data for
            // the 1-row tree).
            (v.proof.len() - 1, 1),
        ];
        if rows > 2 * top_size {
            // First word of the first query's row data, pushed >= 2^31 so the
            // field-element read itself must reject (word >= P).
            badwords.push((top_size * 8, 0x8000_0000));
            // First word of the first query's first path digest.
            badwords.push((top_size * 8 + cols, 1));
        }
        for (pos, xor) in badwords {
            let mut p = v.proof.clone();
            p[pos] ^= xor;
            assert!(
                !oracle_replay_ok(&v, &p, None),
                "badword vector unexpectedly verified ({rows}x{cols} q{queries} pos {pos})"
            );
            s.push_str(&format!("badword:{pos},{xor}\n"));
        }
        let trunc = v.proof.len() - 1;
        {
            let p = &v.proof[..trunc];
            assert!(
                !oracle_replay_ok(&v, p, None),
                "truncated vector unexpectedly verified ({rows}x{cols} q{queries})"
            );
            s.push_str(&format!("truncate:{trunc}\n"));
        }
        if rows > 1 {
            let bad_q = queries - 1;
            assert!(
                !oracle_replay_ok(&v, &v.proof, Some(bad_q)),
                "bad-query vector unexpectedly verified ({rows}x{cols} q{queries})"
            );
            s.push_str(&format!("badquery:{bad_q}\n"));
        }
        s.push_str("endtree\n");
    }

    fs::write(out.join("merkle_kat.tsv"), s).expect("write merkle tsv");
    println!("wrote merkle_kat.tsv (oracle-replayed, negatives oracle-confirmed)");
}

/// Mirror of risc0-zkp `MerkleTreeParams::new` top_size (used only to pick
/// deterministic corruption offsets; the Scala port derives its own).
fn top_size_of(row_size: usize, queries: usize) -> usize {
    let layers = usize::BITS as usize - 1 - row_size.leading_zeros() as usize;
    assert_eq!(1 << layers, row_size);
    let mut top_layer = 0;
    for i in 1..layers {
        if (1 << i) > queries {
            break;
        }
        top_layer = i;
    }
    1 << top_layer
}

fn main() {
    let out = Path::new(OUT_DIR);
    fs::create_dir_all(out).expect("mkdir out");
    gen_readiop_script(out);
    gen_merkle(out);
    println!("merkle/iop KATs generated + oracle-confirmed");
}
