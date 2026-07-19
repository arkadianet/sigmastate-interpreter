//! transcript_capture — record the COMPLETE Fiat-Shamir transcript of the
//! real devnet succinct receipt (`fixtures/proof_inner.bin`) through the
//! risc0-zkp 3.0.4 verifier, without patching any crate.
//!
//! Output: `core/jvm/src/test/resources/stark-kats/transcript_capture.tsv` —
//! an ordered, replayable script of every transcript event from IOP start to
//! accept:
//!   - every `mix(digest)` (raw digest words),
//!   - every `random_elem` / `random_bits(n)` / `random_ext_elem` RESULT,
//!   - every hash-function call (pair / elem-slice / ext-elem-slice) with
//!     full inputs and output,
//!   - labeled `ck` checkpoint lines (group Merkle roots as committed, mix
//!     values, poly_mix / z / FRI mixes, eval_u, constraint `result`,
//!     combo_u, final FRI poly, query positions, claim-digest binding).
//!
//! A Scala verifier that reproduces this event sequence byte-exactly and
//! reaches accept has implemented the whole succinct protocol correctly.
//!
//! How the recording works (report §6): `HashSuite` fields are pub, so we
//! inject wrapper `HashFn`/`Rng` implementations that DELEGATE to RISC0's own
//! Poseidon2 implementations and log every call. Nothing in the verification
//! algebra is reimplemented for the capture itself; the few derived
//! checkpoints (eval_u recompute, check-poly, combo_u) mirror
//! risc0-zkp 3.0.4 `verify/mod.rs` and are asserted against values captured
//! from the live run.
//!
//! Sanity (all hard asserts, printed on success):
//!   1. the untouched entry-point oracle `risc0_verifier::verify(&v3_0(), …)`
//!      ACCEPTS the fixture;
//!   2. the zkp-level `risc0_zkp_v3::verify::verify(&CIRCUIT, plain suite, …)`
//!      ACCEPTS with our reimplemented `check_code` (control-ID inclusion);
//!   3. the same call with the RECORDING suite ACCEPTS (recording does not
//!      perturb verification);
//!   4. a step-by-step `Verifier` driver (feature `unstable`) that interleaves
//!      the checkpoints produces EXACTLY the same event stream as run 3.
//!
//! Determinism: everything derives from the fixed fixture receipt and crate
//! constants — no RNG, no time; re-running is byte-identical.

use std::fs;
use std::path::Path;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use risc0_binfmt::{read_sha_halfs, SystemState};
use risc0_circuit_recursion::{CircuitImpl, CIRCUIT};
use risc0_verifier::receipt_claim::{MaybePruned, Output, ReceiptClaim};
use risc0_verifier::{v3_0, Digestible, InnerReceipt, Journal, Proof, Vk};
use risc0_zkp_v3::adapter::{
    CircuitInfo, PolyExt, TapsProvider, REGISTER_GROUP_ACCUM, REGISTER_GROUP_CODE,
    REGISTER_GROUP_DATA,
};
use risc0_zkp_v3::core::digest::Digest as DigestV3;
use risc0_zkp_v3::core::hash::poseidon2::{Poseidon2HashSuite, Poseidon2Rng};
use risc0_zkp_v3::core::hash::{HashFn, HashSuite, Rng, RngFactory};
use risc0_zkp_v3::field::baby_bear::{BabyBear, BabyBearElem, BabyBearExtElem, P};
use risc0_zkp_v3::field::{Elem, ExtElem, RootsOfUnity};
use risc0_zkp_v3::verify::{verify as zkp_verify, VerificationError, Verifier};
use risc0_zkp_v3::{INV_RATE, QUERIES};

const OUT_DIR: &str = "../core/jvm/src/test/resources/stark-kats";
const FIXTURES: &str = "fixtures";

/// Private const risc0-zkp 3.0.4 src/lib.rs:54 (cited; not importable).
const FRI_MIN_DEGREE: usize = 256;
const FRI_FOLD: usize = risc0_zkp_v3::FRI_FOLD;
const EXT_SIZE: usize = 4;
const CHECK_SIZE: usize = INV_RATE * EXT_SIZE;
const NUM_TAPS: usize = 643;

// ---------------------------------------------------------------------------
// Recording infrastructure
// ---------------------------------------------------------------------------

type EventLog = Arc<Mutex<Vec<String>>>;

/// Structured copies of selected values, stashed by the wrappers alongside
/// the textual event log (`event_idx` = index of the corresponding event
/// line, used to insert labeled `ck` lines at the exact position).
#[derive(Default)]
struct StashData {
    ext_draws: Vec<(usize, BabyBearExtElem)>,
    bits_draws: Vec<(usize, usize, u32)>,
    /// The single 659-ext-elem hash input (coeff_u = 643 taps + 16 check).
    coeff_u: Vec<(usize, Vec<BabyBearExtElem>)>,
    /// Elem-slice hash inputs of the FRI final-poly length (labeled later).
    final_poly: Vec<(usize, Vec<BabyBearElem>)>,
}

type Stash = Arc<Mutex<StashData>>;

fn fmt_words(words: &[u32]) -> String {
    words
        .iter()
        .map(|w| w.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn fmt_elems(elems: &[BabyBearElem]) -> String {
    elems
        .iter()
        .map(|e| e.as_u32().to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn fmt_ext(e: &BabyBearExtElem) -> String {
    fmt_elems(e.subelems())
}

fn fmt_exts(elems: &[BabyBearExtElem]) -> String {
    elems.iter().map(fmt_ext).collect::<Vec<_>>().join(",")
}

struct RecordingRng {
    inner: Poseidon2Rng,
    log: EventLog,
    stash: Stash,
}

impl Rng<BabyBear> for RecordingRng {
    fn mix(&mut self, val: &DigestV3) {
        self.log
            .lock()
            .unwrap()
            .push(format!("mix\t{}", fmt_words(val.as_words())));
        self.inner.mix(val);
    }

    fn random_bits(&mut self, bits: usize) -> u32 {
        let v = self.inner.random_bits(bits);
        let mut log = self.log.lock().unwrap();
        log.push(format!("bits\t{bits}\t{v}"));
        self.stash
            .lock()
            .unwrap()
            .bits_draws
            .push((log.len() - 1, bits, v));
        v
    }

    fn random_elem(&mut self) -> BabyBearElem {
        let v = self.inner.random_elem();
        self.log
            .lock()
            .unwrap()
            .push(format!("elem\t{}", v.as_u32()));
        v
    }

    fn random_ext_elem(&mut self) -> BabyBearExtElem {
        let v = self.inner.random_ext_elem();
        let mut log = self.log.lock().unwrap();
        log.push(format!("ext\t{}", fmt_ext(&v)));
        self.stash
            .lock()
            .unwrap()
            .ext_draws
            .push((log.len() - 1, v));
        v
    }
}

struct RecordingRngFactory {
    log: EventLog,
    stash: Stash,
}

impl RngFactory<BabyBear> for RecordingRngFactory {
    fn new_rng(&self) -> Box<dyn Rng<BabyBear>> {
        Box::new(RecordingRng {
            inner: Poseidon2Rng::new(),
            log: self.log.clone(),
            stash: self.stash.clone(),
        })
    }
}

struct RecordingHashFn {
    /// RISC0's own Poseidon2 hash fn (the concrete type is private, so we
    /// hold the suite's `Rc<dyn HashFn>`); every call delegates.
    inner: Rc<dyn HashFn<BabyBear>>,
    log: EventLog,
    stash: Stash,
}

// SAFETY: `HashFn` declares Send + Sync supertraits, but this generator is
// strictly single-threaded (risc0-zkp's verifier never spawns threads); the
// inner `Rc` never crosses a thread boundary.
unsafe impl Send for RecordingHashFn {}
unsafe impl Sync for RecordingHashFn {}

impl HashFn<BabyBear> for RecordingHashFn {
    fn hash_pair(&self, a: &DigestV3, b: &DigestV3) -> Box<DigestV3> {
        let out = self.inner.hash_pair(a, b);
        self.log.lock().unwrap().push(format!(
            "hash_pair\t{}\t{}\t{}",
            fmt_words(a.as_words()),
            fmt_words(b.as_words()),
            fmt_words(out.as_words())
        ));
        out
    }

    fn hash_elem_slice(&self, slice: &[BabyBearElem]) -> Box<DigestV3> {
        let out = self.inner.hash_elem_slice(slice);
        let mut log = self.log.lock().unwrap();
        log.push(format!(
            "hash_elems\t{}\t{}\t{}",
            slice.len(),
            fmt_elems(slice),
            fmt_words(out.as_words())
        ));
        self.stash
            .lock()
            .unwrap()
            .final_poly
            .push((log.len() - 1, slice.to_vec()));
        out
    }

    fn hash_ext_elem_slice(&self, slice: &[BabyBearExtElem]) -> Box<DigestV3> {
        let out = self.inner.hash_ext_elem_slice(slice);
        let mut log = self.log.lock().unwrap();
        log.push(format!(
            "hash_ext_elems\t{}\t{}\t{}",
            slice.len(),
            fmt_exts(slice),
            fmt_words(out.as_words())
        ));
        if slice.len() == NUM_TAPS + CHECK_SIZE {
            self.stash
                .lock()
                .unwrap()
                .coeff_u
                .push((log.len() - 1, slice.to_vec()));
        }
        out
    }

    fn is_digest_valid(&self, digest: &DigestV3) -> bool {
        // Not logged (pure predicate), but MUST delegate: the Poseidon2
        // override rejects non-reduced words and is part of verification.
        self.inner.is_digest_valid(digest)
    }
}

fn recording_suite(log: EventLog, stash: Stash) -> HashSuite<BabyBear> {
    let plain = Poseidon2HashSuite::new_suite();
    HashSuite {
        name: plain.name.clone(),
        hashfn: Rc::new(RecordingHashFn {
            inner: plain.hashfn,
            log: log.clone(),
            stash: stash.clone(),
        }),
        rng: Rc::new(RecordingRngFactory { log, stash }),
    }
}

// ---------------------------------------------------------------------------
// check_code: control-ID inclusion proof against ALLOWED_CONTROL_ROOT
// (reimplements zkVerify RV/receipt/merkle.rs MerkleProof::root at the
// risc0-zkp-v3 layer; hash calls go through the given suite so the recorded
// runs include them, exactly like zkVerify's HashFnWrapper does)
// ---------------------------------------------------------------------------

fn inclusion_root(
    leaf: &DigestV3,
    index: u32,
    siblings: &[DigestV3],
    hashfn: &dyn HashFn<BabyBear>,
) -> DigestV3 {
    let mut cur = *leaf;
    let mut cur_index = index;
    for sibling in siblings {
        cur = if cur_index & 1 == 0 {
            *hashfn.hash_pair(&cur, sibling)
        } else {
            *hashfn.hash_pair(sibling, &cur)
        };
        cur_index >>= 1;
    }
    cur
}

fn digest_v1_to_v3(d: &risc0_verifier::Digest) -> DigestV3 {
    let words: [u32; 8] = d.as_words().try_into().expect("8-word digest");
    DigestV3::from(words)
}

// ---------------------------------------------------------------------------
// Shared helpers mirroring risc0-zkp 3.0.4 verify/mod.rs (for derived
// checkpoints; every derived value is asserted against the captured run)
// ---------------------------------------------------------------------------

fn poly_eval(coeffs: &[BabyBearExtElem], x: BabyBearExtElem) -> BabyBearExtElem {
    let mut mul_x = BabyBearExtElem::ONE;
    let mut tot = BabyBearExtElem::ZERO;
    for coeff in coeffs {
        tot += *coeff * mul_x;
        mul_x *= x;
    }
    tot
}

fn main() {
    let out_dir = Path::new(OUT_DIR);
    fs::create_dir_all(out_dir).expect("mkdir out");

    // ----- fixtures -----
    let proof_bytes = fs::read(format!("{FIXTURES}/proof_inner.bin")).expect("proof fixture");
    let journal_bytes = fs::read(format!("{FIXTURES}/journal.bin")).expect("journal fixture");
    let image_id_bytes: [u8; 32] = fs::read(format!("{FIXTURES}/image_id.bin"))
        .expect("image id fixture")
        .as_slice()
        .try_into()
        .expect("32-byte image id");

    let inner: InnerReceipt = bincode::deserialize(&proof_bytes).expect("bincode InnerReceipt");
    let succinct = inner.succinct().expect("succinct receipt").clone();
    assert_eq!(succinct.hashfn, "poseidon2", "receipt hash suite");

    // ----- sanity 1: untouched entry-point oracle accepts -----
    let vk: Vk = image_id_bytes.into();
    risc0_verifier::verify(
        &v3_0(),
        vk,
        Proof::new(inner.clone()),
        Journal::new(journal_bytes.clone()),
    )
    .expect("sanity 1: risc0_verifier::verify(v3_0) must accept the fixture");
    println!("sanity 1 OK: risc0-verifier v0.11.0 entry point accepts proof_inner.bin");

    let seal: &[u32] = &succinct.seal;
    // ALLOWED_CONTROL_ROOT is already a v3 digest (risc0-circuit-recursion
    // 4.0.4 links risc0-zkp 3.0.4 types directly).
    let control_root: DigestV3 = risc0_circuit_recursion::control_id::ALLOWED_CONTROL_ROOT;
    let incl_index = succinct.control_inclusion_proof.index;
    let incl_digests: Vec<DigestV3> = succinct
        .control_inclusion_proof
        .digests
        .iter()
        .map(digest_v1_to_v3)
        .collect();
    let control_id_v3 = digest_v1_to_v3(&succinct.control_id);

    let make_check_code = |hashfn: Rc<dyn HashFn<BabyBear>>| {
        let incl_digests = incl_digests.clone();
        move |_po2: u32, code_root: &DigestV3| -> Result<(), VerificationError> {
            if inclusion_root(code_root, incl_index, &incl_digests, hashfn.as_ref()) == control_root
            {
                Ok(())
            } else {
                Err(VerificationError::ControlVerificationError {
                    control_id: *code_root,
                })
            }
        }
    };

    // ----- sanity 2: zkp-level verify with plain suite accepts -----
    let plain = Poseidon2HashSuite::new_suite();
    zkp_verify(
        &CIRCUIT,
        &plain,
        seal,
        make_check_code(plain.hashfn.clone()),
    )
    .expect("sanity 2: risc0-zkp 3.0.4 verify (plain suite) must accept");
    println!("sanity 2 OK: zkp-level verify accepts with reimplemented check_code");

    // ----- sanity 3 / run A: recording suite, untouched verify() driver -----
    let log_a: EventLog = Default::default();
    let stash_a: Stash = Default::default();
    let suite_a = recording_suite(log_a.clone(), stash_a.clone());
    zkp_verify(
        &CIRCUIT,
        &suite_a,
        seal,
        make_check_code(suite_a.hashfn.clone()),
    )
    .expect("sanity 3: recording suite must not perturb verification");
    let events_a = log_a.lock().unwrap().clone();
    println!(
        "sanity 3 OK: recording suite accepts; {} transcript events",
        events_a.len()
    );

    // ----- run B: step-by-step Verifier driver with checkpoints -----
    // Mirrors risc0-zkp 3.0.4 verify/mod.rs `verify` (lines 495-556) exactly;
    // the `unstable` feature exposes the Verifier building blocks.
    let log_b: EventLog = Default::default();
    let stash_b: Stash = Default::default();
    let suite_b = recording_suite(log_b.clone(), stash_b.clone());
    let check_code_b = make_check_code(suite_b.hashfn.clone());
    let ck = |line: String| log_b.lock().unwrap().push(format!("ck\t{line}"));

    let taps = CIRCUIT.get_taps();
    assert!(!seal.is_empty());
    ck(format!("seal_words\t{}", seal.len()));

    let mut verifier = Verifier::<BabyBear>::new(taps, &suite_b, seal);
    verifier.commit_circuit_info(&<CircuitImpl as CircuitInfo>::CIRCUIT_INFO);

    let (out, po2) = verifier
        .read_slice_with_po2(<CircuitImpl as CircuitInfo>::OUTPUT_SIZE)
        .expect("read_slice_with_po2");
    let tot_cycles = 1usize << po2;
    let domain = INV_RATE * tot_cycles;
    ck(format!("po2\t{po2}"));
    ck(format!("tot_cycles\t{tot_cycles}"));
    ck(format!("domain\t{domain}"));
    ck(format!("out\t{}", fmt_elems(out)));

    let code_root = *verifier
        .verify_group(REGISTER_GROUP_CODE)
        .expect("code group");
    ck(format!(
        "group_root\tcode\t{}",
        fmt_words(code_root.as_words())
    ));
    assert_eq!(
        code_root, control_id_v3,
        "code_root from seal must equal the receipt's control_id"
    );
    check_code_b(po2 as u32, &code_root).expect("control-ID inclusion proof");
    ck(format!(
        "control_id_included\t{}",
        hex::encode(code_root.as_bytes())
    ));

    let data_root = *verifier
        .verify_group(REGISTER_GROUP_DATA)
        .expect("data group");
    ck(format!(
        "group_root\tdata\t{}",
        fmt_words(data_root.as_words())
    ));

    let mix = verifier.read_rng(<CircuitImpl as CircuitInfo>::MIX_SIZE);
    ck(format!("mix\t{}", fmt_elems(&mix)));

    let accum_root = *verifier
        .verify_group(REGISTER_GROUP_ACCUM)
        .expect("accum group");
    ck(format!(
        "group_root\taccum\t{}",
        fmt_words(accum_root.as_words())
    ));

    /// Values captured from inside the validity closure: (poly_mix, eval_u,
    /// constraint result).
    type ValidityCapture = Option<(BabyBearExtElem, Vec<BabyBearExtElem>, BabyBearExtElem)>;
    let captured: Arc<Mutex<ValidityCapture>> = Default::default();
    {
        let captured = captured.clone();
        let log_b = log_b.clone();
        verifier
            .verify_validity(|poly_mix, eval_u| {
                let result = CIRCUIT.poly_ext(poly_mix, eval_u, &[out, &mix]).tot;
                let mut log = log_b.lock().unwrap();
                log.push(format!("ck\tpoly_mix\t{}", fmt_ext(poly_mix)));
                log.push(format!(
                    "ck\teval_u\t{}\t{}",
                    eval_u.len(),
                    fmt_exts(eval_u)
                ));
                log.push(format!("ck\tresult\t{}", fmt_ext(&result)));
                *captured.lock().unwrap() = Some((*poly_mix, eval_u.to_vec(), result));
                result
            })
            .expect("verify_validity");
    }
    verifier
        .iop()
        .verify_complete()
        .expect("seal fully consumed");
    let (poly_mix, eval_u, result) = captured.lock().unwrap().clone().expect("closure ran");
    println!("run B OK: step-by-step driver accepts (po2={po2}, domain={domain})");

    // ----- driver fidelity: run B's raw events == run A's events -----
    let events_b_all = log_b.lock().unwrap().clone();
    let events_b_raw: Vec<&String> = events_b_all
        .iter()
        .filter(|l| !l.starts_with("ck\t"))
        .collect();
    assert_eq!(
        events_a.len(),
        events_b_raw.len(),
        "driver event count differs from untouched verify()"
    );
    for (i, (a, b)) in events_a.iter().zip(events_b_raw.iter()).enumerate() {
        assert_eq!(&a, b, "driver event {i} differs from untouched verify()");
    }
    println!(
        "driver fidelity OK: {} raw events identical to untouched verify()",
        events_a.len()
    );

    // ----- derived checkpoints (each asserted against the captured run) -----
    let stash = std::mem::take(&mut *stash_b.lock().unwrap());

    // FRI round structure at this po2.
    let mut fri_rounds = 0usize;
    let mut degree = tot_cycles;
    while degree > FRI_MIN_DEGREE {
        fri_rounds += 1;
        degree /= FRI_FOLD;
    }
    let final_degree = degree;

    // The verify protocol draws ext elems exactly: poly_mix, z,
    // fri_batch_mix, then one per FRI round.
    let ext_labels: Vec<String> = ["poly_mix", "z", "fri_batch_mix"]
        .iter()
        .map(|s| s.to_string())
        .chain((0..fri_rounds).map(|i| format!("fri_round_mix_{i}")))
        .collect();
    assert_eq!(
        stash.ext_draws.len(),
        ext_labels.len(),
        "random_ext_elem draw count"
    );
    assert_eq!(stash.ext_draws[0].1, poly_mix, "first ext draw is poly_mix");
    let z = stash.ext_draws[1].1;

    // Query positions: the only random_bits draws, log2(domain) bits each.
    let pos_bits = domain.ilog2() as usize;
    assert_eq!(stash.bits_draws.len(), QUERIES, "query-position draw count");
    for (_, bits, v) in &stash.bits_draws {
        assert_eq!(*bits, pos_bits, "query position bit width");
        assert!((*v as usize) < domain, "query position in range");
    }

    // coeff_u: the single 659-ext-elem hash input.
    assert_eq!(stash.coeff_u.len(), 1, "exactly one coeff_u-sized hash");
    let (coeff_u_idx, coeff_u) = &stash.coeff_u[0];
    assert_eq!(coeff_u.len(), NUM_TAPS + CHECK_SIZE);

    // Recompute eval_u from coeff_u (mirrors verify/mod.rs:334-344).
    let back_one = <BabyBearElem as RootsOfUnity>::ROU_REV[po2];
    let mut recomputed_eval_u = Vec::with_capacity(NUM_TAPS);
    let mut cur_pos = 0usize;
    for reg in taps.regs() {
        for i in 0..reg.size() {
            let x = z * back_one.pow(reg.back(i));
            recomputed_eval_u.push(poly_eval(&coeff_u[cur_pos..cur_pos + reg.size()], x));
        }
        cur_pos += reg.size();
    }
    assert_eq!(recomputed_eval_u, eval_u, "eval_u recompute from coeff_u");

    // Recompute the check polynomial (mirrors verify/mod.rs:360-381) and
    // assert it equals the captured constraint result.
    let mut check = BabyBearExtElem::ZERO;
    let remap = [0usize, 2, 1, 3];
    let fp0 = BabyBearElem::ZERO;
    let fp1 = BabyBearElem::ONE;
    for (i, rmi) in remap.iter().enumerate() {
        check += coeff_u[NUM_TAPS + rmi]
            * z.pow(i)
            * BabyBearExtElem::from_subelems([fp1, fp0, fp0, fp0]);
        check += coeff_u[NUM_TAPS + rmi + 4]
            * z.pow(i)
            * BabyBearExtElem::from_subelems([fp0, fp1, fp0, fp0]);
        check += coeff_u[NUM_TAPS + rmi + 8]
            * z.pow(i)
            * BabyBearExtElem::from_subelems([fp0, fp0, fp1, fp0]);
        check += coeff_u[NUM_TAPS + rmi + 12]
            * z.pow(i)
            * BabyBearExtElem::from_subelems([fp0, fp0, fp0, fp1]);
    }
    let three = BabyBearElem::from_u64(3);
    check *= (BabyBearExtElem::from_subfield(&three) * z).pow(tot_cycles) - BabyBearExtElem::ONE;
    assert_eq!(check, result, "check polynomial == constraint result");

    // Recompute combo_u (mirrors verify/mod.rs:397-428).
    let fri_batch_mix = stash.ext_draws[2].1;
    let mut combo_u = vec![BabyBearExtElem::ZERO; taps.tot_combo_backs + 1];
    let mut cur_mix = BabyBearExtElem::ONE;
    cur_pos = 0;
    for reg in taps.regs() {
        for i in 0..reg.size() {
            combo_u[taps.combo_begin[reg.combo_id()] as usize + i] +=
                cur_mix * coeff_u[cur_pos + i];
        }
        cur_mix *= fri_batch_mix;
        cur_pos += reg.size();
    }
    for _ in 0..CHECK_SIZE {
        combo_u[taps.tot_combo_backs] += cur_mix * coeff_u[cur_pos];
        cur_pos += 1;
        cur_mix *= fri_batch_mix;
    }

    // Final FRI polynomial: the elem-slice hash input of length
    // EXT_SIZE * final_degree that follows the last FRI round commit.
    let final_len = EXT_SIZE * final_degree;
    let finals: Vec<&(usize, Vec<BabyBearElem>)> = stash
        .final_poly
        .iter()
        .filter(|(_, v)| v.len() == final_len)
        .collect();
    assert_eq!(
        finals.len(),
        1,
        "exactly one {final_len}-elem hash (FRI final poly)"
    );
    let (final_poly_idx, final_poly) = finals[0];

    // ----- assemble labeled output: insert derived ck lines in order -----
    let mut insertions: Vec<(usize, String)> = Vec::new();
    for ((idx, v), label) in stash.ext_draws.iter().zip(ext_labels.iter()) {
        // poly_mix already has a ck line from the closure at the right spot.
        if label != "poly_mix" {
            insertions.push((*idx, format!("ck\t{label}\t{}", fmt_ext(v))));
        }
    }
    for (q, (idx, _, v)) in stash.bits_draws.iter().enumerate() {
        insertions.push((*idx, format!("ck\tquery\t{q}\tpos\t{v}")));
    }
    insertions.push((
        *coeff_u_idx,
        format!("ck\tcoeff_u_committed\t{}", coeff_u.len()),
    ));
    insertions.push((
        *final_poly_idx,
        format!(
            "ck\tfinal_poly\t{}\t{}",
            final_poly.len(),
            fmt_elems(final_poly)
        ),
    ));
    // combo_u is derived after fri_batch_mix is drawn; insert right after it.
    insertions.push((
        stash.ext_draws[2].0,
        format!("ck\tcombo_u\t{}\t{}", combo_u.len(), fmt_exts(&combo_u)),
    ));
    insertions.sort_by_key(|(idx, _)| *idx);

    let mut lines: Vec<String> = Vec::with_capacity(events_b_all.len() + insertions.len());
    let mut ins_iter = insertions.into_iter().peekable();
    for (idx, line) in events_b_all.iter().enumerate() {
        lines.push(line.clone());
        while ins_iter.peek().is_some_and(|(i, _)| *i == idx) {
            lines.push(ins_iter.next().unwrap().1);
        }
    }
    assert!(ins_iter.next().is_none(), "all insertions consumed");
    lines.push(format!("ck\tcheck_value\t{}", fmt_ext(&check)));

    // ----- claim binding (outside the zkp core; report §2) -----
    // Output slots: first 32 seal elems (Montgomery words -> standard u32).
    let out_elems: Vec<u32> = seal[..32]
        .iter()
        .map(|w| {
            assert!(*w < P, "seal output word reduced");
            BabyBearElem::new_raw(*w).as_u32()
        })
        .collect();
    let seal_control_root_words: Vec<u32> = out_elems[..16]
        .iter()
        .enumerate()
        .filter_map(|(i, w)| (i % 2 == 0).then_some(*w))
        .collect();
    let seal_control_root =
        DigestV3::from(<[u32; 8]>::try_from(seal_control_root_words.as_slice()).expect("8 words"));
    assert_eq!(
        seal_control_root, control_root,
        "control root read from seal output == ALLOWED_CONTROL_ROOT (inner_control_root = None)"
    );
    let mut halfs: std::collections::VecDeque<u32> = out_elems[16..32].iter().copied().collect();
    let seal_output_hash = read_sha_halfs(&mut halfs).expect("read_sha_halfs");
    let claim_digest = succinct.claim.digest();
    assert_eq!(
        seal_output_hash, claim_digest,
        "seal output hash == receipt claim digest"
    );

    let journal_digest = Journal::new(journal_bytes.clone()).digest();
    let image_id_digest = risc0_verifier::Digest::from(image_id_bytes);
    let expected_claim = ReceiptClaim::ok(image_id_digest, MaybePruned::Pruned(journal_digest));
    let expected_claim_digest = expected_claim.digest();
    assert_eq!(
        expected_claim_digest, claim_digest,
        "expected claim (image_id + journal) == receipt claim"
    );
    // Sub-digests for incremental Scala testing of the tagged-struct hasher.
    let post_state = SystemState {
        pc: 0,
        merkle_root: risc0_verifier::Digest::ZERO,
    };
    let output_struct = Output {
        journal: MaybePruned::<Vec<u8>>::Pruned(journal_digest),
        assumptions: MaybePruned::Pruned(risc0_verifier::Digest::ZERO),
    };

    let mut ck2 = |label: &str, v: String| lines.push(format!("ck\t{label}\t{v}"));
    ck2("hashfn", succinct.hashfn.clone());
    ck2(
        "verifier_parameters",
        hex::encode(succinct.verifier_parameters.as_bytes()),
    );
    ck2("control_id", hex::encode(succinct.control_id.as_bytes()));
    ck2("control_inclusion_index", incl_index.to_string());
    ck2(
        "control_inclusion_digests",
        incl_digests
            .iter()
            .map(|d| hex::encode(d.as_bytes()))
            .collect::<Vec<_>>()
            .join(","),
    );
    ck2("allowed_control_root", hex::encode(control_root.as_bytes()));
    ck2(
        "seal_control_root",
        hex::encode(seal_control_root.as_bytes()),
    );
    ck2("seal_output_hash", hex::encode(seal_output_hash.as_bytes()));
    ck2("journal_sha256", hex::encode(journal_digest.as_bytes()));
    ck2("image_id", hex::encode(image_id_digest.as_bytes()));
    ck2(
        "post_system_state_digest",
        hex::encode(post_state.digest().as_bytes()),
    );
    ck2(
        "output_digest",
        hex::encode(output_struct.digest().as_bytes()),
    );
    ck2("claim_digest", hex::encode(claim_digest.as_bytes()));
    ck2(
        "expected_claim_digest",
        hex::encode(expected_claim_digest.as_bytes()),
    );
    ck2("verdict", "accept".to_string());

    // ----- header + write -----
    let n_mix = lines.iter().filter(|l| l.starts_with("mix\t")).count();
    let n_elem = lines.iter().filter(|l| l.starts_with("elem\t")).count();
    let n_bits = lines.iter().filter(|l| l.starts_with("bits\t")).count();
    let n_ext = lines.iter().filter(|l| l.starts_with("ext\t")).count();
    let n_pair = lines
        .iter()
        .filter(|l| l.starts_with("hash_pair\t"))
        .count();
    let n_he = lines
        .iter()
        .filter(|l| l.starts_with("hash_elems\t"))
        .count();
    let n_hee = lines
        .iter()
        .filter(|l| l.starts_with("hash_ext_elems\t"))
        .count();
    assert_eq!(n_ext, 3 + fri_rounds);
    assert_eq!(n_bits, QUERIES);
    assert_eq!(
        n_elem,
        <CircuitImpl as CircuitInfo>::MIX_SIZE,
        "top-level random_elem draws are exactly the accum mix"
    );
    // Commits: 2 info strings + out/po2 slice + 3 group roots + check root +
    // coeff_u hash + FRI round roots + final-poly hash.
    assert_eq!(n_mix, 2 + 1 + 3 + 1 + 1 + fri_rounds + 1, "mix event count");

    let header = format!(
        "# transcript_capture.tsv — full Fiat-Shamir transcript of the REAL devnet succinct\n\
         # receipt (proof_inner.bin) through risc0-zkp 3.0.4 verify with the recursion circuit\n\
         # (risc0-circuit-recursion 4.0.4), Poseidon2 suite. Recording wrappers delegate to\n\
         # RISC0's own implementations; the untouched verifier ACCEPTS through the identical\n\
         # code path (asserted at generation time). See circuit_tables.md for the schema.\n\
         # po2={po2} tot_cycles={tot_cycles} domain={domain} queries={QUERIES} fri_rounds={fri_rounds} final_degree={final_degree}\n\
         # events: mix={n_mix} elem={n_elem} bits={n_bits} ext={n_ext} hash_pair={n_pair} hash_elems={n_he} hash_ext_elems={n_hee}\n\
         # NOTE digest words (mix inputs, hash_pair in/out, hash_* out) are RAW Digest u32 words\n\
         # (Poseidon2 digests carry Montgomery-form residues); field-element values (elem/ext/bits\n\
         # results, hash_elems/hash_ext_elems inputs, ck elems) are STANDARD-form u32 (as_u32).\n"
    );
    let mut body = header;
    for line in &lines {
        body.push_str(line);
        body.push('\n');
    }
    fs::write(out_dir.join("transcript_capture.tsv"), &body).expect("write transcript_capture.tsv");
    println!(
        "wrote transcript_capture.tsv: {} lines ({} raw events, {} ck lines), {} bytes",
        lines.len(),
        events_a.len(),
        lines.len() - events_a.len(),
        body.len()
    );
    println!("transcript captured + verified: all sanity assertions passed");
}
