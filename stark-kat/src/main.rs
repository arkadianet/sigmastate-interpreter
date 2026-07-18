//! KAT generator for the EIP-0045 verifyStark JVM verifier.
//!
//! Every vector is produced by an EXTERNAL oracle:
//!  - field / extension-field / Poseidon2 vectors: risc0-core / risc0-zkp
//!    (RISC0's own production implementations),
//!  - receipt vectors: risc0-verifier v0.11.0 (zkVerify), the same crate at
//!    the same tag the Rust Ergo node's verifyStark spike links — so the
//!    accept vector here is bit-identical to what a live devnet validates.
//!
//! The Scala verifier under test NEVER produces an expected value here
//! (oracle-parity rule: self-oracles prove consistency, not correctness).
//!
//! Determinism: no RNG — inputs derive from a fixed LCG seed so re-running
//! the generator reproduces byte-identical vectors.

use std::fs;
use std::path::Path;

use blake2::digest::{consts::U32, Digest};
use blake2::Blake2b;
use risc0_core::field::baby_bear::{BabyBearElem, BabyBearExtElem, P};
use risc0_core::field::{Elem, ExtElem};
use risc0_zkp::core::hash::poseidon2::{poseidon2_mix, CELLS};
use serde::Serialize;

type Blake2b256 = Blake2b<U32>;

const OUT_DIR: &str = "../core/jvm/src/test/resources/stark-kats";
const FIXTURES: &str = "fixtures";

/// Deterministic 32-bit LCG (Numerical Recipes constants) — reproducible
/// pseudo-random field elements without an RNG dependency.
struct Lcg(u64);
impl Lcg {
    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 32) as u32
    }
    fn next_fe(&mut self) -> u32 {
        self.next_u32() % P
    }
}

#[derive(Serialize)]
struct BabyBearCase {
    a: u32,
    b: u32,
    add: u32,
    sub: u32,
    mul: u32,
    neg_a: u32,
    inv_a: Option<u32>,
    pow_a_b: u32,
}

#[derive(Serialize)]
struct BabyBearKat {
    description: &'static str,
    modulus: u32,
    oracle: &'static str,
    cases: Vec<BabyBearCase>,
}

fn u32_of(e: BabyBearElem) -> u32 {
    u32::from(e)
}

fn gen_babybear(out: &Path) {
    let mut lcg = Lcg(0xE1900045_00000001);
    let mut inputs: Vec<(u32, u32)> = vec![
        (0, 0),
        (0, 1),
        (1, 1),
        (P - 1, 1),
        (P - 1, P - 1),
        (1 << 27, 15),
        (2, P - 2),
    ];
    for _ in 0..57 {
        inputs.push((lcg.next_fe(), lcg.next_fe()));
    }
    let cases = inputs
        .into_iter()
        .map(|(a, b)| {
            let (ea, eb) = (BabyBearElem::new(a), BabyBearElem::new(b));
            BabyBearCase {
                a,
                b,
                add: u32_of(ea + eb),
                sub: u32_of(ea - eb),
                mul: u32_of(ea * eb),
                neg_a: u32_of(-ea),
                inv_a: if a % P == 0 { None } else { Some(u32_of(ea.inv())) },
                pow_a_b: u32_of(ea.pow(b as usize)),
            }
        })
        .collect();
    let kat = BabyBearKat {
        description: "BabyBear base-field ops; p = 15*2^27+1 = 2013265921. Oracle: risc0-core 1.2.6.",
        modulus: P,
        oracle: "risc0-core 1.2.6 field::baby_bear::Elem",
        cases,
    };
    write_json(out, "babybear_ops.json", &kat);
}

#[derive(Serialize)]
struct Ext4Case {
    a: [u32; 4],
    b: [u32; 4],
    add: [u32; 4],
    mul: [u32; 4],
    inv_a: Option<[u32; 4]>,
}

#[derive(Serialize)]
struct Ext4Kat {
    description: &'static str,
    /// risc0-core baby_bear.rs: extension is x^4 + BETA with BETA = 11;
    /// coefficient order is [c0, c1, c2, c3] (c0 = subfield part).
    irreducible: &'static str,
    oracle: &'static str,
    cases: Vec<Ext4Case>,
}

fn ext_of(c: [u32; 4]) -> BabyBearExtElem {
    BabyBearExtElem::new(
        BabyBearElem::new(c[0]),
        BabyBearElem::new(c[1]),
        BabyBearElem::new(c[2]),
        BabyBearElem::new(c[3]),
    )
}

fn arr_of(e: BabyBearExtElem) -> [u32; 4] {
    let s = e.subelems();
    [u32_of(s[0]), u32_of(s[1]), u32_of(s[2]), u32_of(s[3])]
}

fn gen_ext4(out: &Path) {
    let mut lcg = Lcg(0xE1900045_00000002);
    let mut inputs: Vec<([u32; 4], [u32; 4])> = vec![
        ([0; 4], [0; 4]),
        ([1, 0, 0, 0], [1, 0, 0, 0]),
        ([0, 1, 0, 0], [0, 1, 0, 0]), // x * x = x^2
        ([0, 0, 1, 0], [0, 0, 1, 0]), // x^2 * x^2 = x^4 -> reduction visible
        ([P - 1, P - 1, P - 1, P - 1], [1, 2, 3, 4]),
    ];
    for _ in 0..43 {
        let a = [lcg.next_fe(), lcg.next_fe(), lcg.next_fe(), lcg.next_fe()];
        let b = [lcg.next_fe(), lcg.next_fe(), lcg.next_fe(), lcg.next_fe()];
        inputs.push((a, b));
    }
    let cases = inputs
        .into_iter()
        .map(|(a, b)| {
            let (ea, eb) = (ext_of(a), ext_of(b));
            let zero = a.iter().all(|&c| c % P == 0);
            Ext4Case {
                a,
                b,
                add: arr_of(ea + eb),
                mul: arr_of(ea * eb),
                inv_a: if zero { None } else { Some(arr_of(ea.inv())) },
            }
        })
        .collect();
    let kat = Ext4Kat {
        description: "BabyBear degree-4 extension ops. Oracle: risc0-core 1.2.6.",
        irreducible: "x^4 + 11 (risc0-core baby_bear.rs BETA = 11), coeffs [c0,c1,c2,c3]",
        oracle: "risc0-core 1.2.6 field::baby_bear::ExtElem",
        cases,
    };
    write_json(out, "ext4_ops.json", &kat);
}

#[derive(Serialize)]
struct PoseidonCase {
    input: Vec<u32>,
    output: Vec<u32>,
}

#[derive(Serialize)]
struct PoseidonKat {
    description: &'static str,
    width: usize,
    oracle: &'static str,
    cases: Vec<PoseidonCase>,
}

fn gen_poseidon2(out: &Path) {
    let mut lcg = Lcg(0xE1900045_00000003);
    let mut inputs: Vec<Vec<u32>> = vec![
        vec![0; CELLS],
        {
            let mut v = vec![0; CELLS];
            v[0] = 1;
            v
        },
        (0..CELLS as u32).collect(),
    ];
    for _ in 0..13 {
        inputs.push((0..CELLS).map(|_| lcg.next_fe()).collect());
    }
    let cases = inputs
        .into_iter()
        .map(|input| {
            let mut cells: [BabyBearElem; CELLS] =
                core::array::from_fn(|i| BabyBearElem::new(input[i]));
            poseidon2_mix(&mut cells);
            PoseidonCase {
                input,
                output: cells.iter().map(|&e| u32_of(e)).collect(),
            }
        })
        .collect();
    let kat = PoseidonKat {
        description: "Poseidon2-BabyBear width-24 full permutation (poseidon2_mix). Oracle: risc0-zkp 1.2.6.",
        width: CELLS,
        oracle: "risc0-zkp 1.2.6 core::hash::poseidon2::poseidon2_mix",
        cases,
    };
    write_json(out, "poseidon2_perm.json", &kat);
}

#[derive(Serialize)]
struct Mutation {
    description: String,
    /// Byte offset XORed with `xor` (applied to a fresh copy of the proof),
    /// or `truncate_to` bytes kept. Exactly one of xor/truncate applies.
    offset: Option<usize>,
    xor: Option<u8>,
    truncate_to: Option<usize>,
    mutate_image_id: bool,
    expected: bool,
    /// Confirmed by actually running the oracle verifier on the mutated input.
    oracle_confirmed: bool,
}

#[derive(Serialize)]
struct ReceiptKat {
    description: &'static str,
    oracle: &'static str,
    verifier_context: &'static str,
    proof_file: &'static str,
    proof_len: usize,
    proof_blake2b256: String,
    image_id_hex: String,
    journal_hex: String,
    expected: bool,
    mutations: Vec<Mutation>,
}

fn oracle_verify(proof: &[u8], journal: &[u8], image_id: &[u8; 32]) -> bool {
    use risc0_verifier::{v3_0, verify, Journal, Proof, Vk};
    let inner: risc0_verifier::InnerReceipt = match bincode::deserialize(proof) {
        Ok(r) => r,
        Err(_) => return false,
    };
    let vk: Vk = (*image_id).into();
    let journal = Journal::new(journal.to_vec());
    let proof = Proof::new(inner);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify(&v3_0(), vk, proof, journal).is_ok()
    }))
    .unwrap_or(false)
}

fn gen_receipt(out: &Path) {
    let proof = fs::read(format!("{FIXTURES}/proof_inner.bin")).expect("proof fixture");
    let journal = fs::read(format!("{FIXTURES}/journal.bin")).expect("journal fixture");
    let image_id_v = fs::read(format!("{FIXTURES}/image_id.bin")).expect("image id fixture");
    let image_id: [u8; 32] = image_id_v.as_slice().try_into().expect("32-byte image id");

    // The accept vector MUST verify through the oracle, or the fixture is bad.
    assert!(
        oracle_verify(&proof, &journal, &image_id),
        "fixture receipt failed oracle verification"
    );

    let mut mutations = Vec::new();
    let mut push_mutation = |description: String,
                             offset: Option<usize>,
                             xor: Option<u8>,
                             truncate_to: Option<usize>,
                             mutate_image_id: bool| {
        let mut p = proof.clone();
        let mut id = image_id;
        if let (Some(o), Some(x)) = (offset, xor) {
            p[o] ^= x;
        }
        if let Some(t) = truncate_to {
            p.truncate(t);
        }
        if mutate_image_id {
            id[0] ^= 0x01;
        }
        let got = oracle_verify(&p, &journal, &id);
        assert!(!got, "mutation unexpectedly verified: {description}");
        mutations.push(Mutation {
            description,
            offset,
            xor,
            truncate_to,
            mutate_image_id,
            expected: false,
            oracle_confirmed: true,
        });
    };

    push_mutation("flip low bit of first proof byte".into(), Some(0), Some(0x01), None, false);
    push_mutation(
        format!("flip a byte mid-proof (offset {})", proof.len() / 2),
        Some(proof.len() / 2),
        Some(0x80),
        None,
        false,
    );
    push_mutation(
        format!("flip last proof byte (offset {})", proof.len() - 1),
        Some(proof.len() - 1),
        Some(0xFF),
        None,
        false,
    );
    push_mutation("truncate proof to 1024 bytes".into(), None, None, Some(1024), false);
    push_mutation("truncate proof to 0 bytes".into(), None, None, Some(0), false);
    push_mutation("wrong image id (flip low bit of byte 0)".into(), None, None, None, true);

    let kat = ReceiptKat {
        description: "End-to-end RISC0 succinct receipt accept/reject vectors. The accept \
                      receipt is a REAL proof (sha256 guest) generated by the RISC0 prover and \
                      carried in a transaction on a live Ergo Rust-node devnet.",
        oracle: "risc0-verifier v0.11.0 (zkVerify), verify(&v3_0(), ...)",
        verifier_context: "RISC0 circuit v3.0, succinct (stock profile: BabyBear/Ext4/Poseidon2)",
        proof_file: "proof_inner.bin",
        proof_len: proof.len(),
        proof_blake2b256: hex::encode(Blake2b256::digest(&proof)),
        image_id_hex: hex::encode(image_id),
        journal_hex: hex::encode(&journal),
        expected: true,
        mutations,
    };
    write_json(out, "receipt_kat.json", &kat);

    // The proof itself ships next to the vectors so the Scala tests can load it.
    fs::copy(
        format!("{FIXTURES}/proof_inner.bin"),
        out.join("proof_inner.bin"),
    )
    .expect("copy proof fixture");
}

#[derive(Serialize)]
struct ProfileDescriptor {
    profile_id: u32,
    name: &'static str,
    zkvm: &'static str,
    circuit_version: &'static str,
    base_field: &'static str,
    extension_field: &'static str,
    merkle_hash: &'static str,
    transcript_hash: &'static str,
    proof_format: &'static str,
    public_input_format: &'static str,
    security_note: &'static str,
}

#[derive(Serialize)]
struct ProfileKat {
    description: &'static str,
    canonicalization: &'static str,
    descriptor: ProfileDescriptor,
    canonical_json: String,
    profile_hash_blake2b256: String,
}

fn gen_profile(out: &Path) {
    let descriptor = ProfileDescriptor {
        profile_id: 1,
        name: "risc0-succinct-v3.0-stock",
        zkvm: "RISC Zero (RISC-V CPU transition constraints)",
        circuit_version: "3.0",
        base_field: "BabyBear p=2013265921 (15*2^27+1)",
        extension_field: "degree-4, x^4 + 11, coeffs [c0,c1,c2,c3]",
        merkle_hash: "Poseidon2-BabyBear t=24 rate=16 out=8",
        transcript_hash: "SHA-256 (RISC0 succinct transcript)",
        proof_format: "bincode(InnerReceipt), succinct kind",
        public_input_format: "journal bytes; imageId = 32-byte Vk",
        security_note: "conjectured ~100-bit PQ soundness (stock parameters); \
                        registered as-is, hardened profiles may supersede",
    };
    // PROPOSAL (the EIP does not yet define canonicalProfileDescriptor
    // encoding): canonical form = minified JSON with keys in the exact order
    // above; profileHash = Blake2b-256 over its UTF-8 bytes.
    let canonical_json = serde_json::to_string(&descriptor).expect("canonical json");
    let profile_hash = hex::encode(Blake2b256::digest(canonical_json.as_bytes()));
    let kat = ProfileKat {
        description: "Stock RISC0 succinct verifier profile descriptor (proposed vmType 0x01) \
                      + canonicalization proposal and profileHash.",
        canonicalization: "minified JSON, fixed key order as listed; Blake2b-256 over UTF-8",
        descriptor,
        canonical_json: canonical_json.clone(),
        profile_hash_blake2b256: profile_hash,
    };
    write_json(out, "profile_descriptor.json", &kat);
}

/// TSV mirrors of the primitive KATs so the Scala parity tests need no JSON
/// dependency. One case per line; `-` marks an undefined inverse.
fn write_tsvs(out: &Path) {
    // Regenerate the same deterministic inputs the JSON emitters used.
    {
        let mut lcg = Lcg(0xE1900045_00000001);
        let mut inputs: Vec<(u32, u32)> = vec![
            (0, 0),
            (0, 1),
            (1, 1),
            (P - 1, 1),
            (P - 1, P - 1),
            (1 << 27, 15),
            (2, P - 2),
        ];
        for _ in 0..57 {
            inputs.push((lcg.next_fe(), lcg.next_fe()));
        }
        let mut s = String::from("# a\tb\tadd\tsub\tmul\tneg_a\tinv_a\tpow_a_b\n");
        for (a, b) in inputs {
            let (ea, eb) = (BabyBearElem::new(a), BabyBearElem::new(b));
            let inv = if a % P == 0 { "-".to_string() } else { u32_of(ea.inv()).to_string() };
            s.push_str(&format!(
                "{a}\t{b}\t{}\t{}\t{}\t{}\t{inv}\t{}\n",
                u32_of(ea + eb),
                u32_of(ea - eb),
                u32_of(ea * eb),
                u32_of(-ea),
                u32_of(ea.pow(b as usize)),
            ));
        }
        fs::write(out.join("babybear_ops.tsv"), s).expect("write tsv");
    }
    {
        let mut lcg = Lcg(0xE1900045_00000002);
        let mut inputs: Vec<([u32; 4], [u32; 4])> = vec![
            ([0; 4], [0; 4]),
            ([1, 0, 0, 0], [1, 0, 0, 0]),
            ([0, 1, 0, 0], [0, 1, 0, 0]),
            ([0, 0, 1, 0], [0, 0, 1, 0]),
            ([P - 1, P - 1, P - 1, P - 1], [1, 2, 3, 4]),
        ];
        for _ in 0..43 {
            let a = [lcg.next_fe(), lcg.next_fe(), lcg.next_fe(), lcg.next_fe()];
            let b = [lcg.next_fe(), lcg.next_fe(), lcg.next_fe(), lcg.next_fe()];
            inputs.push((a, b));
        }
        let j = |c: [u32; 4]| c.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(",");
        let mut s = String::from("# a\tb\tadd\tmul\tinv_a  (coeffs c0,c1,c2,c3)\n");
        for (a, b) in inputs {
            let (ea, eb) = (ext_of(a), ext_of(b));
            let zero = a.iter().all(|&c| c % P == 0);
            let inv = if zero { "-".to_string() } else { j(arr_of(ea.inv())) };
            s.push_str(&format!(
                "{}\t{}\t{}\t{}\t{inv}\n",
                j(a),
                j(b),
                j(arr_of(ea + eb)),
                j(arr_of(ea * eb)),
            ));
        }
        fs::write(out.join("ext4_ops.tsv"), s).expect("write tsv");
    }
    {
        let mut lcg = Lcg(0xE1900045_00000003);
        let mut inputs: Vec<Vec<u32>> = vec![
            vec![0; CELLS],
            {
                let mut v = vec![0; CELLS];
                v[0] = 1;
                v
            },
            (0..CELLS as u32).collect(),
        ];
        for _ in 0..13 {
            inputs.push((0..CELLS).map(|_| lcg.next_fe()).collect());
        }
        let j = |c: &[u32]| c.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(",");
        let mut s = String::from("# input(24)\toutput(24)\n");
        for input in inputs {
            let mut cells: [BabyBearElem; CELLS] =
                core::array::from_fn(|i| BabyBearElem::new(input[i]));
            poseidon2_mix(&mut cells);
            let outv: Vec<u32> = cells.iter().map(|&e| u32_of(e)).collect();
            s.push_str(&format!("{}\t{}\n", j(&input), j(&outv)));
        }
        fs::write(out.join("poseidon2_perm.tsv"), s).expect("write tsv");
    }
    println!("wrote TSV mirrors");
}

fn write_json<T: Serialize>(out: &Path, name: &str, value: &T) {
    let path = out.join(name);
    let json = serde_json::to_string_pretty(value).expect("serialize");
    fs::write(&path, json).expect("write kat");
    println!("wrote {}", path.display());
}

fn main() {
    let out = Path::new(OUT_DIR);
    fs::create_dir_all(out).expect("mkdir out");
    gen_babybear(out);
    gen_ext4(out);
    gen_poseidon2(out);
    gen_receipt(out);
    gen_profile(out);
    write_tsvs(out);
    println!("all KATs generated + oracle-confirmed");
}
