# stark-kat — KAT generator for the EIP-0045 verifyStark verifier

Generates the Known Answer Test vectors under
`core/jvm/src/test/resources/stark-kats/`, consumed by
`sigma.stark.StarkKatSpec`.

**Oracle-parity rule:** every expected value is produced by an EXTERNAL
oracle — never by the Scala implementation under test:

| vectors | oracle |
|---|---|
| `babybear_ops.*`, `ext4_ops.*` | risc0-core 1.2.6 (`field::baby_bear`) |
| `poseidon2_perm.*` | risc0-zkp 1.2.6 (`core::hash::poseidon2::poseidon2_mix`) |
| `receipt_kat.json` + `proof_inner.bin` | risc0-verifier v0.11.0 (zkVerify, Apache-2.0), `verify(&v3_0(), …)` — the same crate/tag the Rust Ergo node's verifyStark implementation links |
| `profile_descriptor.json` | proposal artifact (canonicalization + Blake2b-256 profileHash for a stock RISC0 succinct vmType) |
| `circuit_taps.tsv`, `circuit_polyext_ops.tsv`, `circuit_params.tsv` | risc0-circuit-recursion 4.0.4 (`CIRCUIT.get_taps()`, vendored `poly_ext.rs` DEF asserted equivalent to the crate's private table, `control_id`) + risc0-zkp 3.0.4 consts — `cargo run --release --bin circuit_extract` |
| `transcript_capture.tsv` | risc0-zkp 3.0.4 `verify::verify` over the REAL receipt with delegating recording `HashFn`/`Rng` wrappers (untouched verifier accepts through the identical path, asserted) — `cargo run --release --bin transcript_capture` |

Schemas for the `circuit_*`/`transcript_*` files:
`core/jvm/src/test/resources/stark-kats/circuit_tables.md`. The risc0 3.x /
recursion 4.x deps are pinned to exactly what the Rust Ergo node's
`Cargo.lock` resolves for risc0-verifier v0.11.0 (zkp 3.0.4 / recursion
4.0.4) — the devnet verifies with that resolution.

The accept receipt in `fixtures/` is a REAL proof (sha256 guest) generated
by the RISC0 prover and carried in a transaction on a live Ergo Rust-node
devnet — an un-forgeable external artifact. Every reject mutation's verdict
is confirmed by actually running the oracle verifier on the mutated input
at generation time (one mutation makes the oracle verifier *panic*
internally, caught and recorded as reject — a JVM verifier must likewise
reject, never throw, on malformed receipts).

Regenerate (deterministic — no RNG; byte-identical on re-run):

```bash
cd stark-kat && cargo run --release
```

These vectors target the **stock RISC0 succinct profile**
(BabyBear/Ext4/Poseidon2, circuit v3.0) — the profile provers actually
emit today. They complement sigmastate PR #1116 (draft verifier for the
PQ-hardened Poseidon1/Ext16 profile), for which no prover — and therefore
no real-proof KAT — currently exists.
