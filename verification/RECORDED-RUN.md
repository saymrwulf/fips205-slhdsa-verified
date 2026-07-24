# Recorded clean run — check.sh + independent cone dump

External review round 2 asked for a recorded clean run at the current pin
by a party with the toolchain, so a reviewer who cannot run Lean has current
evidence. Captured 2026-07-24. Pins are in [PROVENANCE.json](PROVENANCE.json).
The cone dump below is an *independent* `collectAxioms` read (not the asserted
table in Proofs/Audit.lean); it matches each certificate's expected boundary.

```
RECORDED CLEAN RUN — fips205-slhdsa-verified
date(UTC): 20260724T171145Z
host lean: Lean (version 4.30.0-rc2, x86_64-unknown-linux-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
source pin: 797b4ef26338e27363683656f93cb065a77daa0e
==============================================
fips205-slhdsa-verified — check
===============================
=== Phase 1: compile the extracted model ===
  · gen/SlhVerify/TypesExternal
  · gen/SlhVerify/Types
  · gen/SlhVerify/FunsExternal
  · gen/SlhVerify/Funs
=== Phase 2: compile the proofs ===
  · ChainSpec
  · WotsSpec
  · XmssSpec
  · HtSpec
  · ForsInnerSpec
  · ForsOuterSpec
  · InputPrepSpec
  · ApexSpec
=== Phase 3: axiom audit (exact cone per certificate — inside Lean) ===
  ✓ exact-cone audit PASSED: each of the 11 certificate cones == its expected boundary set

ALL GREEN — model compiles, proofs compile, and every certificate cone
equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles.
Certificates proven: fips205.chain_free_loop_eq fips205.wots_loop1_eq fips205.xmss_loop_eq fips205.ht_loop_eq fips205.fors_inner_loop_eq fips205.fors_outer_loop_eq fips205.to_int_loop_eq fips205.to_byte_loop_eq fips205.wots_csum_loop_eq fips205.base2b_outer_loop_eq fips205.slh_verify_128s_accepts_iff

=== INDEPENDENT cone dump (collectAxioms, 20260724T171253Z) ===
fips205.chain_free_loop_eq :: propext, Classical.choice, Quot.sound, verify_mono.oracle.f
fips205.wots_loop1_eq :: propext, Classical.choice, Quot.sound, verify_mono.oracle.f
fips205.xmss_loop_eq :: propext, Classical.choice, Quot.sound, verify_mono.oracle.h
fips205.ht_loop_eq :: propext, Classical.choice, Quot.sound, verify_mono.oracle.f, verify_mono.oracle.h, verify_mono.oracle.t_l
fips205.fors_inner_loop_eq :: propext, Classical.choice, Quot.sound, verify_mono.oracle.h
fips205.fors_outer_loop_eq :: propext, Classical.choice, Quot.sound, verify_mono.oracle.f, verify_mono.oracle.h
fips205.to_int_loop_eq :: propext, Classical.choice, Quot.sound
fips205.to_byte_loop_eq :: propext, Classical.choice, Quot.sound
fips205.wots_csum_loop_eq :: propext, Classical.choice, Quot.sound
fips205.base2b_outer_loop_eq :: propext, Classical.choice, Quot.sound
fips205.slh_verify_128s_accepts_iff :: propext, Classical.choice, Quot.sound, verify_mono.oracle.f, verify_mono.oracle.h, verify_mono.oracle.h_msg, verify_mono.oracle.t_l, verify_mono.oracle.t_len
```

## Locked cargo run under the pinned nightly (round-3 reviewer recommendation)

The differential test `mono_matches_deployed_verify` is the sole
verify_mono→deployed bridge; recorded here under `--locked` on the
toolchain pinned by `rust-toolchain.toml` (nightly-2026-06-01, the
transpiler's own channel). Note: the upstream integration-test files
hardcode all twelve parameter sets, so they only build with default
features — the single-feature run therefore uses `--lib` (which contains
the differential test), and the full suite runs with default features.
This explains the round-1 GPT observation that single-feature
`cargo test` fails to compile: an upstream test-layout property, not a
defect of the snapshot.

```
=== LOCKED CARGO RUN — fips205-source @ 797b4ef26338e27363683656f93cb065a77daa0e ===
date(UTC): 20260724T192246Z
toolchain: nightly-2026-06-01-x86_64-unknown-linux-gnu (overridden by '/home/oho/GitClone/FormalVerification/sources/fips205-source/rust-toolchain.toml')

--- (1) differential test (verify_mono vs deployed generic verifier), lib tests, SHA2-128s feature ---
running 2 tests
test verify_mono::tests::mono_matches_deployed_verify ... ok
test slh_dsa_sha2_128s::tests::simple_round_trips ... ok
test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 10.82s

--- (2) full upstream suite, default features (all parameter sets), --locked ---
test src/traits.rs - traits::Signer::try_sign_with_rng (line 284) ... ok
test src/traits.rs - traits::Verifier::hash_verify (line 455) ... ok
test src/traits.rs - traits::Verifier::verify (line 415) ... ok

test result: ok. 37 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 28.20s


--- (2b) full-suite summary lines (all test binaries + doctests) ---
running 13 tests
test result: ok. 13 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 39.25s
running 3 tests
test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 143.21s
running 1 test
test result: ok. 0 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.00s
running 12 tests
test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 6.39s
running 37 tests
test result: ok. 37 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 27.89s
```
