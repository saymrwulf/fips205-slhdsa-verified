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

## INDEPENDENT RUN — executed by the operator (the round-3 blocker)

Round 3's single remaining blocker was a recorded toolchain session
executed by a party other than the author agent. The operator ran the
block below personally on 2026-07-27 (a first attempt on 2026-07-24
failed with a memory-clamped lean abort on a loaded desktop — an
environment condition, diagnosed from ~/.lean-guard.log and addressed
by the lean-guard stderr-diagnostics commit 62d7ed1; the proofs were
never implicated). Result: check.sh ALL GREEN at 62d7ed1 (11
certificates, exact-cone audit passed) and extract.sh regeneration
byte-identical against fips205-source @ 797b4ef — both sha256 values
match PROVENANCE.json. Transcript verbatim from the operator's shell:

```
INDEPENDENT RUN — executed by the operator, 20260727T125816Z
proof repo @ 62d7ed12091bb9bd267724b698f663c00ddc3210
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
--- extract.sh byte-identity ---
[0/2] provenance OK: fips205-source @ 797b4ef26338 (clean)
[1/2] charon: Rust -> LLBC (monomorphic SHA2-128s verify cone;
        crate::verify_mono::oracle is the opaque SHA-2 boundary)
   Compiling fips205 v0.4.1 (/home/oho/GitClone/FormalVerification/sources/fips205-source)
    Finished `dev` profile [optimized + debuginfo] target(s) in 0.54s
[2/2] aeneas: LLBC -> Lean (split files, SlhVerify.* modules;
        hand-maintained TypesExternal.lean / FunsExternal.lean are
        NOT overwritten once they exist)
[[92mInfo[39m ] Imported: SlhVerify.llbc
[?25lApplied prepasses:  [------------------------------------------------]   0/142 ⠋Applied prepasses:  [------------------------------------------------]   1/142 ⠋Applied prepasses:  [###---------------------------------------------]  11/142 ⠋Applied prepasses:  [#################-------------------------------]  52/142 ⠙Applied prepasses:  [########################################--------] 120/142 ⠙Applied prepasses:  [################################################] 142/142 ✔️
[?25h[?25lTranslated globals:  [-------------------------------------------------]  0/10 ⠋Translated globals:  [#################################################] 10/10 ✔️
[?25h[?25lTranslated opaque functions:  [----------------------------------------]  0/76 ⠋Translated opaque functions:  [########################################] 76/76 ✔️
[?25h[?25lTranslated transparent functions:  [-----------------------------------]  0/42 ⠋Translated transparent functions:  [-----------------------------------]  1/42 ⠙Translated transparent functions:  [#######----------------------------]  9/42 ⠹Translated transparent functions:  [########---------------------------] 10/42 ⠹Translated transparent functions:  [##########-------------------------] 12/42 ⠹Translated transparent functions:  [##########-------------------------] 13/42 ⠹Translated transparent functions:  [###########------------------------] 14/42 ⠸Translated transparent functions:  [############-----------------------] 15/42 ⠸Translated transparent functions:  [##############---------------------] 17/42 ⠸Translated transparent functions:  [###############--------------------] 19/42 ⠸Translated transparent functions:  [################-------------------] 20/42 ⠼Translated transparent functions:  [##################-----------------] 22/42 ⠼Translated transparent functions:  [####################---------------] 24/42 ⠼Translated transparent functions:  [#####################--------------] 26/42 ⠴Translated transparent functions:  [######################-------------] 27/42 ⠴Translated transparent functions:  [#######################------------] 28/42 ⠦Translated transparent functions:  [########################-----------] 29/42 ⠦Translated transparent functions:  [#########################----------] 30/42 ⠦Translated transparent functions:  [#########################----------] 31/42 ⠧Translated transparent functions:  [###########################--------] 33/42 ⠇Translated transparent functions:  [#############################------] 35/42 ⠏Translated transparent functions:  [##############################-----] 36/42 ⠏Translated transparent functions:  [##############################-----] 37/42 ⠋Translated transparent functions:  [###############################----] 38/42 ⠙Translated transparent functions:  [################################---] 39/42 ⠹Translated transparent functions:  [#################################--] 40/42 ⠸Translated transparent functions:  [##################################-] 41/42 ⠸Translated transparent functions:  [###################################] 42/42 ⠼Translated transparent functions:  [###################################] 42/42 ✔️
[?25h[?25lTranslated trait declarations:  [--------------------------------------]  0/33 ⠋Translated trait declarations:  [##############------------------------] 13/33 ✔️
[?25h[?25lTranslated trait impls:  [---------------------------------------------]  0/50 ⠋Translated trait impls:  [######################-----------------------] 25/50 ✔️
[?25h[?25lPost-processed translated opaque functions:  [-------------------------]  0/76 ⠋Post-processed translated opaque functions:  [-------------------------]  1/76 ⠙Post-processed translated opaque functions:  [#########################] 76/76 ✔️
[?25h[?25lPost-processed translated transparent functions:  [--------------------]  0/42 ⠋Post-processed translated transparent functions:  [--------------------]  1/42 ⠙Post-processed translated transparent functions:  [###-----------------]  7/42 ⠙Post-processed translated transparent functions:  [####----------------]  9/42 ⠙Post-processed translated transparent functions:  [####----------------] 10/42 ⠹Post-processed translated transparent functions:  [#####---------------] 11/42 ⠹Post-processed translated transparent functions:  [#####---------------] 12/42 ⠸Post-processed translated transparent functions:  [######--------------] 13/42 ⠸Post-processed translated transparent functions:  [######--------------] 14/42 ⠸Post-processed translated transparent functions:  [#######-------------] 15/42 ⠼Post-processed translated transparent functions:  [#######-------------] 16/42 ⠼Post-processed translated transparent functions:  [########------------] 17/42 ⠼Post-processed translated transparent functions:  [#########-----------] 19/42 ⠴Post-processed translated transparent functions:  [#########-----------] 20/42 ⠴Post-processed translated transparent functions:  [##########----------] 21/42 ⠴Post-processed translated transparent functions:  [##########----------] 22/42 ⠦Post-processed translated transparent functions:  [##########----------] 23/42 ⠦Post-processed translated transparent functions:  [###########---------] 25/42 ⠦Post-processed translated transparent functions:  [############--------] 26/42 ⠧Post-processed translated transparent functions:  [############--------] 27/42 ⠧Post-processed translated transparent functions:  [#############-------] 28/42 ⠧Post-processed translated transparent functions:  [##############------] 30/42 ⠇Post-processed translated transparent functions:  [###############-----] 32/42 ⠇Post-processed translated transparent functions:  [###############-----] 33/42 ⠏Post-processed translated transparent functions:  [################----] 34/42 ⠏Post-processed translated transparent functions:  [#################---] 37/42 ⠋Post-processed translated transparent functions:  [##################--] 38/42 ⠋Post-processed translated transparent functions:  [##################--] 39/42 ⠙Post-processed translated transparent functions:  [###################-] 40/42 ⠹Post-processed translated transparent functions:  [###################-] 41/42 ⠸Post-processed translated transparent functions:  [####################] 42/42 ⠼Post-processed translated transparent functions:  [####################] 42/42 ✔️
[?25h[[92mInfo[39m ] Generated: gen/SlhVerify/Types.lean
[[92mInfo[39m ] Generated: gen/SlhVerify/FunsExternal_Template.lean
[[92mInfo[39m ] Generated: gen/SlhVerify/Funs.lean
[[92mInfo[39m ] Total execution time: 8.980301 seconds
Done. Now run ./check.sh (Phase 1: the regenerated model must type-check).
db720b4a30f512e6048212a472e6853b24931a8121cb94c4cf7e6489754d6384  gen/SlhVerify/Types.lean
7b7de55fd0206142f2678a079a6ed4462292356bc7de08ecd55cac0c76a1da9f  gen/SlhVerify/Funs.lean
```

## Round-4 hardening (third reviewer, 2026-07-27)

The third reviewer demonstrated three fail-opens OUTSIDE the cone check
(F1 unbound cert set / un-manifested theorem; F2 statements unbound; F3
model bytes unbound). All fixed. check.sh green with the hardened gate,
and the adversarial self-test then rejected eight attacks including the two
the reviewer used to make the button green over a repo proving False.

**CORRECTION (2026-07-27, found by an independent audit of this file).** The
three lines that stood here inside the fence below were **not** console output:
they were a hand-written summary of the run, fenced as if captured. `check.sh`
never printed them. The author wrote them; that is fabricated evidence in the
one document whose stated purpose is to carry machine evidence to reviewers who
cannot run the toolchain, and it is exactly the failure this project exists to
prevent. They have been removed. The selftest transcript that follows in the
same fence **is** verbatim.

Two further corrections to this file's framing:
* the "INDEPENDENT RUN — executed by the operator" block above is at proof repo
  `62d7ed1`, which **predates the round-4 gate** (its transcript has no Phase 0).
  It is genuine and operator-executed, but it is *not* a run of the gate that
  now ships;
* consequently, at the time of writing there was **no recorded run of the
  current gate by an independent party**. Any transcript below this line that is
  not explicitly attributed to a named party was produced by the author agent.

Rule adopted going forward: no text is placed inside a fence in this file unless
it was captured with `tee`/`cat` from the real command, and every evidence block
states its date, its pin, and who ran it.

```

check-selftest: attacking the gates
====================================
✓ attack 1 rejected (dead-file gate)
✓ attack 2 rejected (extra-axiom detection — evil_ax named)
✓ attack 3 rejected (missing-oracle detection — exact cone, not subset)
✓ attack 4 rejected (existence check — vanished cert cannot pass as 0-axiom)
✓ attack 5 rejected (module enumeration — an un-manifested False theorem cannot pass)
✓ attack 6 rejected (statement fingerprint — a gutted statement of the same cone cannot pass)
✓ attack 7 rejected (Phase 0 model-byte integrity — a hand-edited model cannot compile)
✓ attack 8 rejected (manifest fingerprint — a silently-dropped cert cannot pass)

SELFTEST GREEN: the gate rejects dead files, extra axioms, dropped oracles,
vanished certs, un-manifested False theorems, gutted statements, hand-edited
models, and deleted manifest rows.
```

## Round-5 hardening — author-agent run, 20260727T205716Z, proof repo @ (this commit)

Captured with `tee` from the real commands; nothing below was typed by hand.
Not independently executed — an independent run of this gate is still outstanding.

### check.sh
```
fips205-slhdsa-verified — check
===============================
=== Phase 0: build hygiene + model/harness integrity ===
  ✓ gen/SlhVerify/Funs.lean
  ✓ gen/SlhVerify/FunsExternal.lean
  ✓ gen/SlhVerify/Types.lean
  ✓ gen/SlhVerify/TypesExternal.lean
  ✓ lean-guard
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
=== Phase 3: in-Lean audit (cones + statement fingerprints + enumeration) ===
  ✓ exact-cone audit PASSED
  ✓ audit-manifest digest matches (sha256 d83e297a49094c97…)

ALL GREEN — model compiles, proofs compile, and every certificate cone
equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles.
Certificates proven: fips205.chain_free_loop_eq fips205.wots_loop1_eq fips205.xmss_loop_eq fips205.ht_loop_eq fips205.fors_inner_loop_eq fips205.fors_outer_loop_eq fips205.to_int_loop_eq fips205.to_byte_loop_eq fips205.wots_csum_loop_eq fips205.base2b_outer_loop_eq fips205.slh_verify_128s_accepts_iff
```

### check-selftest.sh (14 attacks + digest-coverage check)
```
check-selftest: attacking the gates
====================================
✓ attack 1 rejected (dead-file gate)
✓ attack 2 rejected (extra-axiom detection — evil_ax named)
✓ attack 3 rejected (missing-oracle detection — exact cone, not subset)
✓ attack 4 rejected (existence check — a vanished cert cannot pass as 0-axiom)
✓ attack 5 rejected (enumeration — an un-manifested False theorem cannot pass)
✓ attack 6 rejected (statement check — a gutted statement of the same cone cannot pass)
✓ attack 7 rejected (Phase 0 model-byte integrity)
✓ attack 8 rejected (audit-manifest digest — a silently-dropped cert cannot pass)
✓ attack 9 rejected (digest covers allowedBoundary — the policy cannot be widened silently)
✓ attack 10 rejected (a specification fold cannot be silently redefined to the loop)
✓ attack 11 rejected (enumeration covers every declaration kind, not just theorems)
✓ attack 12 rejected (the auditor audits itself — no exemption)
✓ attack 13 rejected (Phase 0 pins lean-guard — the harness is in the TCB and bound)
✓ attack 14 rejected (no .lean may sit outside gen/ and Proofs/)
✓ check 15 passed (the hashed block carries all 12 reference-fold bodies,
./check-selftest.sh: line 270: _f: command not found
  including the recursive  companions and their extracted-primitive calls)

SELFTEST GREEN: 14 attacks rejected + digest-coverage check — dead files, extra axioms, dropped
oracles, vanished certs, un-manifested False theorems AND defs, gutted
statements, hand-edited models, dropped manifest rows, widened policy,
specification folds redefined to the loop, a False-proof in the auditor,
a stubbed harness, and stray modules.
```

Note: the `_f: command not found` line in the selftest transcript above is a
cosmetic shell-quoting bug in the script's own success message (backticks inside
a double-quoted echo), fixed in this same commit. It did not affect any gate.

## Round-6 hardening — author-agent run, 20260728T072212Z, proof repo @ (this commit)

Captured with `tee` from the real commands. Not independently executed.
PIN ROTATIONS IN THIS COMMIT (stated explicitly — round-6 NEW-11):
  · harness_integrity_sha256 GAINS Proofs/Audit.lean (6108b97d…) — new pin, NEW-7.
  · no model pin rotated; gen/ bytes unchanged.

### check.sh
```
fips205-slhdsa-verified — check
===============================
=== Phase 0: build hygiene + model/harness integrity ===
  ✓ Proofs/Audit.lean
  ✓ gen/SlhVerify/Funs.lean
  ✓ gen/SlhVerify/FunsExternal.lean
  ✓ gen/SlhVerify/Types.lean
  ✓ gen/SlhVerify/TypesExternal.lean
  ✓ lean-guard
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
=== Phase 3: in-Lean audit (cones + statement fingerprints + enumeration) ===
  ✓ exact-cone audit PASSED
  ✓ audit-manifest digest matches (sha256 d83e297a49094c97…)

ALL GREEN — model compiles, proofs compile, and every certificate cone
equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles.
Certificates proven: fips205.chain_free_loop_eq fips205.wots_loop1_eq fips205.xmss_loop_eq fips205.ht_loop_eq fips205.fors_inner_loop_eq fips205.fors_outer_loop_eq fips205.to_int_loop_eq fips205.to_byte_loop_eq fips205.wots_csum_loop_eq fips205.base2b_outer_loop_eq fips205.slh_verify_128s_accepts_iff
```

### check-selftest.sh (16 attacks + digest-coverage check)
```
check-selftest: attacking the gates
====================================
✓ attack 1 rejected (dead-file gate)
✓ attack 2 rejected (extra-axiom detection — evil_ax named)
✓ attack 3 rejected (missing-oracle detection — exact cone, not subset)
✓ attack 4 rejected (existence check — a vanished cert cannot pass as 0-axiom)
✓ attack 5 rejected (enumeration — an un-manifested False theorem cannot pass)
✓ attack 6 rejected (statement check — a gutted statement of the same cone cannot pass)
✓ attack 7 rejected (Phase 0 model-byte integrity)
✓ attack 8 rejected (audit-manifest digest — a silently-dropped cert cannot pass)
✓ attack 9 rejected (digest covers allowedBoundary — the policy cannot be widened silently)
✓ attack 10 rejected (a specification fold cannot be silently redefined to the loop)
✓ attack 11 rejected (enumeration covers every declaration kind, not just theorems)
✓ attack 12 rejected (the auditor audits itself — no exemption)
✓ attack 13 rejected (Phase 0 pins lean-guard — the harness is in the TCB and bound)
✓ attack 14 rejected (no .lean may sit outside gen/ and Proofs/)
✓ attack 16 rejected (Phase 0 purges every .olean under verification/, so an
  orphan compiled module with no source cannot satisfy an import)
✓ attack 17 rejected (Phase 0 pins Audit.lean — its LOGIC cannot be silently switched off)
✓ check 15 passed (the hashed block carries all 12 reference-fold bodies,
  including the recursive _f companions and their extracted-primitive calls)

SELFTEST GREEN: 16 attacks rejected + digest-coverage check — dead files, extra axioms, dropped
oracles, vanished certs, un-manifested False theorems AND defs, gutted
statements, hand-edited models, dropped manifest rows, widened policy,
specification folds redefined to the loop, a False-proof in the auditor,
a stubbed harness, and stray modules.
```
