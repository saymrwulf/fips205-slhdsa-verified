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
