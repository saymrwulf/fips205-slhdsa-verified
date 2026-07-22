# fips205-slhdsa-verified

Machine-checked verification campaign for the **SLH-DSA (FIPS 205) verify
path**, extracted from a pure-Rust implementation into Lean 4 via
Charon/Aeneas — the same pipeline, discipline, and honesty rules as the
four ed25519 campaigns (`dalek/anza/risc0/betrusted-ed25519-verified`).

## STATUS: MODEL EXTRACTED & TYPE-CHECKS — NOTHING PROVEN YET

There are still **zero certificates** in this repository. What phase 1
established (2026-07-22):

- the Aeneas-compat patch landed in the snapshot (an additive monomorphic
  SHA2-128s verify module reached through a named hash-oracle boundary);
- **charon and aeneas both exit 0** on the full verify cone — the gate-0
  fn-pointer blocker is gone;
- the extracted Lean model (`verification/gen/SlhVerify`, 62 defs, apex
  `verify_mono.slh_verify_128s`) **type-checks under lean-guard**
  (`verification/check.sh` Phase 1 is green);
- fidelity of the monomorphic path is pinned by a differential test in the
  snapshot that agrees with the deployed verifier on valid / corrupted /
  wrong-message signatures.

A green Phase-1 compile proves the model is **well-formed**, NOT that the
verifier is correct. No operation theorem has been stated or proven. Every
claim under "What will be claimed" remains a *plan* (H5: an honest gap
outranks a hollow certificate).

## Subject

- Upstream: `integritychain/fips205` — pure-Rust FIPS 205 (final standard,
  2024-08-13), zero `unsafe`, `no_std`, const-generic parameterization,
  modules mirroring the FIPS 205 algorithm structure.
- Pinned at upstream commit `30bac08580aa61f653e5436d1bbacb5ffac446c4`
  (2025-09-01), snapshotted with full history at
  `saymrwulf/fips205-source` (snapshot head `5dca0db`, whose single
  deviation from verbatim is the removal of upstream CI workflows,
  documented in that commit). Aeneas-compat patches will land in the
  snapshot repo as transparent, individually-justified commits — never
  upstream. **No affiliation with, and no changes proposed to, the
  upstream project.**
- Parameter set: **SLH-DSA-SHA2-128s** first (the small-signature profile
  deployed in the firmware/code-signing lane). The architecture
  generalizes; each further parameter set is a separate claim (rigor
  invariant R2).

## Scope

**Verify path only.** The extraction cone, mirroring FIPS 205's own
algorithm tree:

```
slh_verify -> slh_verify_internal
  -> fors_pk_from_sig
  -> ht_verify -> xmss_pk_from_sig -> wots_pk_from_sig -> chain
```

Key generation and signing are out of scope (trusted base), exactly as
ed25519 signing was. The five verify-path hash oracles (`h_msg, f, h,
t_l, t_len` — SHA-2 instantiations; `prf`/`prf_msg` are sign-side only
and never enter the cone) are opaque external models with written
justifications, kept outside every certificate's dependency cone
(honesty invariant H4); their semantics are the standing SHA-2 oracle
boundary documented in [TRUSTED-BASE.md](TRUSTED-BASE.md).

## Gate-0 record (2026-07-22)

Per TARGETS.md ("re-verify before use"), the subject was probed before
this repository was created:

- **Charon**: clean (`charon cargo --preset=aeneas`, roots at the verify
  cone, `sha2/sha3/zeroize/rand_core` opaque, features
  `slh_dsa_sha2_128s`) — LLBC produced, exit 0.
- **Aeneas**: translated the entire const-generic verify cone to Lean
  definitions (`wots.chain` … `slh.slh_verify_internal` all generated),
  with exactly **one obstruction class** (3 unique errors): the
  `crate::hashers::Hashers` struct of plain **function pointers** cannot
  be translated.
- **Phase 1 — DONE (2026-07-22)**: the Aeneas-compat patch landed in
  `fips205-source` (snapshot `2d89ee3`): an additive monomorphic SHA2-128s
  verify module (`src/verify_mono.rs`) whose hash suite is reached through
  named free functions in `verify_mono::oracle` (marked opaque at the
  Charon boundary) — the `sha512_*`-shim pattern. Two further compat
  refinements: the message-digest input M' passes as a single `&[u8]`
  (nested `&[&[u8]]` is untranslatable), and one `let-else` became the
  `is_err`/`unwrap` idiom. `verification/extract.sh` now re-derives the
  model from the mono root; charon + aeneas both exit 0, and
  `verification/check.sh` compiles the result. The generic paths and all
  twelve parameter sets are untouched (the only change to existing code is
  two lines wiring the module).

## What will be claimed (when the button is green, not before)

One theorem per layer, each a statement about the **extracted** functions
(H3), compiled by `verification/check.sh` with a per-certificate
`#print axioms` audit (H1): chain semantics, WOTS+ pk recomputation,
XMSS path recomputation, hypertree acceptance, FORS pk recomputation,
and the apex — `slh_verify_internal` accepts iff the recomputed
hypertree root equals the pinned public-key root.

**The allowed axiom set, stated precisely:** unlike the ed25519 field and
scalar layers (whose cones are exactly `[propext, Classical.choice,
Quot.sound]`), the hash oracles permeate *every* SLH-DSA layer — `chain`
already calls `F`. So each certificate's cone may contain the three
kernel axioms **plus at most the five named oracles**
(`verify_mono.oracle.{h_msg, f, h, t_l, t_len}`) — and nothing else: the
transpiler-plumbing axioms currently in `FunsExternal.lean` must be
discharged before any certificate ships, and the audit fails the button
if any of them (or anything unlisted) appears in a cone.

## Discipline

Every Lean compile in this repository runs under `verification/lean-guard`
(memory-capped, machine-wide serialized). Extraction is reproducible from
the committed `extract.sh` against the pinned snapshot (R1). What cannot
be proven is named in [TRUSTED-BASE.md](TRUSTED-BASE.md), not hidden (H5).
