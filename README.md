# fips205-slhdsa-verified

Machine-checked verification campaign for the **SLH-DSA (FIPS 205) verify
path**, extracted from a pure-Rust implementation into Lean 4 via
Charon/Aeneas — the same pipeline, discipline, and honesty rules as the
four ed25519 campaigns (`dalek/anza/risc0/betrusted-ed25519-verified`).

## STATUS: SKELETON — NOTHING PROVEN YET

There are **zero certificates** in this repository. `verification/check.sh`
exits non-green and says so. Every claim in this README below the line
"What will be claimed" is a *plan*, not a result. (Honesty invariant H5:
an honest gap outranks a hollow certificate.)

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
ed25519 signing was. The six hash oracles (`h_msg, prf, f, h, t_l,
t_len` — SHA-2 instantiations) are opaque external models with written
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
- **Consequence (campaign phase 1)**: an Aeneas-compat patch in
  `fips205-source` will replace the fn-pointer struct with named opaque
  free functions on the verify path — the same pattern as the
  `sha512_new/update/finalize` shims in `curve25519-dalek-source`'s
  verify glue. Until that patch lands, `verification/extract.sh`
  documents intent and produces a partial model.

## What will be claimed (when the button is green, not before)

One theorem per layer, each a statement about the **extracted** functions
(H3), compiled by `verification/check.sh` with `#print axioms` reporting
exactly `[propext, Classical.choice, Quot.sound]` (H1): chain semantics,
WOTS+ pk recomputation, XMSS path recomputation, hypertree acceptance,
FORS pk recomputation, and the apex — `slh_verify_internal` accepts iff
the recomputed hypertree root equals the pinned public-key root, under
the stated oracle boundary.

## Discipline

Every Lean compile in this repository runs under `verification/lean-guard`
(memory-capped, machine-wide serialized). Extraction is reproducible from
the committed `extract.sh` against the pinned snapshot (R1). What cannot
be proven is named in [TRUSTED-BASE.md](TRUSTED-BASE.md), not hidden (H5).
