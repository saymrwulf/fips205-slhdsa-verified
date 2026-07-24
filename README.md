# fips205-slhdsa-verified

Machine-checked verification campaign for the **SLH-DSA (FIPS 205) verify
path**, extracted from a pure-Rust implementation into Lean 4 via
Charon/Aeneas — the same pipeline, discipline, and honesty rules as the
four ed25519 campaigns (`dalek/anza/risc0/betrusted-ed25519-verified`).

## STATUS: eleven certificates over the extracted verify model (external review round 1 applied)

`verification/check.sh` is **green** (exit 0): the model compiles, the
proofs compile, and the axiom audit passes (the Phase-3 parser was rewritten
to be fail-closed and wrap-safe after external review round 1, 2026-07-24).

**What is actually established** — eleven Lean theorems about the
Aeneas-generated model of the **monomorphic `verify_mono` compatibility
verify path** (an additive, `#![allow(dead_code)]` re-expression of the
deployed generic verifier, using named hash oracles because Charon/Aeneas
cannot translate the deployed `Hashers` function-pointer struct):

- **Ten loop-fidelity theorems** (chain 5, WOTS+ 8, XMSS 10, hypertree 12,
  FORS-inner/outer 17, and the input-prep helpers to_int/to_byte/checksum/
  base_2b-outer, Alg 2/3/4). Each equates one *generated* Aeneas loop with an
  explicit hand-written recursive fold — a local control-flow correspondence,
  not an Algorithm-level mathematical specification.
- **The apex, `fips205.slh_verify_128s_accepts_iff`** — the extracted
  `verify_mono::slh_verify_128s` returns `ok true` **iff** the recomputed
  hypertree root byte-equals `pk.pk_root`. This is an *acceptance
  characterization*: there is no acceptance path other than root equality
  over the extracted recomputation. Its `#print axioms` cone is exactly
  `[propext, Classical.choice, Quot.sound]` + the five SHA-2 oracles.

**What is NOT (yet) established — do not overclaim:**
- **The apex proof does not compose the ten loop theorems.** It is a
  *structural factorization* of the extracted verifier around its final
  equality check; it references none of the ten (it would remain provable if
  one were deleted). The ten are independent local-fidelity lemmas, not links
  in the apex's proof chain.
- **Not "every loop":** `base_2b`'s inner accumulation loop
  (`helpers.base_2b_loop0_loop0`) is threaded *opaquely* and has no
  certificate — and it determines the FORS indices / WOTS digits, so a defect
  there could change the recomputed root while all eleven theorems still hold.
- **Not the deployed public verifier:** the proved subject is the private
  `verify_mono` facade; the bridge to upstream's generic `pk.verify()` is the
  finite in-snapshot **differential test**, not a machine-checked refinement.
- **Not closed-form FIPS 205 correctness:** the folds are transliterations of
  the extracted loops (the hash primitives stay opaque); nothing here relates
  the recomputed root to a mathematical SLH-DSA specification.

This is a real **intermediate** verification layer, not an end-to-end
formal verification of the deployed verifier. After de-plumbing rounds 1+2
the model carries no plumbing axioms on the verify path — its external
surface is exactly the five SHA-2 oracles (plus off-path zeroize impls).
The trust base and residual assumptions are stated in
[TRUSTED-BASE.md](TRUSTED-BASE.md).

- **`fips205.chain_free_loop_eq`** (Algorithm 5, WOTS+ chaining): the
  extracted `chain_free` loop equals the explicit s-fold hash chain, with
  the hash address set to i, i+1, …, i+s−1 in turn. This rules out —
  machine-checked, for the deployed monomorphic SHA2-128s verify path — an
  off-by-one loop bound, a wrong address field, and wrong threading. Its
  `#print axioms` cone is **exactly** `[propext, Classical.choice,
  Quot.sound, verify_mono.oracle.f]` — the three kernel axioms plus the one
  hash oracle it touches, and nothing else (no transpiler plumbing; the u32
  range machinery was discharged with real definitions). check.sh Phase 3
  fails the build if any certificate cone contains anything outside the
  kernel three + the five documented SHA-2 oracles.

- **`fips205.wots_loop1_eq`** (Algorithm 8, WOTS+ pk recomputation — the
  chain loop): the extracted `wots_pk_from_sig_free_loop1` equals the fold
  that, at each index i in [0, LEN), sets the chain address to i and runs
  `chain_free` on sig[i] starting at digit msg[i] for W−1−msg[i] steps,
  writing tmp[i]. This is the layer above chain: it consumes `chain_free`
  and pins that the LEN chains run with the right start indices, step
  counts, and slots. Cone: kernel three + `verify_mono.oracle.f`.

- **`fips205.xmss_loop_eq`** (Algorithm 10, XMSS pk-from-sig — the
  authentication-path Merkle loop): the extracted
  `xmss_pk_from_sig_free_loop` equals the fold that, at step k, sets the
  tree height to k+1, tests bit k of the leaf index, and on an even bit
  halves the tree index and hashes H(node ∥ auth[k]), on an odd bit sets
  the tree index to (i−1)/2 and hashes H(auth[k] ∥ node). This pins the
  Merkle sibling ORDER (the even/odd rule), the tree-height/tree-index
  address schedule, and the auth-path indexing — the heart of Merkle-path
  verification. Cone: kernel three + `verify_mono.oracle.h` (the first
  certificate where H enters; F does not — the loop runs above the WOTS+
  computation).

- **`fips205.ht_loop_eq`** (Algorithm 12, hypertree verification — the
  layer walk): the extracted `ht_verify_free_loop` equals the fold that,
  at layer j, splits the tree index (idx_leaf = idx_tree mod 2^h' by
  mask+cast, then idx_tree >>= h'), sets the layer address to j and the
  tree address to the shifted index, and recomputes the node through
  `xmss_pk_from_sig` on the j-th XMSS signature. This pins the layer
  schedule of hypertree verification; the final node = pk_root comparison
  sits one bind above, in `ht_verify_free`, and belongs to the apex
  composition. Cone: kernel three + `verify_mono.oracle.{f, h, t_l}` —
  the full WOTS+/XMSS machinery referenced through the fold, and nothing
  else.

Foundations behind this (2026-07-22/23): the Aeneas-compat patch (additive
monomorphic verify module through a named oracle boundary; charon + aeneas
exit 0); the u32 range-loop de-plumbing (faithful `Step` defs vs pinned
rustc, axiom-clean); the 8-site source de-plumbing (snapshot commit
`6f6a9d6`: `try_from`/`is_err`/`unwrap` on pre-masked values → plain
casts, the WOTS+ checksum `iter().take()` + `&u32` Sub → an index loop —
each site semantics-identical for every FIPS 205 parameter set, and the
obsoleted transpiler axioms deleted from the external files); fidelity
pinned by a differential test in the snapshot (valid / corrupted /
wrong-message), re-run green after every source patch.

- **`fips205.fors_inner_loop_eq`** + **`fips205.fors_outer_loop_eq`**
  (Algorithm 17, FORS pk-from-sig): a nested loop, split into two theorems.
  The inner one pins the auth-path Merkle fold for a single FORS tree (bit
  source `indices[i] >> j`, `H` in the even/odd sibling order) — cone
  kernel-3 + `oracle.h`. The outer one pins the K-tree fold: for each tree
  compute the leaf with `F` at index `(i<<a)+indices[i]`, run the inner
  Merkle loop, write `root[i]` — cone kernel-3 + `oracle.{f, h}`. Split into
  two files under the memory discipline; the outer step lemma closes by
  peeling its 16-bind body with `bind_congr` (a bare `rfl` there whnf-times-
  out over the nested inner `loop`).

- **input-prep** (`fips205.to_int_loop_eq`, `to_byte_loop_eq`,
  `wots_csum_loop_eq`, `base2b_outer_loop_eq` — Algorithms 2/3/4 + the WOTS+
  checksum): the byte→integer, integer→byte, checksum, and digit-decomposition
  loops that prepare the verifier's inputs. All four cones are **exactly**
  `[propext, Classical.choice, Quot.sound]` — pure kernel-3, no hash oracle
  (byte/bit arithmetic touches no hash). `base_2b`'s inner `while` loop is
  threaded opaquely, as every layer treats its sub-loops. These proofs became
  possible after **de-plumbing round 2** (snapshot `bea1051`) rewrote
  `to_int`'s `iter().take()` and `base_2b`'s `iter_mut()` as index loops,
  removing the last `Take`/`IterMut` iterator adapters; the obsoleted `Take`
  axiom was then deleted.

The remaining work (the digest-split composition and the apex — the top-level
`slh_verify` accepting iff the recomputed hypertree root equals the pinned
public-key root) is not yet proven. The pyramid rises one certificate at a
time, each audited to the same boundary.

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
