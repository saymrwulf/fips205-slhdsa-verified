# fips205-slhdsa-verified

Machine-checked verification campaign for the **SLH-DSA (FIPS 205) verify
path**, extracted from a pure-Rust implementation into Lean 4 via
Charon/Aeneas — the same pipeline, discipline, and honesty rules as the
four ed25519 campaigns (`dalek/anza/risc0/betrusted-ed25519-verified`).

## STATUS: eleven certificates over the extracted verify model (external review rounds 1–6 applied)

`verification/check.sh` is **green** (exit 0): the model compiles, the proofs
compile, and the audit passes. It binds **six** things, each added because an
external reviewer *demonstrated* the button going green without it. Four are
checked **inside Lean** by `verification/Proofs/Audit.lean`; the last two are
separate phases that deliberately do **not** rely on that file:

- **axiom cones** — each certificate's cone is read from the kernel via
  `collectAxioms` and must equal its expected set EXACTLY, so an added axiom
  and a silently dropped oracle both fail (round 2 retired a text parser that
  could fail open on an empty or truncated report);
- **coverage** — EVERY declaration in the eight certificate modules, of every
  kind, and in `Audit.lean` itself, must stay inside the axiom boundary (rounds
  4–5: an un-manifested `theorem : False`, then a `def : False`, then one inside
  the auditor, each passed a gate that checked only the listed certificates);
- **statements and specifications** — `check.sh` binds to the **SHA-256** of a
  canonical block containing the policy constants, every certificate's
  fully-elaborated statement, and every reference fold's fully-elaborated
  *body*. Round 5 showed why the last part is essential: redefining a fold to
  *be* the extracted loop left every earlier fingerprint bit-identical while the
  certificate degenerated to "the loop equals the loop";
- **bytes** — Phase 0 sha256-pins the five model files and the compiler harness
  `lean-guard`, purges stale `.olean`s, and forbids stray `.lean` files, so the
  verdict depends on committed bytes rather than build-directory state;
- **correspondence** (Phase 0d) — byte pins say the model did not *change*; they
  say nothing about whether it *answers the extraction*. Aeneas states what the
  extracted Rust needs from outside in `FunsExternal_Template.lean`, and every
  such name must be answered by the hand-written model or by a real definition
  in the corpus. An **extra axiom** in the model — an assumption no template
  asks for — fails the button rather than passing as a silent row. This
  repository previously deleted the template on every run, which is exactly why
  it shipped a Template/model pair with no correspondence check at all
  (round-8 estate review, GPT-5.6);
- **the object files** (Phase 3b) — a second, independently implemented axiom
  gate that reads the compiled `.olean`s via `readModuleData` instead of the
  elaboration-time environment. Phase 3's view has a demonstrated blind spot: a
  declaration made *after* the command that performs the walk sits in the object
  file but not in the environment while the walk runs, so the walker reports "no
  axiom" and is telling the truth about what it could see. Verified here by
  planting `axiom cheat : ∀ (P : Prop), P` after the audit command — Phase 3
  passed it, Phase 3b rejected it.

What the button still does **not** bind is stated plainly in
[TRUSTED-BASE.md](TRUSTED-BASE.md) item 11 — `check.sh` itself, the toolchain
env, and `$AENEAS_HOME`. `verification/check-selftest.sh` runs the reviewers'
own exploits back against the gate; all are rejected.

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
  `verify_mono` facade; the bridge to upstream's generic `pk.verify()` is a
  finite **differential test**, not a machine-checked refinement. Its size is
  now stated rather than left to the word "finite": **137 evaluated
  input/verdict cases on the proved path**, of which **20 are NIST ACVP
  SHA2-128s known-answer tests** (9 retained original + 108 randomized + 10 NIST
  internal + 10 NIST external-pure; see TRUSTED-BASE.md item 9 for the table and
  for the 3 deployed-only prehash cases counted separately). Until 2026-07-28 it
  was nine cases from a single seed, and this parameter set had *no* NIST
  verification coverage at all — the vectors vendored upstream contain no
  SHA2-128s sigVer group, so the 128s groups were extracted from the official
  NIST ACVP-Server set by a committed, re-runnable script
  (`tests/nist_acvp_vectors/extract_sha2_128s.py` in the snapshot repo) that
  pins the upstream hash and fails closed on any drift.
- **Not closed-form FIPS 205 correctness:** the folds are transliterations of
  the extracted loops (the hash primitives stay opaque); nothing here relates
  the recomputed root to a mathematical SLH-DSA specification.
- **Read every loop certificate as "visible", not "correct".** This follows
  from the previous point but is worth stating on its own, because the per-
  certificate descriptions below are easy to over-read. Each reference fold is
  built from the *same* extracted primitives the loop calls, so any defect in
  the extracted code is faithfully copied into the fold and the theorem still
  holds. What is machine-checked is the loop's *scaffolding* — trip count,
  index arithmetic, state threading, argument order, branch structure. Whether
  the address schedule, the Merkle sibling order, or the FORS leaf index match
  FIPS 205 is a **human reading step**, not a proved one. (Round-5 review makes
  this sharper: the certificates are individually meaningful only to the extent
  someone has read each fold against the standard — see TRUSTED-BASE item 12.)

This is a real **intermediate** verification layer, not an end-to-end
formal verification of the deployed verifier. After de-plumbing rounds 1+2
the model carries no plumbing axioms on the verify path — its external
surface is exactly the five SHA-2 oracles (plus off-path zeroize impls).
The trust base and residual assumptions are stated in
[TRUSTED-BASE.md](TRUSTED-BASE.md).

- **`fips205.chain_free_loop_eq`** (Algorithm 5, WOTS+ chaining): the
  extracted `chain_free` loop equals the explicit s-fold hash chain, with
  the hash address set to i, i+1, …, i+s−1 in turn. This rules out —
  machine-checked, for the monomorphic SHA2-128s `verify_mono` path — an
  off-by-one loop bound and wrong state threading. (It does **not** rule out
  a wrong ADRS field: the reference fold is built from the same extracted
  `set_hash_address` primitive the loop calls, so a wrong field would be
  faithfully copied into the fold and the theorem would still hold. What the
  certificate pins is what the extracted code does at each index, so a wrong
  field is *visible* in the certificate, not *excluded* by it — the mapping
  onto FIPS 205 Alg 5 is a human reading step, consistent with "the folds are
  transliterations of the extracted loops" above.) Its
  `#print axioms` cone is **exactly** `[propext, Classical.choice,
  Quot.sound, verify_mono.oracle.f]` — the three kernel axioms plus the one
  hash oracle it touches, and nothing else (no transpiler plumbing; the u32
  range machinery was discharged with real definitions). check.sh Phase 3
  (the in-Lean exact-cone audit) fails the build if any certificate's cone
  differs from its expected set — an extra axiom or a dropped oracle both
  break it.

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
  the tree index to (i−1)/2 and hashes H(auth[k] ∥ node). This makes the
  Merkle sibling ORDER (the even/odd rule), the tree-height/tree-index
  address schedule, and the auth-path indexing VISIBLE in the certificate —
  **it does not establish them as correct.** `xmssFoldN` calls the same
  extracted `set_tree_height`/`get_tree_index`/`oracle.h` that the loop body
  calls, so a swapped sibling order would be copied into the fold and the
  theorem would still hold. Read that as: the certificate pins what the
  extracted code *does* at each step; whether that matches FIPS 205
  Algorithm 10 is a human reading step. Cone: kernel three +
  `verify_mono.oracle.h` (the first
  certificate where H enters; F does not — the loop runs above the WOTS+
  computation).

- **`fips205.ht_loop_eq`** (Algorithm 12, hypertree verification — the
  layer walk): the extracted `ht_verify_free_loop` equals the fold that,
  at layer j, splits the tree index (idx_leaf = idx_tree mod 2^h' by
  mask+cast, then idx_tree >>= h'), sets the layer address to j and the
  tree address to the shifted index, and recomputes the node through
  `xmss_pk_from_sig` on the j-th XMSS signature. This makes the layer
  schedule of hypertree verification visible in the certificate (same
  transliteration caveat as above); the final node = pk_root comparison
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
each site a local rewrite whose equivalence is argued in the commit and
checked, for SHA2-128s, by the differential test; the obsoleted transpiler
axioms were deleted from the external files); fidelity pinned by that
differential test in the snapshot — since 2026-07-28 a randomized bridge
(12 rounds, corruption across the whole signature, wrong-key and wrong-context
cases) plus NIST ACVP 128s known-answer tests — re-run green after every
source patch.

- **`fips205.fors_inner_loop_eq`** + **`fips205.fors_outer_loop_eq`**
  (Algorithm 17, FORS pk-from-sig): a nested loop, split into two theorems.
  The inner one equates the auth-path Merkle fold for a single FORS tree (bit
  source `indices[i] >> j`, `H` in the even/odd sibling order) — cone
  kernel-3 + `oracle.h`. The outer one equates the K-tree fold: for each tree
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

The apex (`slh_verify_128s_accepts_iff`, above) sits at the top of this layer:
the extracted `verify_mono::slh_verify_128s` accepts iff the recomputed
hypertree root byte-equals the pinned public-key root. What remains genuinely
unproven is stated in "What is NOT (yet) established" above — most sharply the
opaque `base_2b` inner loop (no certificate) and the bridge from this private
`verify_mono` facade to the deployed generic verifier (a finite differential
test, not a machine-checked refinement). Each certificate is audited to the
same boundary.

## Subject

- Upstream: `integritychain/fips205` — pure-Rust FIPS 205 (final standard,
  2024-08-13), zero `unsafe`, `no_std`, const-generic parameterization,
  modules mirroring the FIPS 205 algorithm structure.
- Pinned at upstream commit `30bac08580aa61f653e5436d1bbacb5ffac446c4`
  (2025-09-01), snapshotted with full history at
  `saymrwulf/fips205-source`. The verbatim-import base commit's only
  deviation from upstream is the removal of CI workflows (documented in
  that commit); the Aeneas-compat and de-plumbing patches then landed as
  transparent, individually-justified commits on top — never upstream.
  The current snapshot head is **`a3ce8e8`** — the NIST ACVP SHA2-128s sigVer
  vectors plus an expanded differential bridge. That commit is TEST-ONLY: no
  verify-path function changed, and re-running `extract.sh` against it
  reproduces the two Aeneas-generated model files byte-identically. Its
  lineage is `bea1051` (de-plumbing round 2) → `797b4ef` (the round-2
  reproducibility commit: committed `Cargo.lock` + pinned
  `rust-toolchain.toml`) → `a3ce8e8`; the model in this repo is extracted from
  it, and `verification/extract.sh` refuses any other commit. **No
  affiliation with, and no changes proposed to, the upstream project.**
- Parameter set: **SLH-DSA-SHA2-128s** first (the small-signature profile
  deployed in the firmware/code-signing lane). The architecture
  generalizes; each further parameter set is a separate claim (rigor
  invariant R2).

## Scope

**Verify path only, rooted at `slh_verify_internal`.** The extraction root
is `verify_mono::slh_verify_128s`, which is `slh_verify_internal_free(M′, sig,
pk)` — it takes the already-assembled message digest input **M′ as an
argument**. So the covered cone is:

```
slh_verify_internal(M′, …)         ← the extraction ROOT (M′ is an input)
  -> fors_pk_from_sig
  -> ht_verify -> xmss_pk_from_sig -> wots_pk_from_sig -> chain
```

Everything **above** this root, in `slh_verify`/`verify` (`src/lib.rs`), is
OUT of scope and is stated as such in [TRUSTED-BASE.md](TRUSTED-BASE.md): M′
assembly, the pure-vs-prehash **domain-separator byte** (`0u8` for `verify`,
`1u8` for `hash_verify` — the entire cross-variant separation), the
`ctx.len() > 255` check, and signature/public-key deserialization. A reader
must NOT read `slh_verify -> slh_verify_internal` as "the top of the verify
path is covered" — it is not; the top-of-path input handling is trusted base.
Key generation and signing are out of scope (trusted base), exactly as
ed25519 signing was. The five verify-path hash oracles (`h_msg, f, h,
t_l, t_len` — SHA-2 instantiations; `prf`/`prf_msg` are sign-side only
and never enter the cone) are opaque external models with written
justifications. They are the *only* things beyond Lean's three kernel
axioms that any certificate cone contains: each cone is exactly the
kernel three plus the specific oracles that certificate's computation
reaches (e.g. `chain` reaches `F`, so `oracle.f` is inside its cone; the
input-prep helpers reach no hash, so their cones are kernel-3 alone).
That the cones contain *nothing else* — no transpiler plumbing, no
hidden axiom — is what the audit enforces (honesty invariant H4); their
semantics are the standing SHA-2 oracle boundary documented in
[TRUSTED-BASE.md](TRUSTED-BASE.md).

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
  `verification/check.sh` compiles the result. At this compat-patch commit
  the only change to pre-existing code was two lines wiring the new module;
  the generic paths and all twelve parameter sets stayed untouched. **That
  scoping does not extend to the later de-plumbing commits, and the difference
  matters:** round 1 (`6f6a9d6`) touched only the private `verify_mono.rs`, but
  round 2 (`bea1051`) rewrote `to_int` and `base_2b` in **`src/helpers.rs`,
  which the DEPLOYED generic verify path and the SIGNING path also call**
  (`slh.rs`, `wots.rs`, `fors.rs`). So the snapshot's deployed verifier — the
  one the differential test compares against — is itself patched relative to
  upstream `30bac08`. `src/wots.rs` was never modified by any patch commit (an
  earlier revision of this README wrongly named it). See the snapshot history
  at head `a3ce8e8` and TRUSTED-BASE.md item 7.

## What is claimed (the button is green)

Each certificate is a statement about the **extracted** functions (H3),
compiled by `verification/check.sh` with the in-Lean exact-cone audit (H1):
chain semantics, WOTS+ pk recomputation, XMSS path recomputation, hypertree
acceptance, FORS pk recomputation, the input-prep helpers, and the apex —
`verify_mono::slh_verify_128s` accepts iff the recomputed hypertree root
equals the pinned public-key root. The precise scope and non-claims are in
the STATUS section above.

**The allowed axiom set, stated precisely:** unlike the ed25519 field and
scalar layers (whose cones are exactly `[propext, Classical.choice,
Quot.sound]`), the hash oracles permeate *every* SLH-DSA layer — `chain`
already calls `F`. Each certificate's cone is therefore the three kernel
axioms **plus exactly the named oracles its computation reaches** (and
nothing else). The transpiler-plumbing axioms that once sat in
`FunsExternal.lean` were discharged (de-plumbing rounds 1+2) before any
certificate shipped; the audit fails the button if anything outside a
certificate's expected boundary — plumbing, an extra oracle, or a dropped
one — appears in its cone.

## Discipline

Every Lean compile in this repository runs under `verification/lean-guard`
(memory-capped, machine-wide serialized). It is Linux-oriented but **degrades
gracefully**: when `systemd-run` is unavailable it falls back to Lean's own
`-M` cap, so the button runs on a stock Linux box without cgroup support — an
external reviewer has run it green that way. Note also that the *empirical
bridge* (`cargo test` in the snapshot repo) needs no Lean toolchain at all and
runs on stable Rust. Extraction is reproducible: the
full pin set (source commit, Charon/Aeneas commits + toolchain channel, Lean
and OCaml versions) is in [verification/PROVENANCE.json](verification/PROVENANCE.json);
`verification/extract.sh` refuses to run against a wrong-commit or dirty
source tree, and re-running it reproduces the aeneas-generated model
byte-identically (verified 2026-07-24). The axiom audit runs inside Lean
([verification/Proofs/Audit.lean](verification/Proofs/Audit.lean)): exact
per-certificate cone equality, fail-closed, adversarially exercised by
`verification/check-selftest.sh`. What cannot be proven is named in
[TRUSTED-BASE.md](TRUSTED-BASE.md), not hidden (H5).
