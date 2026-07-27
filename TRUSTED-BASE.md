# TRUSTED-BASE — what the certificates do NOT cover

Eleven certificates over the extracted `verify_mono` model are now proven
(`verification/check.sh` green; the apex is
`fips205.slh_verify_128s_accepts_iff`). This file states what those
certificates deliberately do NOT establish; it is maintained as the campaign
proceeds and is part of every claim.

1. **The five verify-path hash oracles.** `h_msg, f, h, t_l, t_len`
   (SLH-DSA-SHA2-128s instantiations over SHA-256; `prf`/`prf_msg` are
   sign-side only and do not appear in the cone) are modeled as opaque
   functions with assumed functional behavior. Their correctness against
   FIPS 180-4 is NOT proven here — the same standing boundary as SHA-512
   in the ed25519 apex. A collision or misimplementation inside the hash
   layer is invisible to these certificates.
2. **Signing and key generation.** Out of extraction scope entirely. A
   verified verify path says nothing about the safety of signature or key
   production (including randomness).
3. **The transpilation pair.** Charon and Aeneas (pinned versions in the
   toolchain) are trusted to preserve semantics from Rust (MIR) to the
   Lean model. Divergence between rustc's semantics and the extracted
   model is trusted base.
4. **The Lean kernel and its three axioms**
   (`propext, Classical.choice, Quot.sound`).
5. **Build correspondence.** No reproducible-builds claim: the proof is
   about the pinned source, not about any particular compiled binary
   (the estate's R5 gap, stated everywhere it matters).
6. **Parameter-set scope.** Claims will bind SLH-DSA-SHA2-128s only;
   other parameter sets are unverified until separately extracted and
   proven (R2).
7. **Aeneas-compat + de-plumbing patch surface.** The fn-pointer-to-named-
   oracle rewrite in `fips205-source` (phase 1) and the two de-plumbing
   rounds (index-loop rewrites of the iterator adapters on the verify path,
   de-plumbing round 2 at `bea1051`; current snapshot head `797b4ef`) are
   part of the verified surface: the
   certificates cover the *patched* verify path, and the patch commits are
   the auditable delta from upstream `30bac08`. Each rewrite's equivalence
   to upstream is argued in its commit and checked, for SHA2-128s, by the
   snapshot differential test — it is not itself machine-checked.
8. **The `base_2b` inner loop.** `helpers.base_2b_loop0_loop0` (which
   determines the FORS indices and WOTS digits) is threaded opaquely and
   has no certificate; a defect there could change the recomputed root while
   all eleven theorems still hold.
9. **The deployed generic verifier.** The proved subject is the private
   `verify_mono` facade. The bridge to upstream's generic `pk.verify()` is
   the finite in-snapshot differential test, not a machine-checked
   refinement.
10. **Everything above the extraction root.** The root is
    `verify_mono::slh_verify_128s = slh_verify_internal_free(M′, sig, pk)`,
    which takes the message-digest input **M′ as an argument**. The code in
    `slh_verify`/`verify` (`src/lib.rs`) that runs *before* this root is NOT
    covered by any certificate: the assembly of M′; the pure-vs-prehash
    **domain-separator byte** (`0u8` for `verify` vs `1u8` for `hash_verify`
    — the whole cross-variant domain separation); the FIPS-205 `ctx.len() >
    255` bound; and signature/public-key deserialization. The certificates
    say nothing about this input handling — a defect there (e.g. a wrong
    separator byte) would be outside every proof.
    **Concretely, so the consequence is not left to the reader:** that byte is
    the *only* thing separating the pure and prehash variants. If it were wrong
    or dropped, a signature issued over the pure M′ would verify as a prehash
    signature and vice versa — cross-variant signature confusion, a forgery
    primitive. No certificate in this repository would change.
11. **The verification harness itself.** The certificates are statements
    checked by the Lean kernel, but the *button* that reports them is a shell
    script. Round-5 review demonstrated that stubbing `verification/lean-guard`
    alone — one repo-tracked file, without touching `check.sh`, the manifest, or
    the proofs — yields ALL GREEN in 3.6 seconds over deliberately destroyed
    proofs. `lean-guard` is therefore **sha256-pinned** by check.sh Phase 0
    (`PROVENANCE.json → harness_integrity_sha256`); it is kept rather than
    removed because it is the memory cap and machine-wide lock that protect the
    build machine (a Lean elaboration once reached 12.2 GB and took the host
    down). Still trusted, and NOT bound by anything the button can check:
    `check.sh` itself, `~/aeneas-toolchain/env.sh`, the `$AENEAS_HOME` tree
    (i.e. *which* Aeneas/Lean library the proofs are checked against), `python3`,
    and the Lean toolchain. An audit executed by a harness cannot defend against
    an author who edits that harness; the consumer defense is the pinned commit,
    reviewed at the pin.
12. **Composition.** The apex does **not** compose the ten loop-fidelity
    theorems — it is a structural factorization of the extracted verifier around
    its final equality check and references none of them (it would remain
    provable if one were deleted). The ten are independent, individually
    human-reviewed lemmas. Round-5 review makes this worth stating here rather
    than only in the README: each of the ten is individually meaningful only to
    the extent a human has read its reference fold against FIPS 205.
