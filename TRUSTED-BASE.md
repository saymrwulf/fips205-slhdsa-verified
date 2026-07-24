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
