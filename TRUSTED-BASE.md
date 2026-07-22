# TRUSTED-BASE — what the certificates will NOT cover

Initial statement, written at skeleton time (nothing proven yet); this
file is maintained as the campaign proceeds and is part of every claim.

1. **The six hash oracles.** `h_msg, prf, f, h, t_l, t_len`
   (SLH-DSA-SHA2-128s instantiations over SHA-256) are modeled as opaque
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
7. **Aeneas-compat patch surface.** The fn-pointer-to-named-oracle
   rewrite in `fips205-source` (phase 1) is part of the verified surface:
   the certificate covers the patched verify path, and the patch commits
   are the auditable delta from upstream `30bac08`.
