# Attestation basis — independent technical review

This file records the **reviewer's own words**, verbatim, as the conditions
attached to any attestation of this repository. It is committed here so that the
limits travel with the artifact rather than living in a review document the
consumer never sees.

Nothing in this file is a decision to attest. The signing-key halt and the
paper-appeal gate are the operator's, and an attest verdict from a reviewer is a
technical input to that decision, not the decision.

---

## Verdict

**Round 8, third reviewer, 2026-07-28: ATTEST, with the conditions below.**

Basis the reviewer performed on hardware, an OS and a toolchain build that are
not the author's: `check.sh` ALL GREEN at `1bc4f39` with six pins verified and
the audit digest `d83e297a…`; `check-selftest.sh` green (17 attacks + the
digest-coverage check); the audit digest recomputed *outside* `check.sh` from a
bare `lean Proofs/Audit.lean` and matched byte-for-byte against the committed
`AUDIT-MANIFEST.txt`; NEW-13 attacked five ways; the NIST vector file
independently re-derived from the official 30.7 MB upstream file and found
byte-identical; the full empirical bridge executed on stable Rust; and the ACVP
harness mutation-tested (a flipped bit in a valid vector and a deleted NIST test
both correctly fail).

Not performed by any reviewer: `verification/extract.sh`. See condition 9.

---

## Conditions, verbatim from the reviewer

> What is established: eleven Lean 4 theorems over the Charon/Aeneas-extracted
> model of `verify_mono::slh_verify_128s`, the private monomorphic re-expression
> of the SLH-DSA-SHA2-128s verify path. Ten are loop-fidelity theorems; the apex,
> `fips205.slh_verify_128s_accepts_iff`, characterises acceptance — the extracted
> verifier returns `ok true` if and only if the recomputed hypertree root
> byte-equals the pinned public-key root. Every certificate's axiom cone is
> exactly Lean's three kernel axioms plus the named SHA-2 oracles that layer
> reaches, machine-checked inside Lean and bound by a SHA-256 digest over the
> policy constants, the elaborated statements and the specification bodies.
>
> This attestation carries the following limits, all of which are stated in the
> repository's own `TRUSTED-BASE.md` and all of which I verified are accurate:
>
> 1. **The five SHA-2 hash oracles are opaque assumptions.** Their conformance to
>    FIPS 180-4 is not proven here. `oracle.t_l` and `oracle.t_len` are two
>    independent axioms over one Rust primitive — conservative, but the model
>    cannot express that they agree.
> 2. **The ten loop certificates are transliteration-fidelity results, not
>    conformance results.** Each equates a generated loop with a hand-written
>    reference fold built from the *same* extracted primitives, so it pins what
>    the extracted code does at each index and makes it visible; it does not
>    exclude a wrong ADRS field or a wrong schedule relative to FIPS 205. Mapping
>    each fold onto the standard remains a human reading step.
> 3. **The apex does not compose the ten.** It is a structural factorization of
>    the extracted verifier around its final equality check and references none
>    of them; it would remain provable if one were deleted.
> 4. **`base_2b`'s inner accumulation loop has no certificate.** It determines
>    the FORS indices and WOTS+ digits, so a defect there could change the
>    recomputed root while all eleven theorems still hold.
> 5. **Everything above the extraction root is uncovered:** M′ assembly, the
>    pure-versus-prehash domain-separator byte, the `ctx.len() > 255` bound, and
>    signature/public-key deserialization.
> 6. **The bridge from the proved `verify_mono` facade to the deployed generic
>    `pk.verify()` is empirical, not a machine-checked refinement:** 137 evaluated
>    input/verdict cases on the proved path, of which 20 are NIST ACVP
>    known-answer tests and 127 compare mono against the deployed verifier. A
>    passing differential test is evidence, not a proof.
> 7. **Trusted and unbound by anything the button can check:** the Lean kernel and
>    its three axioms; the Charon/Aeneas transpilation pair; `verification/check.sh`
>    itself; `~/aeneas-toolchain/env.sh`; the `$AENEAS_HOME` Aeneas/Lean library
>    the proofs are checked against; `python3`; and the Lean toolchain.
>    `lean-guard` and `Proofs/Audit.lean` are sha256-pinned, so tampering with
>    either is a build failure rather than a silent green; an author who edits one
>    *and* rotates its pin in the same commit is caught only by reading the diff
>    at the pin.
> 8. **Scope is SLH-DSA-SHA2-128s only**, verify path only. Key generation and
>    signing are out of scope. No reproducible-builds claim: the proof is about
>    the pinned source, not any compiled binary.
> 9. **`verification/extract.sh`'s byte-identical regeneration of the Lean model
>    from the pinned Rust source has never been observed by any party other than
>    the author.** Every other load-bearing claim in this repository has been
>    reproduced by an independent reviewer on different hardware; this one has
>    not, and it is the claim that ties the Lean model to the Rust source. Until a
>    third party re-runs `extract.sh` at the pinned Charon/Aeneas commits and
>    obtains the two EXTRACTION-GENERATED hashes in `model_integrity_sha256`
>    (`Types.lean` and `Funs.lean` — the other two entries, `TypesExternal.lean`
>    and `FunsExternal.lean`, are HAND-MAINTAINED and are not regenerated by
>    `extract.sh`; they are separately byte-pinned), the correspondence between
>    `fips205-source@a3ce8e8` and `verification/gen/SlhVerify/*.lean` rests on the
>    author's attestation alone.

The reviewer's instruction on condition 9: if a third party later succeeds at
`extract.sh`, sentence 9 is to be **replaced with a statement of what was
reproduced, by whom, on what platform and at which commits — not deleted.**

---

## Status of condition 9 as of 2026-07-28

Still open. Two independent reviewers have now been unable to close it for
different environmental reasons: one sandbox blocks `static.rust-lang.org` and
`opam.ocaml.org` so Charon and Aeneas cannot be built there; the other declined
the task of building the two pinned tools from source. The claim therefore
remains author-attested only, exactly as condition 9 states.
