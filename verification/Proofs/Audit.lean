/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/Audit.lean — the axiom-cone audit, performed INSIDE Lean.

   Round-2 external review (2026-07-24) showed the bash `#print axioms` text
   parser was still fragile: it fail-OPENED on an empty `[]` or a truncated
   (missing-`]`) report, and it only subset-checked (a *removed* oracle
   dependency would pass unnoticed). This file removes text parsing entirely.

   `collectAxioms` reads the kernel's own axiom set for each certificate. We
   assert, for every one of the eleven:

     · the certificate EXISTS and is a `theorem` (not an axiom/opaque sham,
       not a renamed/deleted name — `collectAxioms` returns `#[]` for a
       missing name, so existence is checked explicitly, fail-closed);
     · its cone equals its EXPECTED set EXACTLY — extras (a smuggled axiom)
       AND missing (a silently dropped oracle dependency) both fail.

   Any mismatch is a `throwError`, i.e. a Lean elaboration error → non-zero
   `lean` exit. There is no text to misparse and nothing fails open. This is
   the single source of the axiom claim; check.sh Phase 3 just compiles it.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ChainSpec
import Proofs.WotsSpec
import Proofs.XmssSpec
import Proofs.HtSpec
import Proofs.ForsInnerSpec
import Proofs.ForsOuterSpec
import Proofs.InputPrepSpec
import Proofs.ApexSpec
open Lean Elab Command

namespace SlhVerify.Audit

/-- Lean's three kernel axioms — permitted in every cone. -/
def kernel3 : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The five SHA-2 verify-path hash oracles — the documented cryptographic
    boundary (TRUSTED-BASE.md). No other axiom may appear anywhere. -/
def oracleF    : Name := `verify_mono.oracle.f
def oracleH    : Name := `verify_mono.oracle.h
def oracleTL   : Name := `verify_mono.oracle.t_l
def oracleTLen : Name := `verify_mono.oracle.t_len
def oracleHMsg : Name := `verify_mono.oracle.h_msg

/-- The entire allowed boundary: nothing outside this set is permitted in any
    certificate cone, and the expected table below may reference nothing else. -/
def allowedBoundary : List Name :=
  kernel3 ++ [oracleF, oracleH, oracleTL, oracleTLen, oracleHMsg]

/-- EXACT expected cone per certificate. Ground truth captured 2026-07-24 via
    `collectAxioms` (Probe.lean) and cross-checked against both round-1
    reviewers' independent reconstructions. Each entry is asserted for SET
    EQUALITY, so this table is a load-bearing specification of the boundary:
    changing a proof so it drops an oracle, or adds one, breaks the audit. -/
def expectedCones : List (Name × List Name) :=
  [ (`fips205.chain_free_loop_eq,          kernel3 ++ [oracleF]),
    (`fips205.wots_loop1_eq,               kernel3 ++ [oracleF]),
    (`fips205.xmss_loop_eq,                kernel3 ++ [oracleH]),
    (`fips205.ht_loop_eq,                  kernel3 ++ [oracleF, oracleH, oracleTL]),
    (`fips205.fors_inner_loop_eq,          kernel3 ++ [oracleH]),
    (`fips205.fors_outer_loop_eq,          kernel3 ++ [oracleF, oracleH]),
    (`fips205.to_int_loop_eq,              kernel3),
    (`fips205.to_byte_loop_eq,             kernel3),
    (`fips205.wots_csum_loop_eq,           kernel3),
    (`fips205.base2b_outer_loop_eq,        kernel3),
    (`fips205.slh_verify_128s_accepts_iff, kernel3 ++ [oracleF, oracleH, oracleTL, oracleTLen, oracleHMsg]) ]

elab "auditCones" : command => do
  let env ← getEnv
  -- (0) the expected table itself must stay within the boundary — guards a typo
  --     in this file from silently widening what "allowed" means.
  for (cert, expected) in expectedCones do
    for a in expected do
      unless allowedBoundary.contains a do
        throwError "audit table references non-boundary axiom {a} for {cert}"
  -- (1) per certificate: exists ∧ is a theorem ∧ cone == expected set exactly.
  let mut errs : Array String := #[]
  for (cert, expected) in expectedCones do
    match env.find? cert with
    | none                  => errs := errs.push s!"{cert}: NOT FOUND (renamed/deleted?)"
    | some (.thmInfo _)     =>
        let got := (← collectAxioms cert).toList
        let extras  := got.filter      (fun a => !expected.contains a)
        let missing := expected.filter (fun a => !got.contains a)
        unless extras.isEmpty && missing.isEmpty do
          errs := errs.push s!"{cert}: extra={extras} missing={missing}"
    | some (.axiomInfo _)   => errs := errs.push s!"{cert}: is an AXIOM, not a proven theorem"
    | some (.opaqueInfo _)  => errs := errs.push s!"{cert}: is OPAQUE, not a proven theorem"
    | some _                => errs := errs.push s!"{cert}: not a theorem"
  unless errs.isEmpty do
    throwError "EXACT-CONE AUDIT FAILED (fail-closed):\n{String.intercalate "\n" errs.toList}"
  logInfo s!"exact-cone audit PASSED: {expectedCones.length} certificates, each cone == its expected boundary set (kernel-3 + only the named SHA-2 oracles)"

end SlhVerify.Audit

open SlhVerify.Audit in
auditCones
