/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/Audit.lean — the axiom-cone + statement + coverage audit, in Lean.

   History: round 2 moved the axiom check inside Lean (collectAxioms, exact
   per-cert set equality). Round 4 (third reviewer, 2026-07-24) demonstrated
   that exact-cone-per-cert, while sound FOR LISTED certs, left three gaps
   OUTSIDE the cone check — all fail-open:
     F1  the audited SET was unbound: deleting a manifest row silently drops a
         cert, and adding an un-manifested theorem (e.g. `: False := cheat _`)
         was never looked at → the repo could prove False under ALL GREEN.
     F2  only cones were bound, never STATEMENTS: a certificate whose type was
         replaced by a tautology of the same cone passed green.
     F3  (handled in check.sh) the gen/ model bytes were unbound to provenance.

   This file now closes F1 and F2 with three layers:
     (1) NAMED CERTS — each of the eleven: exists ∧ is a `theorem` ∧ cone ==
         its expected set EXACTLY ∧ its elaborated-type structural fingerprint
         (`Expr.hash`) == the committed value. A gutted statement changes the
         fingerprint → fail (F2).
     (2) FULL-MODULE ENUMERATION — EVERY theorem defined in the eight
         certificate modules must have a cone ⊆ the allowed boundary. An
         un-manifested `: False := cheat _` has cone {cheat} ⊄ boundary → fail,
         whether or not anyone "listed" it (F1, the dangerous half).
     (3) MANIFEST FINGERPRINT — a hash over the whole committed manifest
         (names + cones + type fingerprints) is printed; check.sh binds to the
         exact committed value, so deleting/swapping a row, or editing a cone or
         a fingerprint, changes it and fails the build outside Lean too (F1, the
         set-binding half).

   Any mismatch is a `throwError` → non-zero `lean` exit. Nothing fails open for
   a listed cert, an unlisted theorem, a gutted statement, or a dropped oracle.
   The standing limit (unchanged, disclosed): an audit cannot defend against an
   author who edits the manifest AND check.sh AND the proofs together; the
   consumer defense is the pinned commit reviewed at the pin.
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

/-- Lean's three kernel axioms. -/
def kernel3 : List Name := [`propext, `Classical.choice, `Quot.sound]

def oracleF    : Name := `verify_mono.oracle.f
def oracleH    : Name := `verify_mono.oracle.h
def oracleTL   : Name := `verify_mono.oracle.t_l
def oracleTLen : Name := `verify_mono.oracle.t_len
def oracleHMsg : Name := `verify_mono.oracle.h_msg

/-- The only axioms permitted in ANY cone in the certificate modules: kernel-3
    plus the five SHA-2 oracles. -/
def allowedBoundary : List Name :=
  kernel3 ++ [oracleF, oracleH, oracleTL, oracleTLen, oracleHMsg]

/-- The eight certificate-bearing proof modules. Every `theorem` defined in
    these must have a cone ⊆ allowedBoundary (layer 2). -/
def certModules : List Name :=
  [`Proofs.ChainSpec, `Proofs.WotsSpec, `Proofs.XmssSpec, `Proofs.HtSpec,
   `Proofs.ForsInnerSpec, `Proofs.ForsOuterSpec, `Proofs.InputPrepSpec, `Proofs.ApexSpec]

/-- THE COMMITTED MANIFEST: for each certificate, its exact expected cone and
    the structural fingerprint (`Expr.hash`) of its elaborated statement. Ground
    truth captured 2026-07-27 via Probe.lean; cross-checked against the round-1/2
    cone reconstructions. Changing a proof (cone) OR a statement (fingerprint)
    breaks the audit; adding/removing a row changes the manifest fingerprint that
    check.sh binds to. -/
def manifest : List (Name × List Name × UInt64) :=
  [ (`fips205.chain_free_loop_eq,          kernel3 ++ [oracleF],                              2535491171),
    (`fips205.wots_loop1_eq,               kernel3 ++ [oracleF],                              2968777228),
    (`fips205.xmss_loop_eq,                kernel3 ++ [oracleH],                              763493610),
    (`fips205.ht_loop_eq,                  kernel3 ++ [oracleF, oracleH, oracleTL],           1071622136),
    (`fips205.fors_inner_loop_eq,          kernel3 ++ [oracleH],                              2102092697),
    (`fips205.fors_outer_loop_eq,          kernel3 ++ [oracleF, oracleH],                     2749583942),
    (`fips205.to_int_loop_eq,              kernel3,                                           3797401829),
    (`fips205.to_byte_loop_eq,             kernel3,                                           3618049364),
    (`fips205.wots_csum_loop_eq,           kernel3,                                           4245103433),
    (`fips205.base2b_outer_loop_eq,        kernel3,                                           324621577),
    (`fips205.slh_verify_128s_accepts_iff, kernel3 ++ [oracleF, oracleH, oracleTL, oracleTLen, oracleHMsg], 2489587792) ]

/-- Canonical serialization of the committed manifest → one hash. check.sh binds
    to the printed value, so any row add/remove/edit, cone change, or fingerprint
    change flips it and fails the build. -/
def manifestFingerprint : UInt64 :=
  let sortName (l : List Name) : List Name :=
    ((l.map toString).toArray.qsort (· < ·)).toList.map (·.toName)
  let ser := String.intercalate ";" (manifest.map (fun (n, cone, fp) =>
    s!"{n}|{String.intercalate "," ((sortName cone).map toString)}|{fp}"))
  String.hash ser

elab "auditCones" : command => do
  let env ← getEnv
  let mut errs : Array String := #[]
  -- (0) the manifest's expected cones may reference nothing outside the boundary
  for (cert, cone, _) in manifest do
    for a in cone do
      unless allowedBoundary.contains a do
        throwError "manifest references non-boundary axiom {a} for {cert}"
  -- (1) NAMED CERTS: exists ∧ theorem ∧ exact cone ∧ statement fingerprint
  for (cert, expected, expFp) in manifest do
    match env.find? cert with
    | none                  => errs := errs.push s!"{cert}: NOT FOUND (renamed/deleted?)"
    | some (.thmInfo ci)     =>
        let got := (← collectAxioms cert).toList
        let extras  := got.filter      (fun a => !expected.contains a)
        let missing := expected.filter (fun a => !got.contains a)
        unless extras.isEmpty && missing.isEmpty do
          errs := errs.push s!"{cert}: cone extra={extras} missing={missing}"
        unless ci.type.hash == expFp do
          errs := errs.push s!"{cert}: STATEMENT fingerprint {ci.type.hash} ≠ committed {expFp} (statement changed?)"
    | some (.axiomInfo _)   => errs := errs.push s!"{cert}: is an AXIOM, not a proven theorem"
    | some (.opaqueInfo _)  => errs := errs.push s!"{cert}: is OPAQUE, not a proven theorem"
    | some _                => errs := errs.push s!"{cert}: not a theorem"
  -- (2) FULL-MODULE ENUMERATION: every theorem in a cert module has a clean cone.
  --     This is the layer that stops an un-manifested `: False := cheat _`.
  let manifestNames := manifest.map (·.1)
  let mut nModuleThms := 0
  let mut certsSeen : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ =>
      match env.getModuleIdxFor? nm with
      | some idx =>
        if certModules.contains env.header.moduleNames[idx.toNat]! then
          nModuleThms := nModuleThms + 1
          if manifestNames.contains nm then certsSeen := certsSeen.push nm
          let cone := (← collectAxioms nm).toList
          let bad := cone.filter (fun a => !allowedBoundary.contains a)
          unless bad.isEmpty do
            errs := errs.push s!"UN-AUDITED theorem {nm} (module {env.header.moduleNames[idx.toNat]!}) has disallowed axioms {bad}"
      | none => pure ()
    | _ => pure ()
  -- every manifest cert must actually be a theorem found in a cert module
  for cert in manifestNames do
    unless certsSeen.contains cert do
      errs := errs.push s!"manifest cert {cert} not found as a theorem in any certificate module"
  unless errs.isEmpty do
    throwError "AUDIT FAILED (fail-closed):\n{String.intercalate "\n" errs.toList}"
  logInfo s!"exact-cone audit PASSED: {manifest.length} certificates (cones + statement fingerprints), {nModuleThms} module theorems enumerated clean; MANIFEST-FINGERPRINT: {manifestFingerprint}"

end SlhVerify.Audit

open SlhVerify.Audit in
auditCones
