/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/Audit.lean — the axiom / statement / specification / coverage audit.

   ROUND 5 (third reviewer, 2026-07-27) demonstrated that the round-4 gate was
   closed at the EXPLOITS but not at the MECHANISMS. Three fail-opens, each
   executed end-to-end with the button printing ALL GREEN:

     NEW-1  `manifestFingerprint` covered `manifest` only — never
            `allowedBoundary`, the sole predicate the enumeration tests against.
            Adding one name to that list re-opened the `False`-proof completely,
            with the committed fingerprint BYTE-IDENTICAL.
     NEW-2  the statement fingerprint pinned each certificate's TYPE, which
            references its hand-written reference fold BY NAME. Redefining that
            fold to *be* the extracted loop left cone and type-hash identical
            while the certificate degenerated to "the loop equals the loop" —
            100% of the fidelity content lives in those definitions.
     (drill) layer-2 enumeration matched `.thmInfo` only, so a `def : False`
            passed; and this file's own declarations were enumerated by nothing.

   The fix binds the WHOLE audited object, not the parts an attacker happened to
   touch. This file emits a canonical AUDIT-MANIFEST block covering:

     · the POLICY constants (`allowedBoundary`, `certModules`) — NEW-1;
     · every certificate's fully-elaborated STATEMENT (`pp.all`) — F2 properly;
     · every hand-written SPECIFICATION constant transitively reachable from
       those statements, with its fully-elaborated DEFINITION BODY — NEW-2.
       (Proof-valued constants contribute their statement, not their proof term:
       proof irrelevance makes the term semantically immaterial.)

   `check.sh` binds to the **SHA-256** of that block. This also retires the
   32-bit `Expr.hash` as the load-bearing digest (NEW-5): the per-certificate
   type hashes below remain, but only as fast, human-legible DIAGNOSTICS that
   name which certificate moved — the cryptographic binding is the SHA-256.

   Enumeration now covers EVERY declaration kind (`def`, `theorem`, `opaque`,
   `axiom`, …) in the eight certificate modules AND every declaration of this
   file itself (the auditor is no longer exempt from its own audit — round-5 R1).

   Standing limit, stated accurately (see TRUSTED-BASE.md item 11 for the full
   trusted computing base): an audit executed by a harness cannot defend against
   an author who edits that harness. `verification/lean-guard` is therefore
   sha256-pinned by check.sh Phase 0, but `check.sh` itself, the toolchain env,
   and `$AENEAS_HOME` remain trusted. The consumer defense is, and always was,
   the pinned commit reviewed at the pin.
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

/-- The ONLY axioms permitted in any cone anywhere in the audited modules.
    POLICY CONSTANT — folded into the SHA-256 digest (round-5 NEW-1): widening
    this list changes the digest and fails the build. -/
def allowedBoundary : List Name :=
  kernel3 ++ [oracleF, oracleH, oracleTL, oracleTLen, oracleHMsg]

/-- The eight certificate-bearing proof modules. POLICY CONSTANT — also folded
    into the digest. (It is additionally cross-checked by `certsSeen` below:
    every manifest certificate must be found inside one of these modules.) -/
def certModules : List Name :=
  [`Proofs.ChainSpec, `Proofs.WotsSpec, `Proofs.XmssSpec, `Proofs.HtSpec,
   `Proofs.ForsInnerSpec, `Proofs.ForsOuterSpec, `Proofs.InputPrepSpec, `Proofs.ApexSpec]

/-- Per-certificate expected cone + a 32-bit `Expr.hash` of the elaborated
    statement. The hash is a DIAGNOSTIC ONLY (it names which certificate moved);
    the binding digest is the SHA-256 over the canonical block. -/
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

/-- Deterministic name ordering for the canonical serialization. -/
def sortNames (l : List Name) : List Name :=
  ((l.map toString).toArray.qsort (· < ·)).toList.map (·.toName)

/-- Whitespace-canonical: every whitespace run collapses to one space, so the
    pretty-printer's line wrapping cannot perturb the digest. -/
def normWs (s : String) : String :=
  (s.foldl (fun (acc : String × Bool) c =>
      let c := if c.isWhitespace then ' ' else c
      if c == ' ' then (if acc.2 then acc else (acc.1.push ' ', true))
      else (acc.1.push c, false))
    ("", true)).1

/-- Is `n` a hand-written declaration living in one of the certificate modules?
    These are the SPECIFICATION side — the folds the certificates are stated
    against — as opposed to the extracted model in `gen/` (pinned by Phase 0). -/
def isSpecConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => certModules.contains env.header.moduleNames[idx.toNat]!
  | none => false

/-- Transitive closure over specification constants, starting from a
    certificate's STATEMENT and following DEFINITION bodies (a theorem
    contributes its statement only). This discovers the reference folds — and
    any future one — automatically, so a new specification definition cannot be
    introduced without moving the digest. -/
partial def closureOf (env : Environment) (seen : NameSet) (work : List Name) : NameSet :=
  match work with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isSpecConst env n then closureOf env seen rest
    else
      let seen := seen.insert n
      let more := match env.find? n with
        | some (.defnInfo v) => v.value.getUsedConstants.toList ++ v.type.getUsedConstants.toList
        | some ci            => ci.type.getUsedConstants.toList
        | none               => []
      closureOf env seen (more ++ rest)

/-- Fully-explicit (`pp.all`) rendering, whitespace-canonicalized. -/
def ppAll (e : Expr) : CommandElabM String := do
  let s ← Command.liftCoreM <| Meta.MetaM.run' <|
    withOptions (fun o => o.setBool `pp.all true) do
      return (← Meta.ppExpr e).pretty
  return normWs s

elab "auditCones" : command => do
  let env ← getEnv
  let mut errs : Array String := #[]

  -- (0) the manifest's expected cones may reference nothing outside the policy.
  for (cert, cone, _) in manifest do
    for a in cone do
      unless allowedBoundary.contains a do
        throwError "manifest references non-boundary axiom {a} for {cert}"

  -- (1) NAMED CERTS: exists ∧ is a theorem ∧ exact cone ∧ statement diagnostic.
  for (cert, expected, expFp) in manifest do
    match env.find? cert with
    | none                 => errs := errs.push s!"{cert}: NOT FOUND (renamed/deleted?)"
    | some (.thmInfo ci)   =>
        let got := (← collectAxioms cert).toList
        let extras  := got.filter      (fun a => !expected.contains a)
        let missing := expected.filter (fun a => !got.contains a)
        unless extras.isEmpty && missing.isEmpty do
          errs := errs.push s!"{cert}: cone extra={extras} missing={missing}"
        unless ci.type.hash == expFp do
          errs := errs.push s!"{cert}: STATEMENT fingerprint {ci.type.hash} ≠ committed {expFp} (statement changed?)"
    | some (.axiomInfo _)  => errs := errs.push s!"{cert}: is an AXIOM, not a proven theorem"
    | some (.opaqueInfo _) => errs := errs.push s!"{cert}: is OPAQUE, not a proven theorem"
    | some _               => errs := errs.push s!"{cert}: not a theorem"

  -- (2) ENUMERATION over EVERY declaration kind — not just theorems (a
  --     `def : False` passed the round-4 gate) — in the eight certificate
  --     modules, AND over this file's own declarations (module index is `none`
  --     during its own elaboration), so the auditor is not exempt (round-5 R1).
  let manifestNames := manifest.map (·.1)
  let mut nEnum := 0
  let mut certsSeen : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    let scope : Option String :=
      match env.getModuleIdxFor? nm with
      | some idx =>
          let m := env.header.moduleNames[idx.toNat]!
          if certModules.contains m then some (toString m) else none
      | none => if nm.isInternal then none else some "Proofs.Audit (this file)"
    match scope with
    | none => pure ()
    | some where_ =>
      nEnum := nEnum + 1
      if manifestNames.contains nm then certsSeen := certsSeen.push nm
      match ci with
      | .axiomInfo _ =>
          -- the five oracle axioms live in gen/ (Phase-0 pinned); an axiom
          -- DECLARED inside an audited module is never acceptable.
          errs := errs.push s!"AXIOM DECLARED in audited scope: {nm} ({where_})"
      | _ =>
          let cone := (← collectAxioms nm).toList
          let bad := cone.filter (fun a => !allowedBoundary.contains a)
          unless bad.isEmpty do
            errs := errs.push s!"UN-AUDITED declaration {nm} ({where_}) has disallowed axioms {bad}"
  for cert in manifestNames do
    unless certsSeen.contains cert do
      errs := errs.push s!"manifest cert {cert} not found in any certificate module"

  unless errs.isEmpty do
    throwError "AUDIT FAILED (fail-closed):\n{String.intercalate "\n" errs.toList}"

  -- (3) CANONICAL BLOCK: policy + statements + specification bodies. check.sh
  --     binds to the SHA-256 of everything between the markers.
  let mut lines : Array String := #[]
  lines := lines.push
    s!"policy|allowedBoundary={String.intercalate "," ((sortNames allowedBoundary).map toString)}|certModules={String.intercalate "," ((sortNames certModules).map toString)}"
  let mut specs : NameSet := {}
  for (cert, cone, _) in manifest do
    let ci := (env.find? cert).get!
    specs := (closureOf env {} ci.type.getUsedConstants.toList).toList.foldl (·.insert ·) specs
    lines := lines.push
      s!"cert|{cert}|cone={String.intercalate "," ((sortNames cone).map toString)}|type={← ppAll ci.type}"
  for nm in sortNames specs.toList do
    match env.find? nm with
    | none => errs := errs.push s!"specification constant vanished: {nm}"
    | some ci =>
      let isProp ← Command.liftCoreM <| Meta.MetaM.run' <| Meta.isProp ci.type
      -- proof irrelevance: a Prop-valued constant contributes its STATEMENT;
      -- a data definition contributes its BODY — that is where fidelity lives.
      if isProp then
        lines := lines.push s!"spec|{nm}|prop|type={← ppAll ci.type}"
      else
        match ci with
        | .defnInfo v => lines := lines.push s!"spec|{nm}|def|value={← ppAll v.value}"
        | _           => lines := lines.push s!"spec|{nm}|other|type={← ppAll ci.type}"
  unless errs.isEmpty do
    throwError "AUDIT FAILED (fail-closed):\n{String.intercalate "\n" errs.toList}"

  logInfo ("AUDIT-MANIFEST-BEGIN\n" ++ String.intercalate "\n" lines.toList ++ "\nAUDIT-MANIFEST-END")
  -- check.sh prints the certificate list it gets from HERE, not from a hand-kept
  -- bash array (drill finding: the one authoritative claim string was the one
  -- thing nothing bound — adding a name to it printed a cert that never existed).
  logInfo s!"CERTIFICATES: {String.intercalate " " (manifestNames.map toString)}"
  logInfo s!"exact-cone audit PASSED: {manifest.length} certificates (cones + statements), {specs.toList.length} specification constants pinned, {nEnum} declarations enumerated clean"

end SlhVerify.Audit

open SlhVerify.Audit in
auditCones
