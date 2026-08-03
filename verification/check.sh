#!/usr/bin/env bash
# The one-button claim for this repository (rigor invariant R3).
# Green output == the full claim. This script is the ONLY source of the
# word "proven" for this repo.
#
#   Phase 0 — build hygiene + integrity: purge stale .olean (the verdict must
#             depend on committed bytes, not untracked build state), forbid any
#             .lean outside gen/ and Proofs/, and sha256-pin the four model files
#             AND the compiler harness `lean-guard` to PROVENANCE.json.
#   Phase 0d— template/model correspondence: every external Aeneas states the
#             extracted Rust needs (FunsExternal_Template.lean, committed and
#             pinned) must be answered by the hand-written model or by a real
#             definition in the corpus. An EXTRA AXIOM in the model — an
#             assumption no template asks for — is a failure, not a silent row.
#   Phase 1 — compile the extracted Lean model (gen/SlhVerify).
#   Phase 2 — compile the proof files (Proofs/).
#   Phase 3 — the in-Lean audit (Proofs/Audit.lean): per certificate, the cone
#             (via `collectAxioms`) must EQUAL its expected set exactly; EVERY
#             declaration kind in the eight cert modules and in Audit.lean itself
#             must stay within the axiom boundary; and this script binds to the
#             SHA-256 of the canonical AUDIT-MANIFEST block, which covers the
#             POLICY constants, every certificate STATEMENT, and every reachable
#             SPECIFICATION DEFINITION BODY. Any mismatch → non-zero exit →
#             fail-closed. No text parsing of axiom cones.
#   Phase 3b— kernel-side axiom-declaration gate: reads the compiled OBJECT
#             FILES (`readModuleData`) rather than the elaboration-time
#             environment, and rejects any axiom declared under Proofs/. This is
#             a SECOND, independently implemented gate on the same property,
#             because Phase 3's view has a demonstrated blind spot: a
#             declaration made after the command that performs the walk is in
#             the object file but not in the environment while the walk runs.
#             It runs after Phase 3 because Proofs/Audit.lean is compiled there.
#   Phase 3c— declaration coverage + the accounting identity: both walks diffed
#             against committed allowlists in BOTH directions, and every
#             constant the kernel holds must be accounted for by one of them.
#             Set containment, never arithmetic.
#
#   What this button does NOT bind is stated in TRUSTED-BASE.md item 11: this
#   script itself, the toolchain env, $AENEAS_HOME, and the Lean toolchain.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
source ~/aeneas-toolchain/env.sh
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-400}"
MEM="${LEAN_MEM_MB:-4096}"

GEN_MODULES=(
  "SlhVerify/TypesExternal"
  "SlhVerify/Types"
  "SlhVerify/FunsExternal"
  "SlhVerify/Funs"
)
# Proof files, in dependency order.
PROOFS=(
  "ChainSpec"
  "WotsSpec"
  "XmssSpec"
  "HtSpec"
  "ForsInnerSpec"
  "ForsOuterSpec"
  "InputPrepSpec"
  "ApexSpec"
)
echo "fips205-slhdsa-verified — check"
echo "==============================="

# ── Phase 0: build hygiene + model & harness integrity ───────────────────────
echo "=== Phase 0: build hygiene + model/harness integrity ==="
# (a) Purge EVERY .olean under verification/ — round-6 NEW-8: the round-5 purge
#     covered only gen/ and Proofs/ while the stray check greped only *.lean, so
#     an ORPHAN `verification/Evil.olean` WITH NO SOURCE AT ALL fell between them,
#     satisfied an `import Evil`, and went ALL GREEN with the digest untouched
#     (*.olean is .gitignored, so `git status` showed only the import line).
#     The verdict must depend on COMMITTED BYTES, never on untracked build state.
find "$HERE" -name '*.olean' -delete 2>/dev/null || true
#     Aeneas also emits `*_Template.lean` into gen/ on every extraction. This
#     script used to DELETE it, reasoning that an untracked file sitting on
#     LEAN_PATH is exactly the unpinned-state problem described above. The
#     reasoning was right; the remedy was the weaker of the two available. The
#     ed25519 forks face the identical choice and COMMIT AND PIN their
#     templates, which removes the untracked state just as completely and keeps
#     the evidence.
#
#     The evidence matters. The template is Aeneas's own statement of what the
#     extracted Rust needs from outside, and it is the ONLY artifact against
#     which "does the hand-written model ANSWER the extraction?" can be asked.
#     Deleting it made that question unaskable, which is why this repository
#     shipped a Template/model pair with no correspondence check at all —
#     round-8 estate review (GPT-5.6). It is now committed, pinned in
#     model_integrity_sha256 like every other model file, and consumed by
#     Phase 0d below.
#
#     It still never joins the environment: Phase 1 compiles the named model
#     modules, not a glob, and nothing imports the template.
# (b) No Lean source OR compiled module may sit outside gen/ and Proofs/;
#     LEAN_PATH includes $PWD, so either can join the environment ungated.
STRAY=$(find "$HERE" -maxdepth 1 \( -name '*.lean' -o -name '*.olean' \) -printf '%f\n' 2>/dev/null || true)
if [ -n "$STRAY" ]; then
  echo "$STRAY" | sed 's/^/  ✗ stray Lean file outside gen\/ and Proofs\/: /'
  echo "BUILD HYGIENE FAILED (a .lean/.olean outside the audited directories can join LEAN_PATH)"; exit 1
fi
# (c) sha256-pin the extracted model AND the compiler harness. lean-guard is
#     repo-tracked and is shelled out to for every compile, so it is part of the
#     trusted computing base: round 5 demonstrated that stubbing it alone yields
#     ALL GREEN in 3.6s over destroyed proofs. It is KEPT (it is the memory cap
#     that protects this machine after the 12.2GB OOM incident) and pinned.
python3 - "$HERE/PROVENANCE.json" "$HERE" <<'PY' || { echo "INTEGRITY FAILED (a pinned file differs from PROVENANCE.json, or a required file is unpinned — see the specific line above)"; exit 1; }
import json, sys, hashlib, os
prov = json.load(open(sys.argv[1])); here = sys.argv[2]
files = {k: v for k, v in prov.get("model_integrity_sha256", {}).items() if not k.startswith("_")}
files.update({k: v for k, v in prov.get("harness_integrity_sha256", {}).items() if not k.startswith("_")})
if not files:
    print("  no integrity map in PROVENANCE.json (fail-closed)"); sys.exit(1)
bad = 0
# WHICH files must be pinned is policy, and policy belongs in the root of trust —
# not in the map being consulted. Round-6 review (NEW-13) demonstrated the gap:
# PROVENANCE.json is a tracked file that nothing pins, and the only completeness
# test was `if not files`, so deleting the whole `harness_integrity_sha256` key
# silently un-pinned BOTH lean-guard and Proofs/Audit.lean with no diagnostic —
# after which the round-6 NEW-7 logic mutation ran to ALL GREEN over a repository
# proving False, digest byte-identical. The model side self-protected only
# because the gen/ set assertion below derives its requirement from the
# filesystem; the harness side had no such cross-check.
# SELF-DERIVING, so a NEW harness file cannot be forgotten. Round-8 review
# observed that a hardcoded list is itself a second thing to keep in sync, and
# supplied the natural boundary the harness does have: THE EXECUTABLE BIT. Every
# executable file in verification/ is something this script can shell out to, so
# every one must be pinned; a new script therefore fails closed until it is.
# check.sh is excluded because it cannot pin itself — it is the root of trust,
# and TRUSTED-BASE.md item 11 says so. Proofs/Audit.lean is added explicitly: it
# is not executable but it computes the digest it is judged by.
# Backup files are excluded by extension only because check-selftest.sh keeps its
# backups OUTSIDE this directory now; nothing here is expected to match.
harness = {
    f for f in os.listdir(here)
    if os.path.isfile(os.path.join(here, f))
    and os.access(os.path.join(here, f), os.X_OK)
    and f != "check.sh"
}
harness.add("Proofs/Audit.lean")
missing = harness - set(files)
if missing:
    for m in sorted(missing):
        print(f"  ✗ UNPINNED harness file (executable, or the audit driver): {m}")
    bad = 1
for rel, want in sorted(files.items()):
    p = os.path.join(here, rel)
    if not os.path.exists(p):
        print(f"  ✗ {rel} MISSING"); bad = 1; continue
    got = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    if got != want:
        print(f"  ✗ {rel}: sha256 {got[:12]} ≠ pinned {want[:12]}"); bad = 1
    else:
        print(f"  ✓ {rel}")
# Round-6 NEW-9: pin gen/ as a SET, not as four names. A new file under gen/ was
# neither hashed nor forbidden, while LEAN_PATH contains $PWD/gen — so the
# closure's premise ("everything outside certModules is pinned or disclosed")
# was not enforced. Any .lean under gen/ must appear in the pin map.
pinned_gen = {k for k in files if k.startswith("gen/")}
actual_gen = set()
for root, _, names in os.walk(os.path.join(here, "gen")):
    for n in names:
        if n.endswith(".lean"):
            actual_gen.add(os.path.relpath(os.path.join(root, n), here))
for extra in sorted(actual_gen - pinned_gen):
    print(f"  ✗ UNPINNED model file under gen/: {extra}"); bad = 1
for missing in sorted(pinned_gen - actual_gen):
    print(f"  ✗ pinned model file absent: {missing}"); bad = 1
sys.exit(1 if bad else 0)
PY

# ── Phase 1: model ──────────────────────────────────────────────────────────
# ── Phase 0d: template/model correspondence ─────────────────────────────────
# WHAT THE BYTE PINS DO NOT ESTABLISH. Phase 0 pins the model files byte for
# byte, so they cannot drift unnoticed. It says nothing about whether the model
# ANSWERS the extraction: Aeneas states, in FunsExternal_Template.lean, exactly
# what the extracted Rust needs from outside, and each such name must be
# provided by the hand-written sibling FunsExternal.lean or by a real definition
# in the proven corpus. A name the extraction asks for and nothing supplies is
# drift the byte pins cannot see, because both files are individually pinned and
# individually unchanged.
#
# This repository had a Template/model pair and NO correspondence check at all
# — round-8 estate review (GPT-5.6). The scanner is the one the ed25519 forks
# use, including its two round-8 corrections: a named Lean `section` does NOT
# qualify declaration names (treating it as a namespace made the scanner invent
# `Foo.bar`, and a semantic phase then certified an unrelated `Foo.bar` while
# the real external went unqueried), and an EXTRA AXIOM in the model — an
# assumption no template asks for — is a failure rather than a silent row.
echo "=== Phase 0d: template/model correspondence ==="
CORR=$(python3 "$HERE/model-correspondence.py" "$HERE") || {
  echo "MODEL CORRESPONDENCE FAILED — the extraction asks for something this"
  echo "repository does not supply, or the model declares an axiom nothing asks for."
  printf '%s\n' "$CORR" | grep -E 'UNRESOLVED|EXTRA-AXIOM' | sed 's/^/    /'
  exit 1
}
if ! printf '%s\n' "$CORR" | cmp -s - "$HERE/MODEL-CORRESPONDENCE.txt"; then
  echo "MODEL CORRESPONDENCE FAILED — the committed table is not what the"
  echo "scanner now produces. Differences:"
  diff <(printf '%s\n' "$CORR") "$HERE/MODEL-CORRESPONDENCE.txt" | head -20 | sed 's/^/    /'
  exit 1
fi
echo "  $(grep -c '|MODEL$\||PROVEN$' "$HERE/MODEL-CORRESPONDENCE.txt") externals, every one answered by the pinned model"

echo "=== Phase 1: compile the extracted model ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -euo pipefail
  cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\"
  compile() { echo \"  · \$1\"; LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' \"\${1}.lean\" >/dev/null || { echo \"FAIL: \$1\"; exit 1; }; }
  for m in ${GEN_MODULES[*]}; do compile \"gen/\$m\"; done
"

# ── Phase 2: proofs ─────────────────────────────────────────────────────────
echo "=== Phase 2: compile the proofs ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -euo pipefail
  cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\"
  compile() { echo \"  · \$1\"; LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' \"Proofs/\${1}.lean\" >/dev/null || { echo \"FAIL: Proofs/\$1\"; exit 1; }; }
  for m in ${PROOFS[*]}; do compile \"\$m\"; done
  # no dead proof files: everything under Proofs/ must be in the manifest
  # (PROOFS) or be the audit driver (Audit, compiled in Phase 3).
  for f in Proofs/*.lean; do b=\$(basename \"\$f\" .lean)
    case \" ${PROOFS[*]} Audit \" in *\" \$b \"*) ;; *) echo \"DEAD FILE: Proofs/\$b.lean not in manifest\"; exit 1 ;; esac
  done
"

# ── Phase 3: in-Lean audit (cones + statements + full-module enumeration) ────
echo "=== Phase 3: in-Lean audit (cones + statement fingerprints + enumeration) ==="
cd "$AENEAS_LEAN"
# THE BINDING DIGEST. Audit.lean emits a canonical AUDIT-MANIFEST block holding
# the POLICY constants (allowedBoundary, certModules — round-5 NEW-1), every
# certificate's fully-elaborated STATEMENT, and every reachable SPECIFICATION
# definition's fully-elaborated BODY (round-5 NEW-2: redefining a reference fold
# to *be* the extracted loop previously left every fingerprint intact). We bind
# to the SHA-256 of that block, retiring the 32-bit Expr.hash as the load-bearing
# digest (NEW-5). To rotate deliberately: run check.sh, take the printed OBSERVED
# digest, and update this constant in the same reviewable commit.
EXPECTED_AUDIT_SHA256="d83e297a49094c970b88ce7c63ceb85d6bee0764d4623456a7225860e2298afa"
AUD_OUT=$(lake env bash -c "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' 'Proofs/Audit.lean'" 2>&1) || {
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (Audit.lean did not compile — cone/statement mismatch, missing cert, sham, or un-audited declaration)"; exit 1; }
if ! grep -qF "exact-cone audit PASSED" <<<"$AUD_OUT"; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (no PASSED line — fail-closed)"; exit 1
fi
BLOCK=$(awk '/AUDIT-MANIFEST-BEGIN/{f=1;next} /AUDIT-MANIFEST-END/{f=0} f' <<<"$AUD_OUT")
if [ -z "$BLOCK" ]; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (no AUDIT-MANIFEST block — fail-closed)"; exit 1
fi
GOT_SHA=$(printf '%s\n' "$BLOCK" | sha256sum | cut -d' ' -f1)
if [ "$GOT_SHA" != "$EXPECTED_AUDIT_SHA256" ]; then
  printf '%s\n' "$BLOCK" > "$HERE/.audit-manifest.observed"
  echo "AUDIT FAILED — audit-manifest digest mismatch."
  echo "  expected: $EXPECTED_AUDIT_SHA256"
  echo "  observed: $GOT_SHA"
  echo "  A policy constant, a certificate statement, or a specification"
  echo "  definition changed without a reviewed rotation."
  echo "  What moved (committed block vs observed):"
  diff -u "$HERE/AUDIT-MANIFEST.txt" "$HERE/.audit-manifest.observed" 2>/dev/null \
    | head -40 | sed 's/^/    /' || echo "    (AUDIT-MANIFEST.txt absent — cannot diff)"
  exit 1
fi
# The digest's INPUT is committed too (round-6: a mismatch previously wrote an
# observed block with nothing to diff it against). Guard against the committed
# copy drifting from what Lean actually emits.
if ! printf '%s\n' "$BLOCK" | cmp -s - "$HERE/AUDIT-MANIFEST.txt"; then
  echo "AUDIT FAILED — the committed AUDIT-MANIFEST.txt does not match the emitted block"
  echo "  (digest matched, so this means the committed copy is stale — refresh it)"; exit 1
fi
echo "  ✓ $(grep -oF 'exact-cone audit PASSED' <<<"$AUD_OUT" | head -1)"
echo "  ✓ audit-manifest digest matches (sha256 ${EXPECTED_AUDIT_SHA256:0:16}…)"



# ── Phase 3b: kernel-side axiom-declaration gate ────────────────────────────
# WHY A SECOND GATE ON THE SAME PROPERTY. Phase 3's audit runs INSIDE Lean and
# reads `env.constants` after the imports — an ELABORATION-TIME view. That view
# has a documented blind spot, demonstrated on the accumulator during round-7
# review and reproduced there: anything declared AFTER the command that performs
# the walk exists in the compiled object file but is not in the environment
# while the walk runs. The walker reports "no axiom, no claim" and is telling
# the truth about what it could see.
#
# This phase reads the OBJECT FILES instead, via `readModuleData`, which is a
# different view of the same modules and has no such ordering. It is deliberately
# a second, independently-implemented gate on the property that matters most:
# that nothing in the proof corpus DECLARES AN AXIOM, whatever its indentation,
# attributes, or position in the file.
#
# Membership, not a glob: the manifest below is this script's PROOFS array plus
# the audit driver, so a module the button never compiled cannot be silently
# demanded, and a module it did compile cannot be silently skipped.
#
# IT RUNS AFTER PHASE 3, and that placement is load-bearing rather than
# cosmetic. Phase 2 compiles the eight certificate modules; Proofs/Audit.lean is
# only compiled by Phase 3. Placed at 2b the gate demanded an artifact that did
# not exist yet and died with COVERAGE — correctly, since a gate that skipped
# the missing module would have been vacuous exactly where it matters. The
# audit driver is the one module whose own declarations no other gate examines,
# so covering it is the point, and covering it requires waiting for it.
echo "=== Phase 3b: kernel-side axiom-declaration gate ==="
KERN_MODS=$(printf '"%s.olean", ' "${PROOFS[@]}" "Audit" | sed 's/, $//')
GATE=$(mktemp "$HERE/.axgate-XXXX.lean")
{
  echo "import Lean"
  echo "open Lean"
  echo "def expected : List String := [$KERN_MODS]"
  cat <<'LEANGATE'

run_cmd do
  let dir : System.FilePath := "Proofs"
  let mut errs : Array String := #[]
  let mut nMod := 0
  let mut nConst := 0
  for name in expected do
    let p := dir / name
    -- FAIL CLOSED ON ABSENCE: a manifest module whose artifact is missing makes
    -- this gate vacuous for that module. An error, never a skip.
    unless (← p.pathExists) do
      throwError "COVERAGE: {name} is in the compile manifest but its artifact is absent"
    nMod := nMod + 1
    let (mod, _) ← readModuleData p
    for ci in mod.constants do
      nConst := nConst + 1
      -- The kernel's OWN list of names, for the accounting identity in check.sh:
      -- every constant the kernel holds must be accounted for by one of the two
      -- environment walks. Emitted rather than counted, because a count cannot
      -- say WHICH constant is unaccounted for — the residual would then have to
      -- be "explained", which is how a fudge term gets born.
      IO.println s!"KERNEL-NAME|{ci.name}"
      if ci matches .axiomInfo _ then
        errs := errs.push s!"  {name}: {ci.name}"
  unless errs.isEmpty do
    throwError "AXIOM DECLARED under Proofs/ (kernel-side gate):\n{String.intercalate "\n" errs.toList}"
  -- FAIL CLOSED ON EMPTINESS: an empty scan and a clean scan must not share a
  -- code path, or a gate that read nothing would report the same as one that
  -- read everything and found nothing wrong.
  if nConst == 0 then
    throwError "KERNEL GATE VACUOUS: read {nMod} module(s) and saw no declarations at all"
  logInfo s!"  kernel confirms: {nConst} declarations across {nMod} compiled modules, none is an axiom"
LEANGATE
} > "$GATE"
GATE_RC=0
# The temp source AND its artifact are removed on BOTH paths: under `set -e` a
# bare rm after the call never runs when the gate goes red, which is how the
# ed25519 repos once accumulated 101 orphan .olean files.
GATELOG=$(mktemp /tmp/slh-kernlog-XXXX.log)
( cd "$AENEAS_LEAN" && lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  cd '$HERE'
  LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' '$GATE'
" ) 2>&1 | tee "$GATELOG" || GATE_RC=${PIPESTATUS[0]}
rm -f "$GATE" "${GATE%.lean}.olean"
if [ "$GATE_RC" -ne 0 ]; then
  echo "AXIOM SMUGGLING GATE FAILED (kernel-side) — see the error above."
  exit 1
fi

# ── Phase 3c: declaration coverage, both walks, both directions ─────────────
# Phase 3 proves each certificate's cone is exact and that no declaration in
# scope carries a disallowed axiom. It does NOT pin WHICH declarations exist:
# a new one that happens to be clean, or a silently vanished one, both pass it.
# These two gates diff the walks against committed allowlists in both
# directions — UNCLASSIFIED for something in the environment and not the list,
# STALE for the reverse — using the same implementation the ed25519 repositories
# use for their corpus, with a tag for each surface.
AUDROWS=$(mktemp /tmp/slh-audrows-XXXX.log)
printf '%s\n' "$AUD_OUT" > "$AUDROWS"
COVFAIL=0
"$HERE/inventory_gate.sh" "$AUDROWS" "$HERE/inventory-allowlist.txt" INV || COVFAIL=1
"$HERE/inventory_gate.sh" "$AUDROWS" "$HERE/driver-allowlist.txt"    DRV || COVFAIL=1

# ── THE ACCOUNTING IDENTITY ─────────────────────────────────────────────────
# Round-8 review (Claude, `accounting-certifies-enumeration`). The two walks
# above are ENVIRONMENT views, taken while Audit.lean elaborates. Phase 3b reads
# the OBJECT FILES. Every constant the kernel holds must be accounted for by one
# of the two walks — otherwise a declaration exists that the button compiled,
# the kernel sees, and no allowlist describes.
#
# SET CONTAINMENT, never arithmetic. An earlier version of this identity in the
# ed25519 repositories carried a "+ N_DRIVERS" correction term fitted from one
# repository; four-fork data refuted it (the residual was 2 regardless of driver
# count). A residual that has to be explained is a fudge term waiting to absorb
# the next real finding, so this compares NAMES and prints the ones missing.
KERN=$(mktemp /tmp/slh-kern-XXXX.txt); ACCT=$(mktemp /tmp/slh-acct-XXXX.txt)
LC_ALL=C grep '^KERNEL-NAME|' "$GATELOG" | cut -d'|' -f2 | LC_ALL=C sort -u > "$KERN"
{ LC_ALL=C awk -F'|' '/^INV\|/{print $3}' "$HERE/inventory-allowlist.txt"
  LC_ALL=C awk -F'|' '/^DRV\|/{print $3}' "$HERE/driver-allowlist.txt"
} | LC_ALL=C sort -u > "$ACCT"
UNACCOUNTED=$(LC_ALL=C comm -23 "$KERN" "$ACCT")
if [ ! -s "$KERN" ]; then
  echo "  ACCOUNTING FAILED: the kernel gate reported no names — the scan was vacuous"
  COVFAIL=1
elif [ -n "$UNACCOUNTED" ]; then
  echo "  ACCOUNTING FAILED: the kernel holds constants that neither walk accounts for:"
  printf '%s\n' "$UNACCOUNTED" | head -20 | sed 's/^/    /'
  COVFAIL=1
else
  echo "  accounting: every one of $(wc -l < "$KERN") kernel constants is covered by the corpus inventory or the instrument surface"
fi
rm -f "$AUDROWS" "$KERN" "$ACCT"
[ "$COVFAIL" = 0 ] || { echo "COVERAGE FAILED"; exit 1; }
rm -f "$GATELOG"


echo
echo "ALL GREEN — model compiles, proofs compile, and every certificate cone"
echo "equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles."
# The list comes from the AUDITED manifest itself, never from a hand-kept array:
# a display list nothing binds can name a certificate that does not exist.
CERT_LINE=$(sed -n 's/.*CERTIFICATES: //p' <<<"$AUD_OUT" | head -1)
[ -n "$CERT_LINE" ] || { echo "AUDIT FAILED (no CERTIFICATES line — fail-closed)"; exit 1; }
echo "Certificates proven: $CERT_LINE"
