#!/usr/bin/env bash
# Adversarial self-test of the check.sh gates (the R3-5 tradition: an audit that
# cannot fail is theater). Every attack MUST make check.sh fail, via the gate it
# targets — each assertion names a SPECIFIC diagnostic, so a rejection for an
# unrelated reason fails the test too.
#
# Attacks 1-8 are the round-3/4 set. Attacks 9-14 were authored by external
# reviewers and an independent drill, each having DEMONSTRATED the corresponding
# fail-open against an earlier gate — they are the reason this round exists:
#
#   9  widen `allowedBoundary` by one name + a False-proof   (round-5 NEW-1:
#      previously ALL GREEN with the fingerprint BYTE-IDENTICAL)
#  10  redefine a reference fold to BE the extracted loop    (round-5 NEW-2:
#      previously ALL GREEN — the certificate degenerates to `loop = loop`)
#  11  `def : False` instead of `theorem : False`            (drill: the round-4
#      enumeration matched `.thmInfo` only, so this passed)
#  12  a False-proof inside Audit.lean itself                (round-5 R1: the
#      auditor was exempt from its own enumeration)
#  13  stub `lean-guard`                                     (round-5 NEW-3:
#      previously ALL GREEN in 3.6s over destroyed proofs)
#  14  a stray .lean beside check.sh                         (round-5 NEW-4:
#      LEAN_PATH includes $PWD, so it can join the environment ungated)
#  16  an ORPHAN .olean whose source was deleted             (round-6 NEW-8:
#      fell between the purge and the stray check; ALL GREEN, digest identical)
#  17  the audit's fail-closed guards switched off           (round-6 NEW-7:
#      the digest binds the audit's DATA, never its LOGIC; two characters in
#      Audit.lean defeated every gate with the digest BYTE-IDENTICAL)
#  18  the pin map shortened by one JSON key                 (round-7 NEW-13:
#      deleting harness_integrity_sha256 silently un-pinned BOTH lean-guard and
#      Audit.lean with no diagnostic, re-opening 17 with the digest identical)
#
# Self-cleaning: every mutated file is backed up and restored, and an EXIT trap
# restores even on failure. Run from a clean tree.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"
source ~/aeneas-toolchain/env.sh

BAKS=()
save()    { cp -p "$1" "$1.sfbak"; BAKS+=("$1"); }
restore() { for f in "${BAKS[@]:-}"; do [ -f "$f.sfbak" ] && mv -f "$f.sfbak" "$f"; done; BAKS=(); }
# Proofs/Audit.lean is sha256-pinned by Phase 0 since round 6 (NEW-7). An attack
# that mutates the audit's DATA must therefore ALSO rotate that pin, otherwise it
# is stopped by the byte pin and never reaches the mechanism it means to test —
# the "rejected for an unrelated reason" defect class. `repin_audit` simulates an
# author who edits and dutifully re-pins; the digest/enumeration must still bite.
# Attack 17 deliberately does NOT re-pin: it is the test of the pin itself.
repin_audit() {
  python3 - <<'PY'
import json, hashlib
p = "PROVENANCE.json"; d = json.load(open(p))
d["harness_integrity_sha256"]["Proofs/Audit.lean"] = hashlib.sha256(
    open("Proofs/Audit.lean","rb").read()).hexdigest()
json.dump(d, open(p,"w"), indent=2); open(p,"a").write("\n")
PY
}
cleanup() {
  restore
  rm -f Proofs/Stray.lean Proofs/EvilSpec.lean Evil.lean Evil.olean \
        Proofs/*.olean gen/SlhVerify/*.olean *.olean .audit-manifest.observed 2>/dev/null
  return 0
}
trap cleanup EXIT

fail() { echo "✗ $1"; shift; [ $# -gt 0 ] && sed 's/^/    /' "$1"; exit 1; }

echo "check-selftest: attacking the gates"
echo "===================================="

# ── 1: dead file ────────────────────────────────────────────────────────────
echo "-- stray" > Proofs/Stray.lean
./check.sh > /tmp/sf1.out 2>&1 && fail "ATTACK 1 SUCCEEDED (dead file stayed green)" /tmp/sf1.out
grep -q "DEAD FILE" /tmp/sf1.out || fail "ATTACK 1: failed, not via the dead-file gate" /tmp/sf1.out
rm -f Proofs/Stray.lean
echo "✓ attack 1 rejected (dead-file gate)"

# ── 2: smuggled disallowed axiom in a real cone ─────────────────────────────
save check.sh; save Proofs/Audit.lean; save PROVENANCE.json
# NB: no imports — Phase 0 now purges every .olean, so a module injected at the
# head of the build order cannot import one that has not been compiled yet.
cat > Proofs/EvilSpec.lean <<'EOF'
axiom evil_ax : True
theorem evil_thm : True := evil_ax
EOF
python3 - <<'PY'
s = open("check.sh").read()
assert 'PROOFS=(\n' in s, "check.sh PROOFS shape changed"
open("check.sh","w").write(s.replace('PROOFS=(\n', 'PROOFS=(\n  "EvilSpec"\n', 1))
a = open("Proofs/Audit.lean").read()
assert 'import Proofs.ApexSpec' in a and '  [ (`fips205.chain_free_loop_eq' in a, "Audit.lean shape changed"
a = a.replace('import Proofs.ApexSpec', 'import Proofs.ApexSpec\nimport Proofs.EvilSpec', 1)
a = a.replace('  [ (`fips205.chain_free_loop_eq', '  [ (`evil_thm, kernel3, 0),\n    (`fips205.chain_free_loop_eq', 1)
open("Proofs/Audit.lean","w").write(a)
PY
repin_audit
./check.sh > /tmp/sf2.out 2>&1 && fail "ATTACK 2 SUCCEEDED (smuggled axiom)" /tmp/sf2.out
grep -q "evil_ax" /tmp/sf2.out || fail "ATTACK 2: rejected but evil_ax not named" /tmp/sf2.out
restore; rm -f Proofs/EvilSpec.lean
echo "✓ attack 2 rejected (extra-axiom detection — evil_ax named)"

# ── 3: dropped oracle (a subset check would pass; exact must not) ────────────
save Proofs/Audit.lean; save PROVENANCE.json
python3 - <<'PY'
import re
a = open("Proofs/Audit.lean").read()
new, n = re.subn(r'(`fips205\.to_int_loop_eq,\s*)kernel3,', r'\1kernel3 ++ [oracleF],', a)
assert n == 1, f"expected 1 to_int row, patched {n}"
open("Proofs/Audit.lean","w").write(new)
PY
repin_audit
./check.sh > /tmp/sf3.out 2>&1 && fail "ATTACK 3 SUCCEEDED (dropped oracle — subset hole)" /tmp/sf3.out
grep -q "missing=\[verify_mono.oracle.f\]" /tmp/sf3.out || fail "ATTACK 3: rejected but missing oracle not named" /tmp/sf3.out
restore
echo "✓ attack 3 rejected (missing-oracle detection — exact cone, not subset)"

# ── 4: vanished certificate ─────────────────────────────────────────────────
save Proofs/Audit.lean; save PROVENANCE.json
python3 - <<'PY'
a = open("Proofs/Audit.lean").read()
assert a.count('`fips205.chain_free_loop_eq,') >= 1
open("Proofs/Audit.lean","w").write(a.replace('`fips205.chain_free_loop_eq,', '`fips205.chain_free_loop_eq_VANISHED,', 1))
PY
repin_audit
./check.sh > /tmp/sf4.out 2>&1 && fail "ATTACK 4 SUCCEEDED (vanished cert)" /tmp/sf4.out
grep -q "NOT FOUND" /tmp/sf4.out || fail "ATTACK 4: rejected but not via the existence check" /tmp/sf4.out
restore
echo "✓ attack 4 rejected (existence check — a vanished cert cannot pass as 0-axiom)"

# ── 5: un-manifested THEOREM proving False (round-4 F1) ─────────────────────
save Proofs/ChainSpec.lean
printf '\n-- SELFTEST ATTACK 5\naxiom cheat5 : ∀ (P : Prop), P\ntheorem repo_proves_false : False := cheat5 _\n' >> Proofs/ChainSpec.lean
./check.sh > /tmp/sf5.out 2>&1 && fail "ATTACK 5 SUCCEEDED: check.sh GREEN over a repo proving False!" /tmp/sf5.out
grep -qE "repo_proves_false|AXIOM DECLARED" /tmp/sf5.out || fail "ATTACK 5: rejected but not via the enumeration" /tmp/sf5.out
restore
echo "✓ attack 5 rejected (enumeration — an un-manifested False theorem cannot pass)"

# ── 6: gutted STATEMENT, cone preserved (round-4 F2) ────────────────────────
save Proofs/InputPrepSpec.lean
python3 - <<'PY'
s = open("Proofs/InputPrepSpec.lean").read()
i = s.index("theorem to_byte_loop_eq (n : Std.U32) (k : Nat) :")   # a LEAF cert
j = s.index("theorem hbody_cs", i)                                  # next declaration
open("Proofs/InputPrepSpec.lean","w").write(
    s[:i] + "theorem to_byte_loop_eq : (∀ p : Prop, p ∨ ¬p) := Classical.em\n\n" + s[j:])
PY
./check.sh > /tmp/sf6.out 2>&1 && fail "ATTACK 6 SUCCEEDED (gutted statement, cone preserved)" /tmp/sf6.out
grep -q "STATEMENT fingerprint" /tmp/sf6.out || fail "ATTACK 6: rejected but not via the statement check" /tmp/sf6.out
restore
echo "✓ attack 6 rejected (statement check — a gutted statement of the same cone cannot pass)"

# ── 7: hand-edited model file (round-4 F3) ──────────────────────────────────
save gen/SlhVerify/Funs.lean
printf '\n-- SELFTEST ATTACK 7\n' >> gen/SlhVerify/Funs.lean
./check.sh > /tmp/sf7.out 2>&1 && fail "ATTACK 7 SUCCEEDED (hand-edited model passed)" /tmp/sf7.out
grep -q "INTEGRITY FAILED" /tmp/sf7.out || fail "ATTACK 7: rejected but not via Phase 0" /tmp/sf7.out
restore
echo "✓ attack 7 rejected (Phase 0 model-byte integrity)"

# ── 8: deleted manifest row (round-4 F1, set half) ──────────────────────────
save Proofs/Audit.lean; save PROVENANCE.json
python3 - <<'PY'
import re
a = open("Proofs/Audit.lean").read()
new, n = re.subn(r'\n\s*\(`fips205\.to_int_loop_eq,.*?\),', '', a)
assert n == 1, f"expected 1 row, removed {n}"
open("Proofs/Audit.lean","w").write(new)
PY
repin_audit
./check.sh > /tmp/sf8.out 2>&1 && fail "ATTACK 8 SUCCEEDED (a dropped cert row passed)" /tmp/sf8.out
grep -q "digest mismatch" /tmp/sf8.out || fail "ATTACK 8: rejected but not via the digest binding" /tmp/sf8.out
restore
echo "✓ attack 8 rejected (audit-manifest digest — a silently-dropped cert cannot pass)"

# ── 9: WIDEN THE POLICY (round-5 NEW-1) ─────────────────────────────────────
# Previously ALL GREEN with the committed fingerprint byte-identical: the
# fingerprint covered `manifest` but never `allowedBoundary`, the very predicate
# the enumeration tests against.
# Widen the policy ALONE — no axiom is declared anywhere, so the enumeration
# (which now also rejects a bare `axiom` in an audited module) cannot fire and
# the DIGEST must be what bites. `sorryAx` is used as the smuggled name because
# admitting it would silently legalise every `sorry` in the repository.
save Proofs/Audit.lean; save PROVENANCE.json
python3 - <<'PY'
a = open("Proofs/Audit.lean").read()
old = "  kernel3 ++ [oracleF, oracleH, oracleTL, oracleTLen, oracleHMsg]\n"
assert a.count(old) == 1, "allowedBoundary shape changed"
open("Proofs/Audit.lean","w").write(a.replace(old, old.rstrip("\n") + " ++ [`sorryAx]\n", 1))
PY
repin_audit
./check.sh > /tmp/sf9.out 2>&1 && fail "ATTACK 9 SUCCEEDED: the axiom policy was widened and the button stayed GREEN!" /tmp/sf9.out
grep -q "digest mismatch" /tmp/sf9.out || fail "ATTACK 9: rejected but not via the policy-covering digest" /tmp/sf9.out
restore
echo "✓ attack 9 rejected (digest covers allowedBoundary — the policy cannot be widened silently)"

# ── 10: REDEFINE A SPEC FOLD TO BE THE LOOP (round-5 NEW-2) ─────────────────
# The certificate keeps its exact statement, cone and type-hash, but becomes
# `loop = loop` — vacuous. Previously ALL GREEN.
save Proofs/ChainSpec.lean
python3 - <<'PY'
s = open("Proofs/ChainSpec.lean").read()
i = s.index("noncomputable def chainFoldN")
j = s.index("/-- One full loop step", i)
gut = """noncomputable def chainFoldN {N : Std.Usize} (pk_seed : Slice Std.U8) :
    types.Adrs → Array Std.U8 N → Std.U32 → Nat → Result (Array Std.U8 N) :=
  fun adrs tmp start s =>
    verify_mono.chain_free_loop
      { start := start,
        «end» := Std.U32.ofNatCore ((start.val + s) % 2 ^ 32) (Nat.mod_lt _ (by norm_num)) }
      pk_seed adrs tmp

"""
open("Proofs/ChainSpec.lean","w").write(s[:i] + gut + s[j:])
PY
./check.sh > /tmp/sf10.out 2>&1 && fail "ATTACK 10 SUCCEEDED: the spec fold IS the loop, certificate is vacuous, still GREEN!" /tmp/sf10.out
# Two layers stand here, and either is a valid rejection: the existing proof no
# longer matches the redefined fold (Phase 2), and — if an attacker repairs the
# proof, as the round-5 reviewer did — the digest covers specification BODIES,
# so it moves. Attack 9 is the pure test that the digest binding fires; that the
# digest's input contains the fold bodies is verified directly (see below).
grep -qE "digest mismatch|FAIL: Proofs/ChainSpec" /tmp/sf10.out \
  || fail "ATTACK 10: rejected, but neither via the digest nor a proof break" /tmp/sf10.out
restore
echo "✓ attack 10 rejected (a specification fold cannot be silently redefined to the loop)"

# ── 11: `def : False` rather than `theorem : False` (drill finding) ─────────
save Proofs/WotsSpec.lean
printf '\n-- SELFTEST ATTACK 11\naxiom cheat11 : ∀ (P : Prop), P\ndef attack11_false : False := cheat11 _\n' >> Proofs/WotsSpec.lean
./check.sh > /tmp/sf11.out 2>&1 && fail "ATTACK 11 SUCCEEDED: a def proving False passed!" /tmp/sf11.out
grep -qE "attack11_false|AXIOM DECLARED" /tmp/sf11.out || fail "ATTACK 11: rejected but not via the all-kinds enumeration" /tmp/sf11.out
restore
echo "✓ attack 11 rejected (enumeration covers every declaration kind, not just theorems)"

# ── 12: a False-proof inside the AUDITOR itself (round-5 R1) ────────────────
save Proofs/Audit.lean; save PROVENANCE.json
python3 - <<'PY'
a = open("Proofs/Audit.lean").read()
i = a.index("elab \"auditCones\"")
open("Proofs/Audit.lean","w").write(
    a[:i] + "axiom cheat12 : ∀ (P : Prop), P\ntheorem audit_proves_false : False := cheat12 _\n\n" + a[i:])
PY
repin_audit
./check.sh > /tmp/sf12.out 2>&1 && fail "ATTACK 12 SUCCEEDED: the auditor itself proves False, still GREEN!" /tmp/sf12.out
grep -qE "audit_proves_false|AXIOM DECLARED" /tmp/sf12.out || fail "ATTACK 12: rejected but not via self-enumeration" /tmp/sf12.out
restore
echo "✓ attack 12 rejected (the auditor audits itself — no exemption)"

# ── 13: stub the compiler harness (round-5 NEW-3) ──────────────────────────
# Previously: ALL GREEN in 3.6s with the proofs destroyed. lean-guard is KEPT
# (it is this machine's memory cap) and sha256-pinned instead.
save lean-guard
cat > lean-guard <<'EOF'
#!/usr/bin/env bash
echo "exact-cone audit PASSED"
exit 0
EOF
chmod +x lean-guard
./check.sh > /tmp/sf13.out 2>&1 && fail "ATTACK 13 SUCCEEDED: a stubbed harness passed!" /tmp/sf13.out
grep -q "INTEGRITY FAILED" /tmp/sf13.out || fail "ATTACK 13: rejected but not via the harness pin" /tmp/sf13.out
restore
echo "✓ attack 13 rejected (Phase 0 pins lean-guard — the harness is in the TCB and bound)"

# ── 14: stray .lean beside check.sh (round-5 NEW-4) ────────────────────────
cat > Evil.lean <<'EOF'
axiom cheat14 : ∀ (P : Prop), P
theorem evil14 : False := cheat14 _
EOF
./check.sh > /tmp/sf14.out 2>&1 && fail "ATTACK 14 SUCCEEDED: a stray Lean module passed!" /tmp/sf14.out
grep -q "BUILD HYGIENE FAILED" /tmp/sf14.out || fail "ATTACK 14: rejected but not via the hygiene gate" /tmp/sf14.out
rm -f Evil.lean
echo "✓ attack 14 rejected (no .lean may sit outside gen/ and Proofs/)"

# ── 16: ORPHAN .olean WITH NO SOURCE (round-6 NEW-8) ───────────────────────
# Previously ALL GREEN, digest byte-identical, repo proving False: the round-5
# purge covered gen/ and Proofs/ while the stray check greped only *.lean, so a
# compiled module with its source DELETED fell between the two — and *.olean is
# .gitignored, so `git status` showed only the one-line import.
save Proofs/ChainSpec.lean
cat > Evil.lean <<'EOF'
axiom cheat16 : ∀ (P : Prop), P
theorem attack16_false : False := cheat16 _
EOF
( cd "$AENEAS_HOME/backends/lean" && lake env bash -c \
    "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && lean -o '$HERE/Evil.olean' '$HERE/Evil.lean'" ) >/dev/null 2>&1
rm -f Evil.lean                       # the SOURCE is gone; only the .olean remains
printf '\nimport Evil\n' >> Proofs/ChainSpec.lean
if [ ! -f Evil.olean ]; then
  # An attack that could not be staged must FAIL the suite, never pass quietly:
  # round-7 review found this branch printed a note and fell through to the
  # unconditional "16 attacks rejected" line, so the suite could claim a
  # rejection that never happened.
  rm -f Evil.olean
  fail "ATTACK 16 could not be staged (Evil.olean did not build) — the suite must not report green on an attack it did not run"
else
  ./check.sh > /tmp/sf16.out 2>&1 && fail "ATTACK 16 SUCCEEDED: an orphan .olean injected False and stayed GREEN!" /tmp/sf16.out
  # The defense is Phase 0's purge, which now covers ALL of verification/ and so
  # deletes the orphan BEFORE the stray check ever sees it; `import Evil` then has
  # nothing to resolve and Phase 2 fails closed. Assert that chain precisely —
  # the rejection must be the import failure AND the .olean must be gone. (An
  # earlier revision asserted the hygiene message and failed while the gate was
  # working correctly: the same wrong-diagnostic defect this suite exists to catch.)
  grep -q "FAIL: Proofs/ChainSpec" /tmp/sf16.out \
    || fail "ATTACK 16: rejected, but not by the purge+import chain" /tmp/sf16.out
  [ ! -f Evil.olean ] \
    || fail "ATTACK 16: check.sh failed but the orphan .olean survived Phase 0" /tmp/sf16.out
  echo "✓ attack 16 rejected (Phase 0 purges every .olean under verification/, so an"
  echo "  orphan compiled module with no source cannot satisfy an import)"
fi
restore; rm -f Evil.olean Evil.lean

# ── 17: TAMPER THE AUDIT'S LOGIC, NOT ITS DATA (round-6 NEW-7) ─────────────
# Switching the two fail-closed guards to `unless true` disables every in-Lean
# check while leaving the digest BYTE-IDENTICAL — the digest binds the audit's
# data, never the code that reads it. Note this attack does NOT re-pin
# Audit.lean: the sha256 pin is the only thing standing here, and that is
# exactly what is being tested.
save Proofs/Audit.lean; save Proofs/ChainSpec.lean
python3 - <<'PY'
a = open("Proofs/Audit.lean").read()
n = a.count("  unless errs.isEmpty do")
assert n >= 1, "Audit.lean fail-closed guard shape changed"
open("Proofs/Audit.lean","w").write(a.replace("  unless errs.isEmpty do", "  unless true do"))
PY
printf '\n-- SELFTEST ATTACK 17\naxiom cheat17 : ∀ (P : Prop), P\ntheorem attack17_false : False := cheat17 _\n' >> Proofs/ChainSpec.lean
./check.sh > /tmp/sf17.out 2>&1 && fail "ATTACK 17 SUCCEEDED: the audit's guards were disabled and it stayed GREEN!" /tmp/sf17.out
grep -q "INTEGRITY FAILED" /tmp/sf17.out || fail "ATTACK 17: rejected but not via the Audit.lean harness pin" /tmp/sf17.out
restore
echo "✓ attack 17 rejected (Phase 0 pins Audit.lean — its LOGIC cannot be silently switched off)"

# ── 18: SHORTEN THE PIN MAP (round-7 NEW-13) ───────────────────────────────
# Previously ALL GREEN: PROVENANCE.json is a tracked file that nothing pins, and
# the only completeness test was "is the map non-empty", so deleting the whole
# harness_integrity_sha256 key silently un-pinned BOTH lean-guard and
# Proofs/Audit.lean with no diagnostic — after which the attack-17 logic
# mutation ran green over a repository proving False, digest byte-identical.
# The required pin NAMES now live hardcoded in check.sh (the root of trust),
# so a shortened map is a build failure.
save PROVENANCE.json
python3 - <<'PY'
import json
p = "PROVENANCE.json"; d = json.load(open(p))
del d["harness_integrity_sha256"]
json.dump(d, open(p, "w"), indent=2); open(p, "a").write("\n")
PY
./check.sh > /tmp/sf18.out 2>&1 && fail "ATTACK 18 SUCCEEDED: the harness pins were deleted and the button stayed GREEN!" /tmp/sf18.out
grep -q "pin map INCOMPLETE" /tmp/sf18.out || fail "ATTACK 18: rejected but not via the pin-map completeness check" /tmp/sf18.out
grep -q "Proofs/Audit.lean" /tmp/sf18.out || fail "ATTACK 18: rejected but did not name the missing pin" /tmp/sf18.out
restore
echo "✓ attack 18 rejected (the pin map cannot be silently shortened — required names are in check.sh)"

# ── 15: COVERAGE OF THE DIGEST INPUT (direct, not an attack) ───────────────
# Attack 9 proves the digest binding fires. This proves WHAT it covers: the
# hashed block must literally contain each reference fold's definition BODY, so
# that any change to one necessarily moves the SHA-256 (round-5 NEW-2).
./check.sh > /tmp/sf15.out 2>&1 || fail "ATTACK 15 setup: clean tree is not green" /tmp/sf15.out
lake_out=$(cd "$AENEAS_HOME/backends/lean" 2>/dev/null && lake env bash -c \
  "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && '$HERE/lean-guard' 'Proofs/Audit.lean'" 2>&1)
BLOCK=$(awk '/AUDIT-MANIFEST-BEGIN/{f=1;next} /AUDIT-MANIFEST-END/{f=0} f' <<<"$lake_out")
[ -n "$BLOCK" ] || { echo "✗ ATTACK 15: no audit block"; exit 1; }
for fold in chainFoldN wotsChainFold xmssFoldN htFoldN forsInnerFold forsOuterFold \
            toIntFold toByteFold wotsCsumFold base2bOuterFold slhVerifyRoot htVerifyRoot; do
  grep -q "spec|fips205.$fold|def|value=" <<<"$BLOCK" \
    || { echo "✗ CHECK 15: the digest input does NOT carry the body of $fold"; exit 1; }
done
# Lean's equation compiler splits a recursive definition: `chainFoldN` is a thin
# wrapper and the actual recursion lives in `chainFoldN._f`. BOTH are reached by
# the closure and printed, so assert the SEMANTIC content specifically — the
# extracted primitives a fold must call — rather than assuming which line holds
# it. (An earlier revision of this check asserted the body text was on the
# wrapper's line and failed while coverage was in fact correct.)
for probe in "fips205.chainFoldN._f|def|value=.*set_hash_address" \
             "fips205.xmssFoldN._f|def|value=.*verify_mono.oracle.h" \
             "fips205.slhVerifyRoot|def|value=.*verify_mono.oracle.h_msg"; do
  grep -qE "spec\|$probe" <<<"$BLOCK" \
    || { echo "✗ CHECK 15: the digest input is missing expected body content: $probe"; exit 1; }
done
echo "✓ check 15 passed (the hashed block carries all 12 reference-fold bodies,"
echo '  including the recursive _f companions and their extracted-primitive calls)'

echo
echo "SELFTEST GREEN: 17 attacks rejected + digest-coverage check — dead files, extra axioms, dropped"
echo "oracles, vanished certs, un-manifested False theorems AND defs, gutted"
echo "statements, hand-edited models, dropped manifest rows, widened policy,"
echo "specification folds redefined to the loop, a False-proof in the auditor,"
echo "a stubbed harness, stray modules, and a shortened pin map."
