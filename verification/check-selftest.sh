#!/usr/bin/env bash
# Adversarial self-test of the check.sh gates (the R3-5 tradition: an audit that
# cannot fail is theater). The audit runs INSIDE Lean (Proofs/Audit.lean); the
# model bytes are pinned in Phase 0; the certificate SET and each STATEMENT are
# bound by a manifest fingerprint. Every attack MUST make check.sh fail, via the
# intended gate:
#
#   1. DEAD FILE        — a stray Proofs/*.lean not in the manifest.
#   2. SMUGGLED AXIOM   — a listed cert whose real cone contains a disallowed
#                         axiom; exact-equality reports extra=[...].
#   3. DROPPED ORACLE   — a listed cert whose expected cone claims an oracle its
#                         proof does not use; exact-equality reports missing=[...]
#                         (a subset checker would pass this).
#   4. VANISHED CERT    — a manifest name that no longer resolves; the explicit
#                         existence check reports NOT FOUND (collectAxioms would
#                         otherwise return [] and pass).
#   5. UN-AUDITED FALSE — round-4 F1: an UN-manifested `theorem … : False := …`
#                         added to a certificate module. The full-module
#                         enumeration must flag its disallowed cone. (This is the
#                         attack that made the pre-round-4 button green over a
#                         repo proving False.)
#   6. GUTTED STATEMENT — round-4 F2: a certificate's statement replaced by a
#                         tautology of the SAME cone. The statement fingerprint
#                         must differ from the committed manifest value.
#   7. MODEL TAMPER     — round-4 F3: a hand-edit of a gen/ model file. Phase 0
#                         must reject it before anything is compiled.
#   8. DELETED ROW      — round-4 F1 (set half): a manifest row removed. Audit
#                         still compiles, but the printed MANIFEST-FINGERPRINT
#                         changes and check.sh's committed binding must reject it.
#
# Green here means the gate genuinely rejects all eight. Self-cleaning: every
# file a step tampers is saved and restored around that step.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

TOUCHED=()
save()    { for f in "$@"; do cp -f "$f" "$f.sfbak"; TOUCHED+=("$f"); done; }
restore() { for f in "${TOUCHED[@]}"; do [ -f "$f.sfbak" ] && mv -f "$f.sfbak" "$f"; done; TOUCHED=(); }
cleanup() {
  restore
  rm -f Proofs/Stray.lean Proofs/Stray.olean Proofs/EvilSpec.lean Proofs/EvilSpec.olean \
        Proofs/Audit.olean Proofs/ChainSpec.olean *.sfbak Proofs/*.sfbak gen/SlhVerify/*.sfbak
}
trap cleanup EXIT

echo "check-selftest: attacking the gates"
echo "===================================="

# ── Attack 1: dead file ─────────────────────────────────────────────────────
echo "-- stray" > Proofs/Stray.lean
if ./check.sh > /tmp/sf1.out 2>&1; then echo "✗ ATTACK 1 SUCCEEDED (dead file stayed green)"; exit 1; fi
grep -q "DEAD FILE" /tmp/sf1.out || { echo "✗ ATTACK 1: failed, not via dead-file gate"; cat /tmp/sf1.out; exit 1; }
rm -f Proofs/Stray.lean Proofs/Stray.olean
echo "✓ attack 1 rejected (dead-file gate)"

# ── Attack 2: smuggled disallowed axiom in a real cone ──────────────────────
save check.sh Proofs/Audit.lean
cat > Proofs/EvilSpec.lean <<'EOF'
import Proofs.ChainSpec
axiom evil_ax : True
theorem evil_thm : True := evil_ax
EOF
python3 - <<'PY'
s = open("check.sh").read()
assert 'PROOFS=(\n' in s
open("check.sh","w").write(s.replace('PROOFS=(\n', 'PROOFS=(\n  "EvilSpec"\n', 1))
a = open("Proofs/Audit.lean").read()
assert 'import Proofs.ApexSpec' in a and '  [ (' in a
a = a.replace('import Proofs.ApexSpec', 'import Proofs.ApexSpec\nimport Proofs.EvilSpec', 1)
a = a.replace('  [ (', '  [ (`evil_thm, kernel3, 0),\n    (', 1)
open("Proofs/Audit.lean","w").write(a)
PY
if ./check.sh > /tmp/sf2.out 2>&1; then echo "✗ ATTACK 2 SUCCEEDED (smuggled axiom)"; exit 1; fi
grep -q "evil_ax" /tmp/sf2.out || { echo "✗ ATTACK 2: rejected but evil_ax not named"; cat /tmp/sf2.out; exit 1; }
restore; rm -f Proofs/EvilSpec.lean Proofs/EvilSpec.olean Proofs/Audit.olean
echo "✓ attack 2 rejected (extra-axiom detection — evil_ax named)"

# ── Attack 3: dropped-oracle (subset would pass; exact must not) ─────────────
save Proofs/Audit.lean
python3 - <<'PY'
import re
a = open("Proofs/Audit.lean").read()
new, n = re.subn(r'(`fips205\.to_int_loop_eq,\s*)kernel3(,\s*\d+\))', r'\1kernel3 ++ [oracleF]\2', a)
assert n == 1, f"patched {n}"
open("Proofs/Audit.lean","w").write(new)
PY
if ./check.sh > /tmp/sf3.out 2>&1; then echo "✗ ATTACK 3 SUCCEEDED (dropped oracle, subset hole)"; exit 1; fi
grep -q "missing=\[verify_mono.oracle.f\]" /tmp/sf3.out || { echo "✗ ATTACK 3: rejected but missing oracle not named"; cat /tmp/sf3.out; exit 1; }
restore; rm -f Proofs/Audit.olean
echo "✓ attack 3 rejected (missing-oracle detection — exact cone, not subset)"

# ── Attack 4: vanished certificate ──────────────────────────────────────────
save Proofs/Audit.lean
python3 - <<'PY'
a = open("Proofs/Audit.lean").read()
assert a.count('`fips205.chain_free_loop_eq') >= 1
open("Proofs/Audit.lean","w").write(a.replace('`fips205.chain_free_loop_eq,', '`fips205.chain_free_loop_eq_VANISHED,', 1))
PY
if ./check.sh > /tmp/sf4.out 2>&1; then echo "✗ ATTACK 4 SUCCEEDED (vanished cert)"; exit 1; fi
grep -q "NOT FOUND" /tmp/sf4.out || { echo "✗ ATTACK 4: rejected but not via existence check"; cat /tmp/sf4.out; exit 1; }
restore; rm -f Proofs/Audit.olean
echo "✓ attack 4 rejected (existence check — vanished cert cannot pass as 0-axiom)"

# ── Attack 5: un-manifested theorem proving False (round-4 F1, the big one) ──
save Proofs/ChainSpec.lean
printf '\n-- SELFTEST ATTACK 5 (round-4 F1): an un-manifested cert proving False.\naxiom cheat : ∀ (P : Prop), P\ntheorem repo_proves_false : False := cheat _\n' >> Proofs/ChainSpec.lean
if ./check.sh > /tmp/sf5.out 2>&1; then echo "✗ ATTACK 5 SUCCEEDED: check.sh GREEN over a repo proving False!"; exit 1; fi
grep -q "repo_proves_false" /tmp/sf5.out || { echo "✗ ATTACK 5: rejected but not via the module enumeration"; cat /tmp/sf5.out; exit 1; }
restore; rm -f Proofs/ChainSpec.olean Proofs/Audit.olean
echo "✓ attack 5 rejected (module enumeration — an un-manifested False theorem cannot pass)"

# ── Attack 6: gutted statement, cone preserved (round-4 F2) ─────────────────
# Gut a LEAF certificate (to_byte_loop_eq — nothing depends on it, so Phase 2
# still compiles and the fingerprint gate is what must bite). Replace its
# statement+proof with a kernel-3 tautology: same cone, different type.
save Proofs/InputPrepSpec.lean
python3 - <<'PY'
s = open("Proofs/InputPrepSpec.lean").read()
i = s.index("theorem to_byte_loop_eq (n : Std.U32) (k : Nat) :")
j = s.index("theorem hbody_cs", i)   # the NEXT declaration (to_byte_loop_eq is a leaf)
gut = "theorem to_byte_loop_eq : (∀ p : Prop, p ∨ ¬p) := Classical.em\n\n"
open("Proofs/InputPrepSpec.lean","w").write(s[:i] + gut + s[j:])
PY
if ./check.sh > /tmp/sf6.out 2>&1; then echo "✗ ATTACK 6 SUCCEEDED: gutted statement passed (cone preserved)"; exit 1; fi
grep -qi "fingerprint" /tmp/sf6.out || { echo "✗ ATTACK 6: rejected but not via the statement fingerprint"; cat /tmp/sf6.out; exit 1; }
restore; rm -f Proofs/InputPrepSpec.olean Proofs/Audit.olean
echo "✓ attack 6 rejected (statement fingerprint — a gutted statement of the same cone cannot pass)"

# ── Attack 7: hand-edited model file (round-4 F3) ───────────────────────────
save gen/SlhVerify/Funs.lean
printf '\n-- SELFTEST ATTACK 7 (round-4 F3): hand-edited model.\n' >> gen/SlhVerify/Funs.lean
if ./check.sh > /tmp/sf7.out 2>&1; then echo "✗ ATTACK 7 SUCCEEDED: hand-edited model passed"; exit 1; fi
grep -q "MODEL INTEGRITY FAILED" /tmp/sf7.out || { echo "✗ ATTACK 7: rejected but not via Phase 0"; cat /tmp/sf7.out; exit 1; }
restore
echo "✓ attack 7 rejected (Phase 0 model-byte integrity — a hand-edited model cannot compile)"

# ── Attack 8: deleted manifest row (round-4 F1 set half) ────────────────────
save Proofs/Audit.lean
python3 - <<'PY'
import re
a = open("Proofs/Audit.lean").read()
new, n = re.subn(r'\n *\(`fips205\.to_int_loop_eq,[^\n]*\),', '', a)
assert n == 1, f"removed {n}"
open("Proofs/Audit.lean","w").write(new)
PY
if ./check.sh > /tmp/sf8.out 2>&1; then echo "✗ ATTACK 8 SUCCEEDED: a deleted manifest row passed (set unbound)"; exit 1; fi
grep -q "manifest fingerprint mismatch" /tmp/sf8.out || { echo "✗ ATTACK 8: rejected but not via the manifest-fingerprint binding"; cat /tmp/sf8.out; exit 1; }
restore; rm -f Proofs/Audit.olean
echo "✓ attack 8 rejected (manifest fingerprint — a silently-dropped cert cannot pass)"

echo
echo "SELFTEST GREEN: the gate rejects dead files, extra axioms, dropped oracles,"
echo "vanished certs, un-manifested False theorems, gutted statements, hand-edited"
echo "models, and deleted manifest rows."
