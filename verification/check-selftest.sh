#!/usr/bin/env bash
# Adversarial self-test of the check.sh gates (the R3-5 tradition: an audit that
# cannot fail is theater). The axiom audit now runs INSIDE Lean
# (Proofs/Audit.lean, exact cone per certificate via collectAxioms), so these
# attacks target that gate's actual guarantees — not the retired text parser.
# Every attack MUST make check.sh fail, via the intended gate:
#
#   1. DEAD FILE          — a stray Proofs/*.lean not in the manifest.
#   2. SMUGGLED AXIOM     — a certificate whose real cone contains a disallowed
#                           axiom, declared clean. Exact-equality must report it
#                           as `extra=[...]` (the classic extra-axiom detection).
#   3. DROPPED ORACLE     — a certificate whose expected cone claims an oracle
#                           its real proof does NOT use. A subset checker would
#                           pass this; exact-equality must report `missing=[...]`.
#                           This is the property the round-2 review demanded and
#                           the retired subset parser could never enforce.
#   4. VANISHED CERT      — a certificate name that no longer resolves. Since
#                           `collectAxioms` returns [] for a missing name (a
#                           fail-open trap), the audit must report NOT FOUND.
#
# Green here means: the gate genuinely rejects all four. Self-cleaning: the real
# check.sh / Proofs/Audit.lean are backed up and restored around every attack.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

restore() {
  [ -f check.sh.selftest.bak ]        && mv -f check.sh.selftest.bak        check.sh
  [ -f Proofs/Audit.lean.selftest.bak ] && mv -f Proofs/Audit.lean.selftest.bak Proofs/Audit.lean
  return 0
}
cleanup() {
  restore
  rm -f Proofs/Stray.lean Proofs/Stray.olean \
        Proofs/EvilSpec.lean Proofs/EvilSpec.olean Proofs/Audit.olean
}
trap cleanup EXIT
backup() { cp -f check.sh check.sh.selftest.bak; cp -f Proofs/Audit.lean Proofs/Audit.lean.selftest.bak; }

echo "check-selftest: attacking the gates"
echo "===================================="

# ── Attack 1: dead file ─────────────────────────────────────────────────────
echo "-- stray" > Proofs/Stray.lean
if ./check.sh > /tmp/selftest-dead.out 2>&1; then
  echo "✗ ATTACK 1 SUCCEEDED: check.sh stayed green with a dead file"; exit 1
fi
grep -q "DEAD FILE" /tmp/selftest-dead.out \
  || { echo "✗ ATTACK 1: failed, but not via the dead-file gate"; cat /tmp/selftest-dead.out; exit 1; }
rm -f Proofs/Stray.lean Proofs/Stray.olean
echo "✓ attack 1 rejected (dead-file gate works)"

# ── Attack 2: smuggled disallowed axiom in a real cone ──────────────────────
# A new certificate whose cone genuinely contains `evil_ax`, declared as clean
# (kernel-3) in the expected table. Exact-equality must flag extra=[evil_ax].
backup
cat > Proofs/EvilSpec.lean <<'EOF'
import Proofs.ChainSpec
axiom evil_ax : True
theorem evil_thm : True := evil_ax
EOF
python3 - <<'PY'
import re
# check.sh: add EvilSpec to PROOFS so Phase 2 builds it and the dead-file gate
# passes (inject right after the array's opening paren — no hard-coded contents).
s = open("check.sh").read()
assert 'PROOFS=(\n' in s, "check.sh PROOFS array shape changed"
s = s.replace('PROOFS=(\n', 'PROOFS=(\n  "EvilSpec"\n', 1)
open("check.sh","w").write(s)
# Audit.lean: import EvilSpec and claim evil_thm is kernel-3 clean.
a = open("Proofs/Audit.lean").read()
assert 'import Proofs.ApexSpec' in a, "Audit.lean import shape changed"
a = a.replace('import Proofs.ApexSpec', 'import Proofs.ApexSpec\nimport Proofs.EvilSpec', 1)
assert 'def expectedCones : List (Name × List Name) :=' in a and '  [ (' in a, "Audit.lean table shape changed"
a = a.replace('  [ (', '  [ (`evil_thm, kernel3),\n    (', 1)
open("Proofs/Audit.lean","w").write(a)
PY
if ./check.sh > /tmp/selftest-evil.out 2>&1; then
  echo "✗ ATTACK 2 SUCCEEDED: audit passed a smuggled disallowed axiom"; exit 1
fi
grep -q "AUDIT FAILED" /tmp/selftest-evil.out \
  || { echo "✗ ATTACK 2: failed, but not via the axiom audit"; cat /tmp/selftest-evil.out; exit 1; }
grep -q "evil_ax" /tmp/selftest-evil.out \
  || { echo "✗ ATTACK 2: rejected, but the audit did not name the smuggled axiom"; cat /tmp/selftest-evil.out; exit 1; }
restore; rm -f Proofs/EvilSpec.lean Proofs/EvilSpec.olean Proofs/Audit.olean
echo "✓ attack 2 rejected (extra-axiom detection works — evil_ax named)"

# ── Attack 3: dropped-oracle (subset would pass; exact must not) ─────────────
# Claim to_int_loop_eq depends on oracle.f. Its real cone is kernel-3 only, so
# the audit must report missing=[verify_mono.oracle.f].
backup
python3 - <<'PY'
import re
a = open("Proofs/Audit.lean").read()
new, n = re.subn(r'(`fips205\.to_int_loop_eq,\s*)kernel3\)', r'\1kernel3 ++ [oracleF])', a)
assert n == 1, f"expected exactly one to_int table entry, patched {n}"
open("Proofs/Audit.lean","w").write(new)
PY
if ./check.sh > /tmp/selftest-drop.out 2>&1; then
  echo "✗ ATTACK 3 SUCCEEDED: audit passed a certificate missing a claimed oracle (subset hole!)"; exit 1
fi
grep -q "AUDIT FAILED" /tmp/selftest-drop.out \
  || { echo "✗ ATTACK 3: failed, but not via the axiom audit"; cat /tmp/selftest-drop.out; exit 1; }
grep -q "missing=\[verify_mono.oracle.f\]" /tmp/selftest-drop.out \
  || { echo "✗ ATTACK 3: rejected, but not by naming the missing oracle (exact-cone not enforced?)"; cat /tmp/selftest-drop.out; exit 1; }
restore; rm -f Proofs/Audit.olean
echo "✓ attack 3 rejected (missing-oracle detection works — exact cone enforced, not subset)"

# ── Attack 4: vanished certificate (collectAxioms-returns-[] trap) ──────────
backup
python3 - <<'PY'
a = open("Proofs/Audit.lean").read()
assert a.count('`fips205.chain_free_loop_eq') >= 1
a = a.replace('`fips205.chain_free_loop_eq,', '`fips205.chain_free_loop_eq_VANISHED,', 1)
open("Proofs/Audit.lean","w").write(a)
PY
if ./check.sh > /tmp/selftest-vanish.out 2>&1; then
  echo "✗ ATTACK 4 SUCCEEDED: audit stayed green for a non-existent certificate (fail-open!)"; exit 1
fi
grep -q "NOT FOUND" /tmp/selftest-vanish.out \
  || { echo "✗ ATTACK 4: failed, but not via the existence check"; cat /tmp/selftest-vanish.out; exit 1; }
restore; rm -f Proofs/Audit.olean
echo "✓ attack 4 rejected (existence check works — a vanished cert cannot pass as 0-axiom)"

echo
echo "SELFTEST GREEN: the audit genuinely rejects extra axioms, dropped oracles,"
echo "vanished certificates, and dead proof files."
