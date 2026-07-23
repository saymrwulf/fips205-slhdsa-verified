#!/usr/bin/env bash
# Adversarial self-test of the check.sh gates (the R3-5 tradition: an audit
# that cannot fail is theater). Two attacks, both MUST make check.sh fail:
#
#   1. DEAD FILE   — a stray Proofs/*.lean not in the manifest.
#   2. SMUGGLED AXIOM — a certificate whose cone contains an axiom outside
#      {kernel-3} ∪ {the five SHA-2 oracles}.
#
# Green here means: the gates genuinely reject both. Self-cleaning.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

cleanup() { rm -f Proofs/Stray.lean Proofs/Stray.olean Proofs/EvilSpec.lean \
                  Proofs/EvilSpec.olean check-evil-tmp.sh; }
trap cleanup EXIT

echo "check-selftest: attacking the gates"
echo "===================================="

# ── Attack 1: dead file ─────────────────────────────────────────────────────
echo "-- stray" > Proofs/Stray.lean
if ./check.sh > /tmp/selftest-dead.out 2>&1; then
  echo "✗ ATTACK 1 SUCCEEDED: check.sh stayed green with a dead file"; exit 1
fi
grep -q "DEAD FILE" /tmp/selftest-dead.out \
  || { echo "✗ ATTACK 1: failed, but not via the dead-file gate"; exit 1; }
rm -f Proofs/Stray.lean Proofs/Stray.olean
echo "✓ attack 1 rejected (dead-file gate works)"

# ── Attack 2: smuggled axiom ────────────────────────────────────────────────
cat > Proofs/EvilSpec.lean <<'EOF'
import Proofs.ChainSpec
axiom evil_ax : True
theorem evil_thm : True := evil_ax
EOF
python3 - <<'PY'
s = open("check.sh").read()
s = s.replace('PROOFS=(\n  "ChainSpec"\n)', 'PROOFS=(\n  "ChainSpec"\n  "EvilSpec"\n)')
# Robust to the growing PROOFS / CERTS lists (do NOT hard-code their current
# contents — that rots the self-test as certificates are added): inject the
# evil entries right after each array's opening paren.
assert 'PROOFS=(\n' in s and 'CERTS=(\n' in s, "check.sh array shape changed"
s = s.replace('PROOFS=(\n', 'PROOFS=(\n  "EvilSpec"\n', 1)
s = s.replace('CERTS=(\n', 'CERTS=(\n  "evil_thm"\n', 1)
assert '{ echo "import Proofs.ChainSpec"' in s, "check.sh audit import shape changed"
s = s.replace('{ echo "import Proofs.ChainSpec"',
              '{ echo "import Proofs.EvilSpec"; echo "import Proofs.ChainSpec"', 1)
open("check-evil-tmp.sh","w").write(s)
PY
chmod +x check-evil-tmp.sh
if ./check-evil-tmp.sh > /tmp/selftest-evil.out 2>&1; then
  echo "✗ ATTACK 2 SUCCEEDED: audit passed a smuggled axiom"; exit 1
fi
grep -q "DISALLOWED" /tmp/selftest-evil.out \
  || { echo "✗ ATTACK 2: failed, but not via the axiom gate"; exit 1; }
echo "✓ attack 2 rejected (axiom gate works)"

echo
echo "SELFTEST GREEN: both gates genuinely reject their attacks."
