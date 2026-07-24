#!/usr/bin/env bash
# Adversarial self-test of the check.sh gates (the R3-5 tradition: an audit
# that cannot fail is theater). Three attacks, all MUST make check.sh fail:
#
#   1. DEAD FILE   — a stray Proofs/*.lean not in the manifest.
#   2. SMUGGLED AXIOM (short cone) — an axiom outside {kernel-3} ∪ {5 oracles},
#      on the FIRST line of the cone.
#   3. SMUGGLED AXIOM (WRAPPED cone) — an axiom on a CONTINUATION line of a
#      cone that wraps (the exact fail-open exploit external review found on
#      2026-07-24: the old single-line parser saw only line 1). This attack
#      guards the flattened-parse fix; a self-test that only plants short cones
#      cannot detect a wrapped-cone parser regression.
#
# Green here means: the gates genuinely reject all three. Self-cleaning.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

cleanup() { rm -f Proofs/Stray.lean Proofs/Stray.olean Proofs/EvilSpec.lean \
                  Proofs/EvilSpec.olean Proofs/EvilWrapSpec.lean \
                  Proofs/EvilWrapSpec.olean check-evil-tmp.sh check-evilwrap-tmp.sh; }
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
rm -f Proofs/EvilSpec.lean Proofs/EvilSpec.olean check-evil-tmp.sh
echo "✓ attack 2 rejected (axiom gate works)"

# ── Attack 3: smuggled axiom on a WRAPPED cone (the fail-open exploit) ───────
# evil_wrapped_thm bundles a disallowed axiom with the apex theorem, so its cone
# is 9 axioms and WRAPS across physical lines with review_evil_ax on a
# continuation line — exactly what the old single-line parser missed.
cat > Proofs/EvilWrapSpec.lean <<'EOF'
import Proofs.ApexSpec
open Aeneas Aeneas.Std Result
open fips205
axiom review_evil_ax : True
theorem evil_wrapped_thm
    (mprime : Slice Std.U8)
    (sig : types.SlhDsaSig 12#usize 7#usize 9#usize 14#usize 35#usize 16#usize)
    (pk : types.SlhPublicKey 16#usize) :
    True ∧ (verify_mono.slh_verify_128s mprime sig pk
             = (do let root ← slhVerifyRoot 63#usize 30#usize mprime sig pk
                   ok (decide (root.val = pk.pk_root.val)))) :=
  ⟨review_evil_ax, slh_verify_128s_accepts_iff mprime sig pk⟩
EOF
python3 - <<'PY'
s = open("check.sh").read()
assert 'PROOFS=(\n' in s and 'CERTS=(\n' in s, "check.sh array shape changed"
s = s.replace('PROOFS=(\n', 'PROOFS=(\n  "EvilWrapSpec"\n', 1)
s = s.replace('CERTS=(\n', 'CERTS=(\n  "evil_wrapped_thm"\n', 1)
assert '{ echo "import Proofs.ChainSpec"' in s, "check.sh audit import shape changed"
s = s.replace('{ echo "import Proofs.ChainSpec"',
              '{ echo "import Proofs.EvilWrapSpec"; echo "import Proofs.ChainSpec"', 1)
open("check-evilwrap-tmp.sh","w").write(s)
PY
chmod +x check-evilwrap-tmp.sh
if ./check-evilwrap-tmp.sh > /tmp/selftest-evilwrap.out 2>&1; then
  echo "✗ ATTACK 3 SUCCEEDED: audit passed a smuggled axiom on a WRAPPED cone (fail-open!)"; exit 1
fi
grep -q "DISALLOWED" /tmp/selftest-evilwrap.out \
  || { echo "✗ ATTACK 3: failed, but not via the axiom gate (wrapped-cone parse?)"; exit 1; }
grep -q "review_evil_ax" /tmp/selftest-evilwrap.out \
  || { echo "✗ ATTACK 3: rejected, but the audit did not name the continuation-line axiom"; exit 1; }
echo "✓ attack 3 rejected (wrapped-cone axiom gate works — the continuation-line axiom was seen)"

echo
echo "SELFTEST GREEN: all three gates genuinely reject their attacks."
