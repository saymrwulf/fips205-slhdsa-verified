#!/usr/bin/env bash
# drill.sh — the post-flight drill as a BUTTON.
#
# Motivation (2026-07-23): mid-session model degradation is a recurring,
# operator-observed reality. Five manual drills over this campaign each
# re-verified the latest work window; every substantive check they ran was
# MECHANICAL. This script is that battery as one deterministic button, per
# the estate's standing philosophy: enforcement lives in buttons, never in
# model quality. A degraded window cannot fake this — it either exits 0 or
# it does not.
#
# Run it after ANY work window (flip suspected or not). What it cannot
# cover — fidelity review of NEWLY-written specs against their extracted
# ground truth and upstream sources — remains the bespoke, intelligent part
# of the drill, and is required exactly once per new artifact, recorded in
# the artifact's commit message.
#
#   1. hygiene   — worktree clean; local == remote head
#   2. honesty   — no sorry/admit/axiom outside gen/*External; drafts/ (if
#                  present) is the only place sorries may live
#   3. the claim — check.sh green (model + proofs + axiom audit)
#   4. the gates — check-selftest.sh green (audit gates genuinely reject
#                  a dead file and a smuggled axiom)
#   5. reproducibility (--full) — extract.sh regenerates gen/ byte-identical
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
cd "$REPO"
FULL="${1:-}"

fail=0
step() { echo; echo "── $1"; }

step "1. hygiene: worktree + heads"
if [ -n "$(git status --porcelain)" ]; then
  echo "✗ worktree not clean:"; git status --short; fail=1
else echo "✓ worktree clean"; fi
BR=$(git branch --show-current)
L=$(git rev-parse HEAD); R=$(git ls-remote -q origin "$BR" | cut -f1)
if [ "$L" = "$R" ]; then echo "✓ local == remote ($(git rev-parse --short HEAD))"
else echo "✗ local $L != remote $R"; fail=1; fi

step "2. honesty: sorry/admit/axiom placement"
BAD=$(grep -rlnE "sorry|admit" verification/Proofs/*.lean 2>/dev/null || true)
if [ -n "$BAD" ]; then echo "✗ sorry/admit in Proofs/: $BAD"; fail=1
else echo "✓ Proofs/ free of sorry/admit"; fi
# Tripwire only: column-0 declarations. The REAL gate is check.sh Phase 3
# (the #print-axioms cone audit), which catches any smuggled axiom wherever
# it hides — this grep just fails faster on the obvious case.
AX=$(grep -rlE "^axiom " verification/Proofs/*.lean 2>/dev/null || true)
if [ -n "$AX" ]; then echo "✗ axiom declared under Proofs/: $AX (H4: axioms live in gen/*External only)"; fail=1
else echo "✓ no axiom declarations under Proofs/"; fi

step "3. the claim: check.sh"
if verification/check.sh > /tmp/drill-check.out 2>&1; then
  tail -3 /tmp/drill-check.out | sed 's/^/  /'
  echo "✓ check.sh green"
else echo "✗ check.sh FAILED:"; tail -12 /tmp/drill-check.out | sed 's/^/  /'; fail=1; fi

step "4. the gates: check-selftest.sh"
if verification/check-selftest.sh > /tmp/drill-selftest.out 2>&1; then
  grep -E "attack" /tmp/drill-selftest.out | sed 's/^/  /'
  echo "✓ self-test green (both gates reject their attacks)"
else echo "✗ SELF-TEST FAILED:"; tail -8 /tmp/drill-selftest.out | sed 's/^/  /'; fail=1; fi

if [ "$FULL" = "--full" ]; then
  step "5. reproducibility: extract.sh regen byte-identity"
  if verification/extract.sh > /tmp/drill-extract.out 2>&1 \
     && [ -z "$(git status --porcelain verification/gen/)" ]; then
    echo "✓ regenerated gen/ byte-identical to committed"
  else
    echo "✗ regen diverged or failed:"; git status --short verification/gen/ | sed 's/^/  /'
    git checkout -q -- verification/gen/ 2>/dev/null || true; fail=1
  fi
fi

echo
if [ "$fail" = 0 ]; then
  echo "DRILL GREEN — the mechanical battery holds. Remaining human/model duty:"
  echo "fidelity review of any NEW spec vs its extracted + upstream ground truth."
  exit 0
else
  echo "DRILL RED — at least one mechanical check failed. Fix before any claim."
  exit 1
fi
