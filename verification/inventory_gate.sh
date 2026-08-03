#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# inventory_gate.sh — diff an observed environment inventory against the
# pinned allowlist. PORTED VERBATIM from ltl-accumulator-verified apart from
# the axiom-surface assertion, which is repo-specific: there the corpus admits
# exactly one sanctioned axiom, here it admits none.
#
# This is THE production coverage gate: check.sh Phase 2c calls it, and the
# self-test exercises this exact script — the tested logic IS the shipping
# logic.
#
# Usage: inventory_gate.sh <observed-lean-output> <allowlist-file> [<tag>]
#
# <tag> defaults to INV — the CORPUS walk. Pass DRV to gate the INSTRUMENTS'
# OWN SURFACE with this same implementation.
#
# WHY THE TAG EXISTS — round-8 review (Claude, register keys
# `drv-surface-no-cones`, `accounting-certifies-enumeration`).
#
# The accounting identity added in round 7 proved every constant the kernel
# sees is ENUMERATED by one of the two walks. The reviewer showed that
# enumeration is not audit: a claim planted in an instrument WAS enumerated —
# `DRV|LTLAccAudit.bait.smuggled|theorem` — and then nothing looked at it,
# because DRV rows carried name and kind and NO CONE, and no allowlist covered
# them. In their words, the identity "converted 36 declarations nobody
# enumerated into 36 declarations nobody examined. That is progress of one
# step, not two."
#
# The second step is here: DRV rows now carry their axiom cone and are pinned
# in a committed allowlist, by THIS gate, in both directions — exactly as the
# corpus is. One implementation, not two, because a second copy of a coverage
# gate is a second thing to drift.
#
# It also retires a heuristic. The driver-surface rule permits a theorem whose
# name extends a constant declared alongside it, since that is what the
# elaborator generates for a definition; the reviewer showed it "breaks in one
# line" — declare `def bait`, then `theorem bait.smuggled` passes. That rule is
# kept as a fast, readable first line of defence, but it is NO LONGER
# LOAD-BEARING: a planted claim now has to appear in the pinned allowlist, and
# a new row fails closed whatever it is named.
#
# Fail-closed in BOTH directions:
#   UNCLASSIFIED — constant in the environment, absent from the allowlist
#                  (new/renamed decl, changed kind, or changed axiom cone)
#   STALE        — allowlist entry absent from the environment
# plus an output-integrity check: the INV-COUNT trailer emitted by
# Proofs/Inventory.lean must equal the number of INV lines actually seen,
# so a truncated or crashed run can never pass as an empty diff.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
export LC_ALL=C   # byte-order collation: sort/comm must agree with Lean's String order
obs_file="$1"; allow_file="$2"; TAG="${3:-INV}"
case "$TAG" in
  INV) WHAT="the audited corpus"; TRAILER_TAG="INV-COUNT"; LABEL="inventory gate"; TRUNCLABEL="INVENTORY TRUNCATED" ;;
  DRV) WHAT="the audit instruments"; TRAILER_TAG="DRV-COUNT"; LABEL="driver-surface gate"; TRUNCLABEL="DRIVER SURFACE TRUNCATED" ;;
  *)   echo "  GATE MISUSE: unknown tag '$TAG' (expected INV or DRV)"; exit 1 ;;
esac

# The trailer is an OUTPUT-INTEGRITY check: it must equal the number of rows
# the driver(s) actually emitted, BEFORE de-duplication. Comparing it to the
# de-duplicated count conflates "a run was truncated" with "two rows were
# identical", and the second is a record-format defect that must be fixed at
# the source, not absorbed here. (It was: DRV rows now carry their driver.)
N_RAW=$(grep -c "^$TAG|" "$obs_file" || true)
OBS=$(grep "^$TAG|" "$obs_file" | sort -u)
N_OBS=$(printf '%s' "$OBS" | grep -c "^$TAG|" || true)
if [ "$N_RAW" -ne "$N_OBS" ]; then
  echo "  DUPLICATE $TAG RECORDS: $N_RAW rows collapse to $N_OBS distinct ones."
  echo "  Two declarations share a record, so one is covered by the other's entry:"
  grep "^$TAG|" "$obs_file" | sort | uniq -d | head -5 | sed 's/^/    /'
  exit 1
fi
# Each driver emits its own trailer, so DRV trailers are SUMMED; the corpus
# walk emits one and the last is taken. Either way a truncated or crashed run
# must never pass as an empty diff.
if [ "$TAG" = DRV ]; then
  TRAILER=$(grep "^$TRAILER_TAG|" "$obs_file" | cut -d'|' -f2 | paste -sd+ - | bc)
else
  TRAILER=$(grep "^$TRAILER_TAG|" "$obs_file" | tail -1 | cut -d'|' -f2)
fi
if [ -z "$TRAILER" ] || [ "$TRAILER" != "$N_RAW" ]; then
  echo "  $TRUNCLABEL: trailer=${TRAILER:-absent}, observed $N_RAW lines"
  exit 1
fi

ALLOW=$(grep "^$TAG|" "$allow_file" | sort -u)
FAILGATE=0
UNCLASS=$(comm -23 <(printf '%s\n' "$OBS") <(printf '%s\n' "$ALLOW"))
STALE=$(comm -13 <(printf '%s\n' "$OBS") <(printf '%s\n' "$ALLOW"))
if [ -n "$UNCLASS" ]; then
  printf '%s\n' "$UNCLASS" | sed 's/^/  UNCLASSIFIED (in environment, not allowlisted): /'
  FAILGATE=1
fi
if [ -n "$STALE" ]; then
  printf '%s\n' "$STALE" | sed 's/^/  STALE (allowlisted, not in environment): /'
  FAILGATE=1
fi

# The audited corpus admits NO axiom declarations at all: the sanctioned
# external models live in gen/, outside every module these drivers cover, and
# are byte-pinned by Phase 0b. An axiom appearing here would be a declaration
# smuggled into the proof corpus, which Phase 2b also catches kernel-side —
# two independent gates on the same property, deliberately.
AXLINES=$(printf '%s\n' "$OBS" | grep '|axiom|' || true)
if [ -n "$AXLINES" ]; then
  echo "  AXIOM SURFACE DRIFT: $WHAT must declare no axioms; observed:"
  printf '%s\n' "$AXLINES" | sed 's/^/    /'
  FAILGATE=1
fi

# The message must describe what was actually checked. It said "single
# sanctioned axiom" when ported, which is the accumulator's policy; here the
# audited corpus permits NONE, and a success line describing a different rule
# is how an assertion quietly stops meaning anything.
[ "$FAILGATE" = 0 ] && echo "  $LABEL: $N_OBS constants, environment == allowlist, zero axioms declared in $WHAT"
exit "$FAILGATE"
