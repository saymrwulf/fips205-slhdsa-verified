#!/usr/bin/env bash
# The one-button claim for this repository (rigor invariant R3).
# Green output == the full claim. This script is the ONLY source of the
# word "proven" for this repo.
#
#   Phase 1 — compile the extracted Lean model (gen/SlhVerify).
#   Phase 2 — compile the proof files (Proofs/).
#   Phase 3 — axiom audit: every certificate's #print axioms cone must be a
#             subset of {propext, Classical.choice, Quot.sound} plus the five
#             SHA-2 hash oracles (the documented boundary) — nothing else.
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
# Certificates whose axiom cones are audited, and the allowed extras beyond
# the three kernel axioms: the five SHA-2 verify-path oracles. A certificate
# is listed here only once it is genuinely proven.
CERTS=(
  "fips205.chain_free_loop_eq"
  "fips205.wots_loop1_eq"
  "fips205.xmss_loop_eq"
  "fips205.ht_loop_eq"
  "fips205.fors_inner_loop_eq"
  "fips205.fors_outer_loop_eq"
  "fips205.to_int_loop_eq"
  "fips205.to_byte_loop_eq"
  "fips205.wots_csum_loop_eq"
  "fips205.base2b_outer_loop_eq"
  "fips205.slh_verify_128s_accepts_iff"
)
ORACLES="verify_mono.oracle.f, verify_mono.oracle.h, verify_mono.oracle.t_l, verify_mono.oracle.t_len, verify_mono.oracle.h_msg"
ALLOWED="[propext, Classical.choice, Quot.sound, ${ORACLES}]"

echo "fips205-slhdsa-verified — check"
echo "==============================="

# ── Phase 1: model ──────────────────────────────────────────────────────────
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
  for f in Proofs/*.lean; do b=\$(basename \"\$f\" .lean)
    case \" ${PROOFS[*]} \" in *\" \$b \"*) ;; *) echo \"DEAD FILE: Proofs/\$b.lean not in manifest\"; exit 1 ;; esac
  done
"

# ── Phase 3: axiom audit ────────────────────────────────────────────────────
echo "=== Phase 3: axiom audit (cone ⊆ kernel-3 + 5 oracles) ==="
cd "$AENEAS_LEAN"
AUD="$HERE/Proofs/.audit.lean"
{ echo "import Proofs.ChainSpec"; echo "import Proofs.WotsSpec"
  echo "import Proofs.XmssSpec"; echo "import Proofs.HtSpec"
  echo "import Proofs.ForsInnerSpec"; echo "import Proofs.ForsOuterSpec"; echo "import Proofs.InputPrepSpec"; echo "import Proofs.ApexSpec"
  for c in "${CERTS[@]}"; do echo "#print axioms $c"; done
} > "$AUD"
OUT=$(lake env bash -c "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' 'Proofs/.audit.lean'" 2>&1)
rm -f "$AUD"
# CRITICAL: Lean WRAPS long axiom cones across physical lines. A per-line parse
# silently drops continuation-line axioms (fail-OPEN — external review round 1,
# 2026-07-24, demonstrated a smuggled axiom on line 2 passing). FLATTEN the whole
# report first, then extract each cert's complete bracketed cone with a
# literal-string (regex-safe) scan and subset-check it. Missing/empty report =>
# fail-CLOSED.
FLAT=$(echo "$OUT" | tr '\n' ' ' | tr -s ' ')
fail=0
for c in "${CERTS[@]}"; do
  marker="'$c' depends on axioms: ["
  if ! grep -qF "$marker" <<<"$FLAT"; then
    echo "  ✗ $c — no axiom report (fail-closed)"; fail=1; continue
  fi
  # full cone between this cert's '[' and the next ']' (literal index, not regex)
  cone=$(awk -v m="$marker" '{ i=index($0,m); if(i>0){ r=substr($0,i+length(m)); j=index(r,"]"); if(j>0) print substr(r,1,j-1) } }' <<<"$FLAT")
  bad=$(echo "$cone" | tr ',' '\n' | sed 's/^ *//;s/ *$//' | while read -r ax; do
    [ -z "$ax" ] && continue
    case " propext Classical.choice Quot.sound verify_mono.oracle.f verify_mono.oracle.h verify_mono.oracle.t_l verify_mono.oracle.t_len verify_mono.oracle.h_msg " in
      *" $ax "*) ;; *) echo "$ax" ;;
    esac
  done)
  if [ -n "$bad" ]; then echo "  ✗ $c — DISALLOWED axioms: $(echo $bad | tr '\n' ' ')"; fail=1
  else echo "  ✓ $c  cone ⊆ allowed ($(echo "$cone" | tr ',' '\n' | grep -c .) axioms audited)"; fi
done
[ "$fail" = 0 ] || { echo "AXIOM AUDIT FAILED"; exit 1; }

echo
echo "ALL GREEN — model compiles, proofs compile, every certificate cone is"
echo "the three kernel axioms plus (at most) the SHA-2 hash oracles."
echo "Certificates proven: ${CERTS[*]}"
