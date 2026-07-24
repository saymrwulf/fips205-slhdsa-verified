#!/usr/bin/env bash
# The one-button claim for this repository (rigor invariant R3).
# Green output == the full claim. This script is the ONLY source of the
# word "proven" for this repo.
#
#   Phase 1 — compile the extracted Lean model (gen/SlhVerify).
#   Phase 2 — compile the proof files (Proofs/).
#   Phase 3 — axiom audit, performed INSIDE Lean (Proofs/Audit.lean): each
#             certificate's cone, read from the kernel via `collectAxioms`, must
#             EQUAL its expected set EXACTLY — kernel-3 plus only the named SHA-2
#             oracles. No text parsing (round-2 review closed that class of bug);
#             any extra, any missing, a renamed/deleted cert, or an axiom/opaque
#             sham is a Lean elaboration error → non-zero exit → fail-closed.
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
  # (PROOFS) or be the audit driver (Audit, compiled in Phase 3).
  for f in Proofs/*.lean; do b=\$(basename \"\$f\" .lean)
    case \" ${PROOFS[*]} Audit \" in *\" \$b \"*) ;; *) echo \"DEAD FILE: Proofs/\$b.lean not in manifest\"; exit 1 ;; esac
  done
"

# ── Phase 3: axiom audit (exact cone per certificate, inside Lean) ───────────
echo "=== Phase 3: axiom audit (exact cone per certificate — inside Lean) ==="
cd "$AENEAS_LEAN"
# Proofs/Audit.lean reads each cert's cone from the kernel (collectAxioms) and
# asserts SET EQUALITY against its expected boundary. Compiling it IS the audit:
# any mismatch throws → non-zero exit. We additionally require the explicit
# PASSED line, so a build that somehow exits 0 without running the audit still
# fails closed.
AUD_OUT=$(lake env bash -c "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' 'Proofs/Audit.lean'" 2>&1) || {
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AXIOM AUDIT FAILED (Audit.lean did not compile — cone mismatch, missing cert, or sham)"; exit 1; }
if ! grep -qF "exact-cone audit PASSED" <<<"$AUD_OUT"; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AXIOM AUDIT FAILED (no PASSED line — fail-closed)"; exit 1
fi
echo "  ✓ exact-cone audit PASSED: each of the ${#CERTS[@]} certificate cones == its expected boundary set"

echo
echo "ALL GREEN — model compiles, proofs compile, and every certificate cone"
echo "equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles."
echo "Certificates proven: ${CERTS[*]}"
