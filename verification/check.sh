#!/usr/bin/env bash
# The one-button claim for this repository (rigor invariant R3).
#
# PHASE 1 (current): compiles the extracted Lean model (gen/SlhVerify) under
# lean-guard. Green here means the monomorphic SHA2-128s verify cone
# translated and TYPE-CHECKS — it does NOT yet mean anything is proven. There
# are zero certificates; the proof layers come next. This script grows a
# Phase-2 (proofs) and Phase-3 (axiom audit) section as the pyramid rises,
# exactly like the ed25519 check.sh.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
source ~/aeneas-toolchain/env.sh
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
TIMEOUT="${LEAN_TIMEOUT:-300}"
CORES="${LEAN_MAX_CORES:-4}"

# Import order (each depends on the previous).
GEN_MODULES=(
  "SlhVerify/TypesExternal"
  "SlhVerify/Types"
  "SlhVerify/FunsExternal"
  "SlhVerify/Funs"
)

echo "fips205-slhdsa-verified — check (PHASE 1: model compile only)"
echo "============================================================"
echo "NOTE: 0 certificates. A green compile proves the extracted model is"
echo "well-formed; it does NOT prove the verifier correct. See README.md."
echo

LOG=$(mktemp /tmp/fips205-check-XXXX.log)
cd "$AENEAS_LEAN"
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  compile() {
    echo \"  · \$1\"
    LEAN_TIMEOUT=$TIMEOUT LEAN_MAX_CORES=$CORES '$HERE/lean-guard' \"\${1}.lean\" 2>&1 | tee -a '$LOG' || { echo \"FAIL: \$1\"; exit 1; }
  }
  for m in ${GEN_MODULES[*]}; do compile \"\$m\"; done
"
echo
echo "PHASE 1 GREEN: gen/SlhVerify model type-checks. Proofs are the next layer."
