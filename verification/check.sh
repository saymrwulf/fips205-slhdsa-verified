#!/usr/bin/env bash
# The one-button claim for this repository (rigor invariant R3).
# Green output == the full claim. This script is the ONLY source of the
# word "proven" for this repo.
#
#   Phase 0 — model-byte integrity: every gen/SlhVerify/*.lean must sha256-match
#             PROVENANCE.json (a hand-edited model fails BEFORE it is compiled;
#             round-4 review F3).
#   Phase 1 — compile the extracted Lean model (gen/SlhVerify).
#   Phase 2 — compile the proof files (Proofs/).
#   Phase 3 — the in-Lean audit (Proofs/Audit.lean): each certificate's cone
#             (via `collectAxioms`) must EQUAL its expected set exactly AND its
#             statement fingerprint must match the committed manifest, EVERY
#             theorem in the eight cert modules must have a cone within the
#             boundary (so an un-manifested `: False := cheat _` cannot pass —
#             round-4 F1), and this script binds to the printed MANIFEST
#             fingerprint (round-4 F2/F1). Any mismatch → non-zero exit →
#             fail-closed. No text parsing of axiom cones.
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

# ── Phase 0: model-byte integrity (gen/ == PROVENANCE.json) ──────────────────
echo "=== Phase 0: model-byte integrity (gen/ pinned to PROVENANCE.json) ==="
python3 - "$HERE/PROVENANCE.json" "$HERE" <<'PY' || { echo "MODEL INTEGRITY FAILED (a gen/ file differs from PROVENANCE.json — hand-edited model?)"; exit 1; }
import json, sys, hashlib, os
prov = json.load(open(sys.argv[1])); here = sys.argv[2]
files = {k: v for k, v in prov.get("model_integrity_sha256", {}).items() if k.startswith("gen/")}
if not files:
    print("  no model_integrity_sha256 in PROVENANCE.json (fail-closed)"); sys.exit(1)
bad = 0
for rel, want in sorted(files.items()):
    p = os.path.join(here, rel)
    if not os.path.exists(p):
        print(f"  ✗ {rel} MISSING"); bad = 1; continue
    got = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    if got != want:
        print(f"  ✗ {rel}: sha256 {got[:12]} ≠ pinned {want[:12]}"); bad = 1
    else:
        print(f"  ✓ {rel}")
sys.exit(1 if bad else 0)
PY

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

# ── Phase 3: in-Lean audit (cones + statements + full-module enumeration) ────
echo "=== Phase 3: in-Lean audit (cones + statement fingerprints + enumeration) ==="
cd "$AENEAS_LEAN"
# Proofs/Audit.lean checks: per-cert exact cone + statement fingerprint; every
# theorem in the eight cert modules has a clean cone (no un-manifested axiom
# smuggle); and it prints a MANIFEST-FINGERPRINT over the whole committed
# manifest. We bind to that EXACT fingerprint below, so deleting/swapping a cert
# row, or editing a cone or a statement fingerprint, changes the printed value
# and fails HERE even if Lean itself exits 0 (round-4 F1/F2 set+statement bind).
# To rotate the manifest deliberately, recompute it (compile Audit.lean, read the
# printed value) and update EXPECTED_MANIFEST_FP in the same reviewable commit.
EXPECTED_MANIFEST_FP="MANIFEST-FINGERPRINT: 13660980750615609973"
AUD_OUT=$(lake env bash -c "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' 'Proofs/Audit.lean'" 2>&1) || {
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (Audit.lean did not compile — cone/statement mismatch, missing cert, sham, or un-audited theorem)"; exit 1; }
if ! grep -qF "exact-cone audit PASSED" <<<"$AUD_OUT"; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (no PASSED line — fail-closed)"; exit 1
fi
if ! grep -qF "$EXPECTED_MANIFEST_FP" <<<"$AUD_OUT"; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED — manifest fingerprint mismatch."
  echo "  expected: $EXPECTED_MANIFEST_FP"
  echo "  the certificate set / a cone / a statement fingerprint changed without a reviewed manifest rotation."; exit 1
fi
echo "  ✓ $(grep -oF 'exact-cone audit PASSED' <<<"$AUD_OUT" | head -1) ($EXPECTED_MANIFEST_FP)"

echo
echo "ALL GREEN — model compiles, proofs compile, and every certificate cone"
echo "equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles."
echo "Certificates proven: ${CERTS[*]}"
