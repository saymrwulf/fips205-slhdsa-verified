#!/usr/bin/env bash
# The one-button claim for this repository (rigor invariant R3).
# Green output == the full claim. This script is the ONLY source of the
# word "proven" for this repo.
#
#   Phase 0 — build hygiene + integrity: purge stale .olean (the verdict must
#             depend on committed bytes, not untracked build state), forbid any
#             .lean outside gen/ and Proofs/, and sha256-pin the four model files
#             AND the compiler harness `lean-guard` to PROVENANCE.json.
#   Phase 1 — compile the extracted Lean model (gen/SlhVerify).
#   Phase 2 — compile the proof files (Proofs/).
#   Phase 3 — the in-Lean audit (Proofs/Audit.lean): per certificate, the cone
#             (via `collectAxioms`) must EQUAL its expected set exactly; EVERY
#             declaration kind in the eight cert modules and in Audit.lean itself
#             must stay within the axiom boundary; and this script binds to the
#             SHA-256 of the canonical AUDIT-MANIFEST block, which covers the
#             POLICY constants, every certificate STATEMENT, and every reachable
#             SPECIFICATION DEFINITION BODY. Any mismatch → non-zero exit →
#             fail-closed. No text parsing of axiom cones.
#
#   What this button does NOT bind is stated in TRUSTED-BASE.md item 11: this
#   script itself, the toolchain env, $AENEAS_HOME, and the Lean toolchain.
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
echo "fips205-slhdsa-verified — check"
echo "==============================="

# ── Phase 0: build hygiene + model & harness integrity ───────────────────────
echo "=== Phase 0: build hygiene + model/harness integrity ==="
# (a) Purge EVERY .olean under verification/ — round-6 NEW-8: the round-5 purge
#     covered only gen/ and Proofs/ while the stray check greped only *.lean, so
#     an ORPHAN `verification/Evil.olean` WITH NO SOURCE AT ALL fell between them,
#     satisfied an `import Evil`, and went ALL GREEN with the digest untouched
#     (*.olean is .gitignored, so `git status` showed only the import line).
#     The verdict must depend on COMMITTED BYTES, never on untracked build state.
find "$HERE" -name '*.olean' -delete 2>/dev/null || true
#     Aeneas also emits `*_Template.lean` scaffolding into gen/ on every
#     extraction. Those files are UNTRACKED byproducts (a fresh clone has only
#     the four pinned model files), nothing imports them, and they would
#     otherwise sit on LEAN_PATH unpinned — the same untracked-state problem.
#     Remove them here so the gen/ file-set assertion below can be exact.
find "$HERE/gen" -name '*_Template.lean' -delete 2>/dev/null || true
# (b) No Lean source OR compiled module may sit outside gen/ and Proofs/;
#     LEAN_PATH includes $PWD, so either can join the environment ungated.
STRAY=$(find "$HERE" -maxdepth 1 \( -name '*.lean' -o -name '*.olean' \) -printf '%f\n' 2>/dev/null || true)
if [ -n "$STRAY" ]; then
  echo "$STRAY" | sed 's/^/  ✗ stray Lean file outside gen\/ and Proofs\/: /'
  echo "BUILD HYGIENE FAILED (a .lean/.olean outside the audited directories can join LEAN_PATH)"; exit 1
fi
# (c) sha256-pin the extracted model AND the compiler harness. lean-guard is
#     repo-tracked and is shelled out to for every compile, so it is part of the
#     trusted computing base: round 5 demonstrated that stubbing it alone yields
#     ALL GREEN in 3.6s over destroyed proofs. It is KEPT (it is the memory cap
#     that protects this machine after the 12.2GB OOM incident) and pinned.
python3 - "$HERE/PROVENANCE.json" "$HERE" <<'PY' || { echo "INTEGRITY FAILED (a pinned file differs from PROVENANCE.json — hand-edited model or harness?)"; exit 1; }
import json, sys, hashlib, os
prov = json.load(open(sys.argv[1])); here = sys.argv[2]
files = {k: v for k, v in prov.get("model_integrity_sha256", {}).items() if not k.startswith("_")}
files.update({k: v for k, v in prov.get("harness_integrity_sha256", {}).items() if not k.startswith("_")})
if not files:
    print("  no integrity map in PROVENANCE.json (fail-closed)"); sys.exit(1)
bad = 0
# WHICH files must be pinned is policy, and policy belongs in the root of trust —
# not in the map being consulted. Round-6 review (NEW-13) demonstrated the gap:
# PROVENANCE.json is a tracked file that nothing pins, and the only completeness
# test was `if not files`, so deleting the whole `harness_integrity_sha256` key
# silently un-pinned BOTH lean-guard and Proofs/Audit.lean with no diagnostic —
# after which the round-6 NEW-7 logic mutation ran to ALL GREEN over a repository
# proving False, digest byte-identical. The model side self-protected only
# because the gen/ set assertion below derives its requirement from the
# filesystem; the harness side had no such cross-check.
REQUIRED = {
    "lean-guard", "Proofs/Audit.lean",
    "gen/SlhVerify/Types.lean", "gen/SlhVerify/Funs.lean",
    "gen/SlhVerify/TypesExternal.lean", "gen/SlhVerify/FunsExternal.lean",
}
missing = REQUIRED - set(files)
if missing:
    for m in sorted(missing):
        print(f"  ✗ pin map INCOMPLETE — no entry for {m}")
    bad = 1
for rel, want in sorted(files.items()):
    p = os.path.join(here, rel)
    if not os.path.exists(p):
        print(f"  ✗ {rel} MISSING"); bad = 1; continue
    got = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    if got != want:
        print(f"  ✗ {rel}: sha256 {got[:12]} ≠ pinned {want[:12]}"); bad = 1
    else:
        print(f"  ✓ {rel}")
# Round-6 NEW-9: pin gen/ as a SET, not as four names. A new file under gen/ was
# neither hashed nor forbidden, while LEAN_PATH contains $PWD/gen — so the
# closure's premise ("everything outside certModules is pinned or disclosed")
# was not enforced. Any .lean under gen/ must appear in the pin map.
pinned_gen = {k for k in files if k.startswith("gen/")}
actual_gen = set()
for root, _, names in os.walk(os.path.join(here, "gen")):
    for n in names:
        if n.endswith(".lean"):
            actual_gen.add(os.path.relpath(os.path.join(root, n), here))
for extra in sorted(actual_gen - pinned_gen):
    print(f"  ✗ UNPINNED model file under gen/: {extra}"); bad = 1
for missing in sorted(pinned_gen - actual_gen):
    print(f"  ✗ pinned model file absent: {missing}"); bad = 1
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
# THE BINDING DIGEST. Audit.lean emits a canonical AUDIT-MANIFEST block holding
# the POLICY constants (allowedBoundary, certModules — round-5 NEW-1), every
# certificate's fully-elaborated STATEMENT, and every reachable SPECIFICATION
# definition's fully-elaborated BODY (round-5 NEW-2: redefining a reference fold
# to *be* the extracted loop previously left every fingerprint intact). We bind
# to the SHA-256 of that block, retiring the 32-bit Expr.hash as the load-bearing
# digest (NEW-5). To rotate deliberately: run check.sh, take the printed OBSERVED
# digest, and update this constant in the same reviewable commit.
EXPECTED_AUDIT_SHA256="d83e297a49094c970b88ce7c63ceb85d6bee0764d4623456a7225860e2298afa"
AUD_OUT=$(lake env bash -c "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD/gen:\$PWD\" && LEAN_TIMEOUT=$TIMEOUT LEAN_MEM_MB=$MEM '$HERE/lean-guard' 'Proofs/Audit.lean'" 2>&1) || {
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (Audit.lean did not compile — cone/statement mismatch, missing cert, sham, or un-audited declaration)"; exit 1; }
if ! grep -qF "exact-cone audit PASSED" <<<"$AUD_OUT"; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (no PASSED line — fail-closed)"; exit 1
fi
BLOCK=$(awk '/AUDIT-MANIFEST-BEGIN/{f=1;next} /AUDIT-MANIFEST-END/{f=0} f' <<<"$AUD_OUT")
if [ -z "$BLOCK" ]; then
  echo "$AUD_OUT" | sed 's/^/  /'
  echo "AUDIT FAILED (no AUDIT-MANIFEST block — fail-closed)"; exit 1
fi
GOT_SHA=$(printf '%s\n' "$BLOCK" | sha256sum | cut -d' ' -f1)
if [ "$GOT_SHA" != "$EXPECTED_AUDIT_SHA256" ]; then
  printf '%s\n' "$BLOCK" > "$HERE/.audit-manifest.observed"
  echo "AUDIT FAILED — audit-manifest digest mismatch."
  echo "  expected: $EXPECTED_AUDIT_SHA256"
  echo "  observed: $GOT_SHA"
  echo "  A policy constant, a certificate statement, or a specification"
  echo "  definition changed without a reviewed rotation."
  echo "  What moved (committed block vs observed):"
  diff -u "$HERE/AUDIT-MANIFEST.txt" "$HERE/.audit-manifest.observed" 2>/dev/null \
    | head -40 | sed 's/^/    /' || echo "    (AUDIT-MANIFEST.txt absent — cannot diff)"
  exit 1
fi
# The digest's INPUT is committed too (round-6: a mismatch previously wrote an
# observed block with nothing to diff it against). Guard against the committed
# copy drifting from what Lean actually emits.
if ! printf '%s\n' "$BLOCK" | cmp -s - "$HERE/AUDIT-MANIFEST.txt"; then
  echo "AUDIT FAILED — the committed AUDIT-MANIFEST.txt does not match the emitted block"
  echo "  (digest matched, so this means the committed copy is stale — refresh it)"; exit 1
fi
echo "  ✓ $(grep -oF 'exact-cone audit PASSED' <<<"$AUD_OUT" | head -1)"
echo "  ✓ audit-manifest digest matches (sha256 ${EXPECTED_AUDIT_SHA256:0:16}…)"

echo
echo "ALL GREEN — model compiles, proofs compile, and every certificate cone"
echo "equals EXACTLY the three kernel axioms plus its documented SHA-2 oracles."
# The list comes from the AUDITED manifest itself, never from a hand-kept array:
# a display list nothing binds can name a certificate that does not exist.
CERT_LINE=$(sed -n 's/.*CERTIFICATES: //p' <<<"$AUD_OUT" | head -1)
[ -n "$CERT_LINE" ] || { echo "AUDIT FAILED (no CERTIFICATES line — fail-closed)"; exit 1; }
echo "Certificates proven: $CERT_LINE"
