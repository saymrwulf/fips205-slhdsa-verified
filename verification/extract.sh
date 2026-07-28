#!/usr/bin/env bash
# Regenerate the Lean model in gen/ from the pinned fips205 snapshot.
#
# SCOPE: the SLH-DSA verify path, parameter set SLH-DSA-SHA2-128s
#   roots: slh_verify(_internal), fors_pk_from_sig, ht_verify,
#          xmss_pk_from_sig, wots_pk_from_sig, chain
#   (sign/keygen are out of scope; the five verify-path hash oracles
#    (h_msg, f, h, t_l, t_len) are opaque — see TRUSTED-BASE.md.)
#
#   Rust --charon--> SlhVerify.llbc --aeneas--> gen/SlhVerify/*.lean
#
# REPRODUCIBILITY (external review round 2, 2026-07-24): this script now
# REFUSES to extract from a source tree that is not at the pinned commit or
# is dirty (a wrong/uncommitted source would silently produce a different
# model). The full pin set (source + charon + aeneas + lean + ocaml) is in
# verification/PROVENANCE.json; re-running this against the pinned tree
# reproduces gen/SlhVerify/{Types,Funs}.lean byte-identically.
#
# HISTORY (gate-0 finding, resolved 2026-07-22): upstream models the hash
# family as `crate::hashers::Hashers`, a struct of plain function pointers,
# which Aeneas cannot translate. The compat patch in fips205-source provides
# the additive monomorphic verify_mono module whose hash suite is reached
# through named free functions — this script roots there.
#
# Usage:  ./extract.sh [PATH_TO_fips205-source]
#           (default: ~/GitClone/FormalVerification/sources/fips205-source)
#         Override the required commit only for a deliberate re-pin:
#           EXPECTED_SRC_COMMIT=<full-sha> ./extract.sh [PATH]
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE="${1:-$HOME/GitClone/FormalVerification/sources/fips205-source}"

# The pinned source commit this repo's model + proofs were verified against.
# Keep in lockstep with verification/PROVENANCE.json and the README snapshot.
EXPECTED_SRC_COMMIT="${EXPECTED_SRC_COMMIT:-3153988c4e89df66c41e698329f2ae5460880875}"

# ── Provenance guard: refuse a wrong or dirty source tree (fail-closed) ──────
[ -d "$CRATE/.git" ] || { echo "ERROR: '$CRATE' is not a git checkout of fips205-source." >&2; exit 2; }
GOT_COMMIT="$(git -C "$CRATE" rev-parse HEAD)"
if [ "$GOT_COMMIT" != "$EXPECTED_SRC_COMMIT" ]; then
  echo "ERROR: source is at ${GOT_COMMIT:0:12}, but this repo is pinned to" >&2
  echo "       ${EXPECTED_SRC_COMMIT:0:12}. Check out the pin, or set" >&2
  echo "       EXPECTED_SRC_COMMIT=<sha> for a deliberate re-pin." >&2
  exit 3
fi
if [ -n "$(git -C "$CRATE" status --porcelain)" ]; then
  echo "ERROR: source tree at '$CRATE' is dirty. Extraction must run against" >&2
  echo "       a clean, committed tree so the model is reproducible." >&2
  git -C "$CRATE" status --porcelain | sed 's/^/         /' >&2
  exit 4
fi
echo "[0/2] provenance OK: fips205-source @ ${EXPECTED_SRC_COMMIT:0:12} (clean)"

# Toolchain env is sourced only AFTER the provenance guard, so a party without
# the aeneas toolchain still gets the clean exit-2/3/4 diagnostics above
# (round-3 reviewer nit, 2026-07-24).
source ~/aeneas-toolchain/env.sh

echo "[1/2] charon: Rust -> LLBC (monomorphic SHA2-128s verify cone;"
echo "        crate::verify_mono::oracle is the opaque SHA-2 boundary)"
cd "$CRATE"
# Single extraction root: the monomorphic entry. The five hash primitives
# are reached through crate::verify_mono::oracle, marked opaque here — this
# is the deliberate SHA-2 trust boundary (documented in TRUSTED-BASE.md).
# The generic Hashers fn-pointer path is NOT in this cone by construction.
charon cargo --preset=aeneas \
  --start-from 'crate::verify_mono::slh_verify_128s' \
  --opaque 'crate::verify_mono::oracle' \
  --opaque 'sha2' --opaque 'sha3' --opaque 'zeroize' --opaque 'rand_core' \
  --hide-marker-traits \
  --dest-file "$HERE/SlhVerify.llbc" \
  -- --no-default-features --features slh_dsa_sha2_128s

echo "[2/2] aeneas: LLBC -> Lean (split files, SlhVerify.* modules;"
echo "        hand-maintained TypesExternal.lean / FunsExternal.lean are"
echo "        NOT overwritten once they exist)"
cd "$HERE"
aeneas -backend lean -split-files -subdir SlhVerify -dest gen SlhVerify.llbc

echo "Done. Now run ./check.sh (Phase 1: the regenerated model must type-check)."
