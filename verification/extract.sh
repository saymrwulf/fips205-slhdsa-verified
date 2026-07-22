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
# HISTORY (gate-0 finding, resolved 2026-07-22): upstream models the hash
# family as `crate::hashers::Hashers`, a struct of plain function pointers,
# which Aeneas cannot translate. The compat patch in fips205-source
# (>= 2d89ee3) provides the additive monomorphic verify_mono module whose
# hash suite is reached through named free functions — this script roots
# there, and charon + aeneas both exit 0. Regeneration is byte-identical
# (verified against the committed gen/ during the 2026-07-22 audit).
#
# Usage:  ./extract.sh
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE=~/GitClone/FormalVerification/sources/fips205-source

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
