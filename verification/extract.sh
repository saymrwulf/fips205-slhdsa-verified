#!/usr/bin/env bash
# Regenerate the Lean model in gen/ from the pinned fips205 snapshot.
#
# SCOPE: the SLH-DSA verify path, parameter set SLH-DSA-SHA2-128s
#   roots: slh_verify(_internal), fors_pk_from_sig, ht_verify,
#          xmss_pk_from_sig, wots_pk_from_sig, chain
#   (sign/keygen are out of scope; the six hash oracles are opaque —
#    see TRUSTED-BASE.md.)
#
#   Rust --charon--> SlhVerify.llbc --aeneas--> gen/SlhVerify/*.lean
#
# PHASE-1 PRECONDITION (gate-0 finding, 2026-07-22): upstream models the
# hash family as `crate::hashers::Hashers`, a struct of plain function
# pointers, which Aeneas cannot translate (3 unique errors, the only
# obstruction in the whole cone). Until the Aeneas-compat patch in
# fips205-source replaces that struct with named opaque free functions
# on the verify path (the curve25519-dalek-source sha512-shim pattern),
# this script produces a PARTIAL model. Do not build proofs on a partial
# model; check.sh stays non-green until extraction is clean.
#
# Usage:  ./extract.sh
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE=~/GitClone/FormalVerification/sources/fips205-source

echo "[1/2] charon: Rust -> LLBC (verify cone, SHA2-128s, hash oracles opaque)"
cd "$CRATE"
charon cargo --preset=aeneas \
  --start-from 'crate::slh::slh_verify' \
  --start-from 'crate::slh::slh_verify_internal' \
  --start-from 'crate::fors::fors_pk_from_sig' \
  --start-from 'crate::hypertree::ht_verify' \
  --start-from 'crate::xmss::xmss_pk_from_sig' \
  --start-from 'crate::wots::wots_pk_from_sig' \
  --start-from 'crate::wots::chain' \
  --opaque 'sha2' --opaque 'sha3' --opaque 'zeroize' --opaque 'rand_core' \
  --opaque 'crate::hashers::sha2_cat_1' \
  --opaque 'crate::hashers::sha2_cat_3_5' \
  --opaque 'crate::hashers::shake' \
  --hide-marker-traits \
  --dest-file "$HERE/SlhVerify.llbc" \
  -- --no-default-features --features slh_dsa_sha2_128s

echo "[2/2] aeneas: LLBC -> Lean (split files, SlhVerify.* modules;"
echo "        hand-maintained TypesExternal.lean / FunsExternal.lean are"
echo "        NOT overwritten once they exist)"
cd "$HERE"
aeneas -backend lean -split-files -subdir SlhVerify -dest gen SlhVerify.llbc

echo "Done. Now run ./check.sh (expect non-green until phase 1 lands)."
