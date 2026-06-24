#!/usr/bin/env bash
# Build the pinned Lean/mathlib dependency snapshot and publish it as a GitHub
# Release asset, then record it in scripts/deps.lock.
#
# Run this LOCALLY (or in a full-network environment) -- NOT in the restricted
# routine environment. It needs a working build and outbound network.
# Requires: lake (elan), zstd, gh (authenticated), tar, curl.
#
# Usage:
#   scripts/bootstrap_deps.sh                 # snapshot the CURRENT pinned deps
#   scripts/bootstrap_deps.sh --bump-latest   # `lake update` to latest mathlib first
#   scripts/bootstrap_deps.sh --tag deps-foo --repo owner/name
#
# Typical flow for a NEW problem: --bump-latest, confirm a green build, publish,
# then commit deps.lock + lean-toolchain + lakefile.toml + lake-manifest.json.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/deps_common.sh
. "$SCRIPT_DIR/deps_common.sh"
ROOT="$(deps_repo_root)"; cd "$ROOT"

BUMP=0; TAG=""; REPO=""
while [ $# -gt 0 ]; do
  case "$1" in
    --bump-latest) BUMP=1 ;;
    --tag)  TAG="$2";  shift ;;
    --repo) REPO="$2"; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac; shift
done

command -v lake >/dev/null || { echo "lake not found (install elan + toolchain)." >&2; exit 1; }
command -v zstd >/dev/null || { echo "zstd required." >&2; exit 1; }
command -v gh   >/dev/null || { echo "gh (GitHub CLI), authenticated, required." >&2; exit 1; }

if [ "$BUMP" = 1 ]; then
  echo ">> Bumping mathlib to latest (lake update)..."
  lake update
fi

echo ">> Fetching/building dependencies (this is the snapshot we publish)..."
lake exe cache get || true
lake build          # MUST succeed: we publish exactly what this produced

LEAN_TOOLCHAIN="$(cat lean-toolchain)"
MATHLIB_REV="$(python3 -c 'import json,sys; print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"]=="mathlib"))')"
[ -n "$REPO" ] || REPO="$(gh repo view --json nameWithOwner -q .nameWithOwner)"
VER_TAG="${LEAN_TOOLCHAIN##*:}"
[ -n "$TAG" ] || TAG="deps-${VER_TAG}"
ART="lake-packages-${VER_TAG}.tar.zst"

echo ">> Packing .lake/packages -> ${ART} ..."
tar -C .lake -cf - packages | zstd -19 -T0 -o "/tmp/${ART}"
SHA="$(deps_sha256 "/tmp/${ART}")"
SZ="$(wc -c < "/tmp/${ART}")"
echo "   size=${SZ} bytes  sha256=${SHA}"

# GitHub release assets cap at 2 GB; split above ~1.9 GB.
LIMIT=$((1900 * 1024 * 1024)); PARTS=1; ASSETS=("/tmp/${ART}")
if [ "$SZ" -gt "$LIMIT" ]; then
  ( cd /tmp && rm -f "${ART}.part"* && split -b 1900m -d -a 2 "${ART}" "${ART}.part" )
  ASSETS=(); for f in /tmp/"${ART}".part*; do ASSETS+=("$f"); done
  PARTS=${#ASSETS[@]}
  echo "   split into ${PARTS} parts"
fi

echo ">> Publishing release ${TAG} on ${REPO} ..."
if gh release view "$TAG" --repo "$REPO" >/dev/null 2>&1; then
  gh release upload "$TAG" "${ASSETS[@]}" --repo "$REPO" --clobber
else
  gh release create "$TAG" "${ASSETS[@]}" --repo "$REPO" \
    --title "Lean deps ${VER_TAG}" \
    --notes "Prebuilt .lake/packages for ${LEAN_TOOLCHAIN}, mathlib ${MATHLIB_REV}. Restored by scripts/setup_env.sh."
fi

cat > "$SCRIPT_DIR/deps.lock" <<EOF
# Pinned Lean/mathlib dependency artifact. Written by scripts/bootstrap_deps.sh.
# scripts/setup_env.sh restores the release asset named here on cloud startup.
LEAN_TOOLCHAIN=${LEAN_TOOLCHAIN}
MATHLIB_REV=${MATHLIB_REV}
DEPS_REPO=${REPO}
DEPS_RELEASE_TAG=${TAG}
DEPS_ARTIFACT=${ART}
DEPS_ARTIFACT_SHA256=${SHA}
DEPS_ARTIFACT_PARTS=${PARTS}
EOF

echo ">> Wrote ${SCRIPT_DIR}/deps.lock. Commit the pin:"
echo "   git add scripts/deps.lock lean-toolchain lakefile.toml lake-manifest.json"
echo "   git commit -m 'Pin deps ${VER_TAG}' && git push"
