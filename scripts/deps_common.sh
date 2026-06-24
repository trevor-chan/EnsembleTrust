#!/usr/bin/env bash
# Shared helpers for provisioning the pinned Lean/mathlib dependency artifact.
# Sourced by setup_env.sh (cloud setup script) and restore_deps.sh (SessionStart
# hook). Intentionally tolerant -- the caller decides what is fatal.

# Repo root = parent of the directory holding this file.
deps_repo_root() {
  cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd
}

# Load scripts/deps.lock key=values into the environment (safe no-op if absent).
deps_read_lock() {
  local lock="$1"
  LEAN_TOOLCHAIN=""; MATHLIB_REV=""; DEPS_REPO=""
  DEPS_RELEASE_TAG=""; DEPS_ARTIFACT=""; DEPS_ARTIFACT_SHA256=""; DEPS_ARTIFACT_PARTS="1"
  [ -f "$lock" ] || return 0
  # shellcheck disable=SC1090
  set -a; . "$lock"; set +a
}

# How many mathlib oleans are present (the "is the environment warm?" signal).
deps_olean_count() {
  local root="$1"
  find "$root/.lake/packages/mathlib/.lake/build/lib" -name '*.olean' 2>/dev/null \
    | head -2000 | wc -l | tr -d ' '
}

deps_have_zstd() { command -v zstd >/dev/null 2>&1; }

# Portable sha256 of a file -> stdout (Linux sha256sum, macOS shasum -a 256).
deps_sha256() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  else shasum -a 256 "$1" | awk '{print $1}'; fi
}

# Extract a .tar.zst artifact (containing a top-level `packages/` dir) into
# <root>/.lake, i.e. restoring <root>/.lake/packages/...
deps_extract() {
  local art="$1" root="$2"
  mkdir -p "$root/.lake"
  if deps_have_zstd; then
    zstd -dc "$art" | tar -x -C "$root/.lake"
  else
    tar --zstd -xf "$art" -C "$root/.lake"
  fi
}

# Download the (possibly split) release asset into <cachedir>, reassemble to
# <out>, and verify the sha256 from deps.lock. Uses DEPS_* vars + GITHUB_TOKEN.
deps_download_artifact() {
  local cachedir="$1" out="$2"
  mkdir -p "$cachedir"
  local base="https://github.com/${DEPS_REPO}/releases/download/${DEPS_RELEASE_TAG}"
  local auth=(); [ -n "${GITHUB_TOKEN:-}" ] && auth=(-H "Authorization: Bearer ${GITHUB_TOKEN}")
  local n="${DEPS_ARTIFACT_PARTS:-1}"
  if [ "${n:-1}" -le 1 ]; then
    curl -fSL "${auth[@]}" "${base}/${DEPS_ARTIFACT}" -o "$out"
  else
    local i p
    for ((i=0; i<n; i++)); do
      printf -v p "%s.part%02d" "$DEPS_ARTIFACT" "$i"
      curl -fSL "${auth[@]}" "${base}/${p}" -o "${cachedir}/${p}"
    done
    cat "${cachedir}/${DEPS_ARTIFACT}".part* > "$out"
  fi
  if [ -n "${DEPS_ARTIFACT_SHA256:-}" ]; then
    local got; got="$(deps_sha256 "$out")"
    if [ "$got" != "$DEPS_ARTIFACT_SHA256" ]; then
      echo "deps: sha256 mismatch ($got != $DEPS_ARTIFACT_SHA256)" >&2; return 1
    fi
  fi
}
