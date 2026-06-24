#!/usr/bin/env bash
# Cloud-environment setup script. Runs once per environment cache (AFTER the repo
# is cloned, BEFORE Claude's session starts); the resulting filesystem is then
# snapshotted, so later sessions start warm and this does not re-run.
#
# Job: install the Lean toolchain and provision a complete .lake/packages (source
# + prebuilt oleans) so the session never compiles mathlib. Two provisioning
# paths, in order of preference:
#   1. Restore the pinned dependency artifact published to a GitHub Release
#      (scripts/deps.lock) -- durable, immune to upstream cache GC / git scope.
#   2. Fall back to the upstream mathlib olean cache (works until the pinned rev
#      is GC'd) when no artifact is pinned yet.
# Either way it FAILS LOUDLY if oleans do not actually materialize, so a broken
# (empty) environment is never snapshotted as "warm".
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/deps_common.sh
. "$SCRIPT_DIR/deps_common.sh"
ROOT="$(deps_repo_root)"; cd "$ROOT"

# 1. elan + the toolchain pinned in ./lean-toolchain (elan fetches from
#    *.lean-lang.org -- keep that host on the network allowlist).
if [ ! -x "$HOME/.elan/bin/lake" ] && ! command -v lake >/dev/null 2>&1; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
fi
export PATH="$HOME/.elan/bin:$PATH"
elan show >/dev/null 2>&1 || true

# zstd is needed to unpack the dependency artifact.
deps_have_zstd || { apt-get update -y && apt-get install -y zstd; } || true

deps_read_lock "$SCRIPT_DIR/deps.lock"
CACHE_HOME="$HOME/.deps-cache"
ART_LOCAL="$CACHE_HOME/${DEPS_ARTIFACT:-lake-packages.tar.zst}"

restored=0
# 2. Preferred: restore the pinned release artifact into .lake/packages, keeping
#    a copy under $HOME (persists across the snapshot) for the SessionStart net.
if [ -n "${DEPS_RELEASE_TAG:-}" ] && [ -n "${DEPS_ARTIFACT:-}" ]; then
  echo "Provisioning deps from release ${DEPS_REPO}@${DEPS_RELEASE_TAG} (${DEPS_ARTIFACT})..."
  if deps_download_artifact "$CACHE_HOME" "$ART_LOCAL" && deps_extract "$ART_LOCAL" "$ROOT"; then
    restored=1
  else
    echo "WARN: release-asset restore failed; falling back to upstream cache." >&2
  fi
fi

# 3. Fallback: upstream mathlib olean cache (Cloudflare; the Azure default no
#    longer serves this pinned rev).
if [ "$restored" != 1 ]; then
  export MATHLIB_CACHE_GET_URL="${MATHLIB_CACHE_GET_URL:-https://mathlib4.lean-cache.cloud}"
  rm -f "$HOME/.cache/mathlib"/*.ltar.part 2>/dev/null || true
  lake exe cache get || true   # exits 0 even on a total miss -- assert below
fi

# 4. Honesty gate: real oleans must be present, else fail so the broken state is
#    not cached.
N_OLEAN="$(deps_olean_count "$ROOT")"
if [ "${N_OLEAN:-0}" -lt 100 ]; then
  echo "FATAL: only ${N_OLEAN:-0} mathlib oleans present after provisioning." >&2
  echo "  - If using a pinned artifact: check scripts/deps.lock (tag/sha/parts) and" >&2
  echo "    that the release asset exists and is reachable from this environment." >&2
  echo "  - If using the upstream-cache fallback: the pinned rev may have been GC'd." >&2
  echo "    Run scripts/bootstrap_deps.sh locally to publish your own artifact." >&2
  exit 1
fi
echo "OK: ${N_OLEAN} mathlib oleans present."

# 5. Warm the project build (cheap once oleans are present). Non-fatal: a
#    project-level error is for the session to fix, not setup.
lake build || true

# 6. Make lake visible to the session shell.
LINE='export PATH="$HOME/.elan/bin:$PATH"'
[ -n "${CLAUDE_ENV_FILE:-}" ] && echo "$LINE" >> "$CLAUDE_ENV_FILE"
echo "$LINE" >> "$HOME/.bashrc" 2>/dev/null || true
echo "$LINE" >> "$HOME/.profile" 2>/dev/null || true
