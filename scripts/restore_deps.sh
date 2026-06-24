#!/usr/bin/env bash
# SessionStart safety-net (wired up in .claude/settings.json).
#
# The cloud setup script provisions .lake/packages once and the filesystem is
# snapshotted -- but if a session ever starts with the repo working tree reset
# while $HOME persisted, .lake/packages can be missing. This hook restores it
# from the cached artifact under $HOME, with no network. It is a strict no-op
# when deps are already present (e.g. every local run) or no cache exists, and
# it never fails the session.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

_locate_deps_common() {
  [ -f "$SCRIPT_DIR/deps_common.sh" ] && { echo "$SCRIPT_DIR/deps_common.sh"; return 0; }
  [ -f "$PWD/scripts/deps_common.sh" ] && { echo "$PWD/scripts/deps_common.sh"; return 0; }
  local gr; gr="$(git rev-parse --show-toplevel 2>/dev/null)" && \
    [ -f "$gr/scripts/deps_common.sh" ] && { echo "$gr/scripts/deps_common.sh"; return 0; }
  for d in "$HOME/repo" "$HOME/workspace" "/workspace" "/repo" "/home/user/repo"; do
    [ -f "$d/scripts/deps_common.sh" ] && { echo "$d/scripts/deps_common.sh"; return 0; }
  done
  find /home /root /workspace /repo -maxdepth 6 \
    -name 'deps_common.sh' -path '*/scripts/deps_common.sh' 2>/dev/null | head -1
}

DEPS_COMMON="$(_locate_deps_common)"
# shellcheck source=scripts/deps_common.sh
[ -n "$DEPS_COMMON" ] && . "$DEPS_COMMON" 2>/dev/null || exit 0
ROOT="$(deps_repo_root)"

# Already warm? (covers all local runs -- your machine has a built .lake.)
if [ "$(deps_olean_count "$ROOT")" -ge 100 ]; then exit 0; fi

deps_read_lock "$ROOT/scripts/deps.lock"
ART_LOCAL="$HOME/.deps-cache/${DEPS_ARTIFACT:-}"
if [ -n "${DEPS_ARTIFACT:-}" ] && [ -f "$ART_LOCAL" ]; then
  echo "[restore_deps] .lake/packages missing; restoring from cached artifact..." >&2
  deps_extract "$ART_LOCAL" "$ROOT" 2>/dev/null || true
fi
exit 0
