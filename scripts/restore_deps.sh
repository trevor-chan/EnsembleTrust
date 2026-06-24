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
# shellcheck source=scripts/deps_common.sh
. "$SCRIPT_DIR/deps_common.sh" 2>/dev/null || exit 0
ROOT="$(deps_repo_root)"

# Already warm? (covers all local runs -- your machine has a built .lake.)
if [ "$(deps_olean_count "$ROOT")" -ge 100 ]; then exit 0; fi

deps_read_lock "$SCRIPT_DIR/deps.lock"
ART_LOCAL="$HOME/.deps-cache/${DEPS_ARTIFACT:-}"
if [ -n "${DEPS_ARTIFACT:-}" ] && [ -f "$ART_LOCAL" ]; then
  echo "[restore_deps] .lake/packages missing; restoring from cached artifact..." >&2
  deps_extract "$ART_LOCAL" "$ROOT" 2>/dev/null || true
fi
exit 0
