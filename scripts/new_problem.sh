#!/usr/bin/env bash
# Reset the problem-specific Lean files to a fresh skeleton for a NEW conjecture.
# Keeps the fixed `ConjectureProof` library/namespace (see SKELETON.md to rename).
#
# Usage:  scripts/new_problem.sh <short-name> [--no-archive]
#
# By default the current problem's Statement/Lemmas/Main + PROGRESS are copied to
# archive/<short-name>/ before being overwritten with the templates.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/deps_common.sh
. "$SCRIPT_DIR/deps_common.sh"
ROOT="$(deps_repo_root)"; cd "$ROOT"
T="$SCRIPT_DIR/templates"

ARCHIVE=1; NAME=""
while [ $# -gt 0 ]; do
  case "$1" in
    --no-archive) ARCHIVE=0 ;;
    -*) echo "unknown flag: $1" >&2; exit 2 ;;
    *) NAME="$1" ;;
  esac; shift
done
[ -n "$NAME" ] || { echo "usage: new_problem.sh <short-name> [--no-archive]" >&2; exit 2; }

if [ "$ARCHIVE" = 1 ]; then
  dest="archive/$NAME"; mkdir -p "$dest"
  cp ConjectureProof/Statement.lean ConjectureProof/Lemmas.lean ConjectureProof/Main.lean "$dest/" 2>/dev/null || true
  cp blueprint/PROGRESS.md "$dest/" 2>/dev/null || true
  echo "Archived current problem under $dest/"
fi

cp "$T/Statement.lean.template" ConjectureProof/Statement.lean
cp "$T/Lemmas.lean.template"    ConjectureProof/Lemmas.lean
cp "$T/Main.lean.template"      ConjectureProof/Main.lean
cp "$T/PROGRESS.md.template"    blueprint/PROGRESS.md
echo "Reset Statement/Lemmas/Main + PROGRESS to the skeleton."
echo
echo "Next steps:"
echo "  1. Edit ConjectureProof/Statement.lean to state MainProp (your conjecture)."
echo "  2. bash scripts/freeze_statement.sh           # freeze the statement checksum"
echo "  3. bash scripts/bootstrap_deps.sh --bump-latest   # build + publish deps (run locally)"
echo "  4. Commit, then point the routine at this branch."
