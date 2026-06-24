#!/usr/bin/env bash
# Freeze the conjecture statement: (re)generate scripts/statement.sha256 from the
# current ConjectureProof/Statement.lean. Run this once after writing/editing the
# statement for a new problem; check_integrity.sh then verifies it is unchanged.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/deps_common.sh
. "$SCRIPT_DIR/deps_common.sh"
ROOT="$(deps_repo_root)"; cd "$ROOT"

STMT="ConjectureProof/Statement.lean"
[ -f "$STMT" ] || { echo "missing $STMT" >&2; exit 1; }
printf '%s  %s\n' "$(deps_sha256 "$STMT")" "$STMT" > "$SCRIPT_DIR/statement.sha256"
echo "Froze $STMT:"; cat "$SCRIPT_DIR/statement.sha256"
