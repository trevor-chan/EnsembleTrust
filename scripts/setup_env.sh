#!/usr/bin/env bash
# Cloud-environment setup for the overnight Lean routine.
# Runs once per environment cache (then cached until this file changes), AFTER the
# repo is cloned and BEFORE Claude's session starts. CWD is the repo root.
#
# Its job: install the Lean toolchain and fetch prebuilt mathlib .olean files so
# the session never compiles mathlib from source. It FAILS LOUDLY if the oleans
# do not actually materialize -- a silent "warm" environment that is really empty
# is what burned us before (`lake exe cache get` exits 0 even on a 100% miss, so a
# broken fetch used to get cached as success).
set -euo pipefail

# 1. Install elan (Lean toolchain manager) unless the cache already has it.
if [ ! -x "$HOME/.elan/bin/lake" ] && ! command -v lake >/dev/null 2>&1; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
fi
export PATH="$HOME/.elan/bin:$PATH"

# 2. elan installs the exact Lean version from ./lean-toolchain on first use.
elan show >/dev/null 2>&1 || true

# 3. Select the cache backend. This mathlib version's default backend is the Azure
#    mirror (lakecache.blob.core.windows.net), which no longer serves oleans for
#    this pinned rev; point at the Cloudflare cache instead. The host must be on
#    the environment's network allowlist (mathlib4.lean-cache.cloud).
export MATHLIB_CACHE_GET_URL="https://mathlib4.lean-cache.cloud"

# Drop incomplete/error stubs from any prior failed run. A failed fetch leaves
# tiny .ltar.part files (404 / BlobNotFound bodies) that otherwise mask retries.
rm -f "$HOME/.cache/mathlib"/*.ltar.part 2>/dev/null || true

# 4. Pull prebuilt mathlib oleans. Do NOT trust the exit code (cache get returns 0
#    on a total miss) -- verify real oleans landed afterward.
lake exe cache get || true

# 5. Honesty gate: assert mathlib oleans are actually present. If not, fail so this
#    broken environment is NOT cached as "warm".
OLEAN_DIR=".lake/packages/mathlib/.lake/build/lib"
N_OLEAN=$(find "$OLEAN_DIR" -name '*.olean' 2>/dev/null | head -2000 | wc -l)
if [ "$N_OLEAN" -lt 100 ]; then
  echo "FATAL: mathlib cache fetch produced $N_OLEAN oleans (expected thousands)." >&2
  echo "  The environment is NOT warm; failing so the broken state is not cached." >&2
  echo "  Likely causes:" >&2
  echo "   (a) mathlib (and its dep repos) are not in the environment's source scope," >&2
  echo "       so 'lake' cannot git-clone them (git is gated by repo scope, not the" >&2
  echo "       network allowlist); or" >&2
  echo "   (b) MATHLIB_CACHE_GET_URL host is not allowlisted, or no longer serves" >&2
  echo "       oleans for this pinned mathlib rev (cache aged out)." >&2
  exit 1
fi
echo "OK: $N_OLEAN mathlib oleans present."

# 6. Warm the project build (cheap once mathlib oleans are present; surfaces issues
#    early). Left non-fatal: a project-level error is for the session to fix.
lake build || true

# 7. Make `lake` visible to the session shell (belt and suspenders).
LINE='export PATH="$HOME/.elan/bin:$PATH"'
[ -n "${CLAUDE_ENV_FILE:-}" ] && echo "$LINE" >> "$CLAUDE_ENV_FILE"
echo "$LINE" >> "$HOME/.bashrc"
echo "$LINE" >> "$HOME/.profile"
