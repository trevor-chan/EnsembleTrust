#!/usr/bin/env bash
# Runs once per environment cache. Installs elan + warms the prebuilt mathlib
# download cache (~/.cache/mathlib) so each session's `lake exe cache get` is a
# fast local unpack instead of a from-source rebuild. NO `lake build` here —
# building is left to the session, where there is no ~5-minute setup ceiling.
set -euo pipefail

# Install elan (Lean toolchain manager) only if the cache doesn't already have it.
if ! command -v lake >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
fi
export PATH="$HOME/.elan/bin:$PATH"

# Install the exact toolchain pinned in ./lean-toolchain (no-op if already present).
elan show >/dev/null 2>&1 || true

# Warm the mathlib cache (download + decompress). Let it fail loudly: a broken
# cache fetch means the environment is broken, and we want to see that.
lake exe cache get

# Persist PATH for the agent's subsequent Bash commands in this session.
echo "PATH=$HOME/.elan/bin:\$PATH" >> "$CLAUDE_ENV_FILE"
