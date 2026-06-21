#!/usr/bin/env bash
# Runs ONCE per environment cache (then cached for ~7 days). Installs Lean +
# the prebuilt mathlib cache so each nightly run starts warm.
set -euo pipefail

# Install elan (Lean toolchain manager) only if not already cached.
if ! command -v lake >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
fi
export PATH="$HOME/.elan/bin:$PATH"

# elan reads ./lean-toolchain to install the exact Lean version mathlib needs.
elan show >/dev/null 2>&1 || true

# Pull prebuilt mathlib .olean files (minutes) instead of compiling (hours).
lake exe cache get || true

# Warm the build so nightly runs don't pay full cost.
lake build || true

# Persist PATH for the agent's subsequent Bash commands in this session.
echo "PATH=$HOME/.elan/bin:\$PATH" >> "$CLAUDE_ENV_FILE"
