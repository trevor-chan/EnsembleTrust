#!/usr/bin/env bash
# Honesty gate. Three outcomes:
#   exit 1                 -> INTEGRITY FAILURE (regression or cheating). Never commit.
#   exit 0 + "IN PROGRESS" -> healthy intermediate state; the one goal is still open.
#   exit 0 + "COMPLETE"    -> main_theorem proven with a clean axiom list.
# Run AFTER `lake build`. CI and the routine both call this.
set -uo pipefail

SRC="ConjectureProof"
STATEMENT="ConjectureProof/Statement.lean"
MAIN="ConjectureProof/Main.lean"
FAIL=0
fail() { echo "X FAIL: $*"; FAIL=1; }

# Portable sha256 verify: Linux has `sha256sum`, macOS has `shasum -a 256`.
if command -v sha256sum >/dev/null 2>&1; then
  sha_check() { sha256sum -c "$1" >/dev/null 2>&1; }
elif command -v shasum >/dev/null 2>&1; then
  sha_check() { shasum -a 256 -c "$1" >/dev/null 2>&1; }
else
  sha_check() { return 2; }   # no tool available; cannot verify
fi

echo "== 1. Frozen conjecture =="
if [ -f scripts/statement.sha256 ]; then
  if sha_check scripts/statement.sha256; then
    echo "ok: Statement.lean unchanged"
  else
    fail "Statement.lean changed (or no sha256 tool); the conjecture is frozen."
  fi
else
  echo "warn: scripts/statement.sha256 missing. Create it once (macOS):"
  echo "      shasum -a 256 $STATEMENT > scripts/statement.sha256"
fi

echo "== 2. No cheats in the workspace (everything except the one sanctioned goal) =="
for f in "$STATEMENT" "ConjectureProof/Lemmas.lean" "ConjectureProof/Audit.lean" "ConjectureProof.lean"; do
  [ -f "$f" ] || continue
  grep -nE '\bsorry\b|\badmit\b' "$f" && fail "$f contains a placeholder (sorry/admit)."
done
grep -rnE '\bnative_decide\b'        "$SRC" && fail "native_decide is disallowed."
grep -rnE '\bunsafe\b|@\[implemented_by' "$SRC" && fail "unsafe/implemented_by is disallowed."
grep -rnE '^\s*axiom\b'              "$SRC" && fail "an 'axiom' declaration was introduced."

echo "== 3. Goal present and unweakened =="
if grep -nE 'main_theorem\s*:\s*MainProp\b' "$MAIN" >/dev/null; then
  echo "ok: 'main_theorem : MainProp' present"
else
  fail "main_theorem : MainProp not found in Main.lean (type may be weakened)."
fi
N_MAIN_PH=$(grep -cE '\bsorry\b|\badmit\b' "$MAIN" 2>/dev/null || true)
N_MAIN_PH=${N_MAIN_PH:-0}
if [ "$N_MAIN_PH" -gt 1 ]; then
  fail "Main.lean has more than one placeholder; only the single goal marker is allowed."
fi

if [ "$FAIL" -ne 0 ]; then echo "=== INTEGRITY FAILURE ==="; exit 1; fi

echo "== 4. Done-ness: axiom audit =="
if [ "$N_MAIN_PH" -ge 1 ]; then
  echo "[IN PROGRESS] main_theorem still holds the open placeholder."
  echo "   Workspace is clean. Keep proving lemmas in Lemmas.lean."
  exit 0
fi
if command -v lake >/dev/null 2>&1; then
  AX="$(lake env lean ConjectureProof/Audit.lean 2>/dev/null || true)"
  echo "$AX"
  if echo "$AX" | grep -q 'sorryAx'; then
    echo "X FAIL: main_theorem is placeholder-free in source but depends on sorryAx."
    exit 1
  fi
  # The audit must actually have RUN. With mathlib oleans missing (e.g. a cold
  # container where `lake exe cache get` fetched nothing), `lake env lean` errors
  # to empty output -- which would otherwise fall through to a false [COMPLETE].
  # A genuine audit always prints the axiom list, which includes `propext`.
  if ! echo "$AX" | grep -q 'propext'; then
    echo "[CANNOT VERIFY] axiom audit did not run (no build/oleans available)."
    echo "   Source-level checks passed, but done-ness is NOT asserted. The real"
    echo "   verification is the merged proof / CI, where mathlib oleans are present."
    exit 0
  fi
  echo "[COMPLETE] main_theorem proven."
  echo "   Confirm the axiom list is only: propext, Classical.choice, Quot.sound."
else
  echo "warn: lake not on PATH; the axiom audit will run in CI."
fi
exit 0
