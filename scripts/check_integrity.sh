#!/usr/bin/env bash
# Fails (exit 1) if the agent reached a green build by cheating.
# Run AFTER `lake build` succeeds. CI and the routine both call this.
set -uo pipefail

SRC="ConjectureProof"
STATEMENT="ConjectureProof/Statement.lean"
FAIL=0
note() { echo "❌ INTEGRITY FAIL: $*"; FAIL=1; }

echo "== 1. Conjecture statement is frozen =="
if [ -f scripts/statement.sha256 ]; then
  if sha256sum -c scripts/statement.sha256 >/dev/null 2>&1; then
    echo "ok: $STATEMENT unchanged"
  else
    note "$STATEMENT checksum mismatch — the conjecture was altered."
  fi
else
  echo "warn: scripts/statement.sha256 missing. Create it once with:"
  echo "      sha256sum $STATEMENT > scripts/statement.sha256"
fi

echo "== 2. No proof placeholders or trust escapes in our sources =="
grep -rEn '\bsorry\b|\badmit\b'      "$SRC" && note "found 'sorry'/'admit' (incomplete proof)."
grep -rEn '\bnative_decide\b'        "$SRC" && note "found 'native_decide' (disallowed)."
grep -rEn '\bunsafe\b|@\[implemented_by' "$SRC" && note "found 'unsafe'/implemented_by."
grep -rEn '^\s*axiom\b'              "$SRC" && note "found an 'axiom' declaration (assumptions ≠ proofs)."

echo "== 3. Final theorem proves the FROZEN proposition, unweakened =="
if grep -rEn 'main_theorem\s*:\s*MainProp\b' "$SRC" >/dev/null; then
  echo "ok: 'theorem main_theorem : MainProp' present"
else
  note "could not find 'main_theorem : MainProp' — type may have been weakened."
fi

echo "== 4. Gold standard: axiom audit of the final theorem =="
if command -v lake >/dev/null 2>&1; then
  AX="$(lake env lean ConjectureProof/Audit.lean 2>/dev/null || true)"
  echo "$AX"
  echo "$AX" | grep -q 'sorryAx' && note "main_theorem depends on sorryAx — proof is incomplete."
  echo "→ Confirm the list above is ONLY: propext, Classical.choice, Quot.sound."
else
  echo "warn: lake not on PATH; skipping axiom audit (it runs in CI / the routine)."
fi

if [ "$FAIL" -ne 0 ]; then echo "=== INTEGRITY CHECK FAILED ==="; exit 1; fi
echo "=== integrity check passed ==="
