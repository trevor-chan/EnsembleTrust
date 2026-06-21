# Conjecture proof (Lean 4 + mathlib)

Autonomous overnight formalization. The conjecture is frozen in
`ConjectureProof/Statement.lean`; nightly Claude Code routine runs try to prove
`theorem main_theorem : MainProp`. Integrity is gated so a green build means a
real proof.

## One-time local setup

```bash
# 1. Install Lean toolchain manager
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# 2. Generate a mathlib-ready project (creates lakefile + matched lean-toolchain)
lake new conjecture_proof math
cd conjecture_proof

# 3. Overlay the files from this scaffold (Statement/Lemmas/Main/Audit, scripts,
#    CLAUDE.md, ROUTINE_PROMPT.md, blueprint/, .github/). Match the generated
#    root module/namespace name if it differs from `ConjectureProof`.

# 4. Pull prebuilt mathlib and confirm a green build
lake exe cache get
lake build
chmod +x scripts/*.sh

# 5. Encode YOUR conjecture in ConjectureProof/Statement.lean, then freeze it:
sha256sum ConjectureProof/Statement.lean > scripts/statement.sha256
git add -A && git commit -m "Freeze conjecture statement" && git push
```

## Routine (overnight, hands-off)

1. claude.ai/settings → create a **custom environment**; set its **setup script**
   to the contents of `scripts/setup_env.sh`. Save it before creating the routine.
2. claude.ai/code/routines → **New routine** (Remote): attach this repo, pick the
   environment, select **Opus**, paste `ROUTINE_PROMPT.md` as the prompt, add a
   **nightly schedule** trigger (e.g. 23:00 local).
3. **Run now** once and read the transcript end-to-end. If `lake exe cache get`
   or elan install is blocked, allowlist the host shown in the log under the
   environment's network access.

## The honesty gate

`scripts/check_integrity.sh` fails the build if: the statement file changed, any
`sorry`/`admit`/`native_decide`/`unsafe`/`axiom` appears, the final theorem isn't
typed `MainProp`, or the axiom audit shows `sorryAx`. CI (`.github/workflows/verify.yml`)
runs the same gate on every PR.
