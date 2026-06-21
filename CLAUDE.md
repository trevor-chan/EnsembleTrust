# Project: formal proof of a conjecture

This repo formalizes and proves one conjecture in Lean 4 + mathlib. Empirical
evidence supporting it lives in `python/` (simulations) — that is context, not
proof.

## Hard rules (non-negotiable)

1. **Never edit `ConjectureProof/Statement.lean`.** It is the frozen conjecture.
   Its checksum is verified; any change fails the build.
2. **Never use `sorry`, `admit`, `native_decide`, `unsafe`, or `axiom`.** A proof
   that needs these is not done. Leave unfinished lemmas commented out instead.
3. The final goal is `theorem main_theorem : MainProp` in `ConjectureProof/Main.lean`,
   with the type exactly `MainProp`. Do not change the type.
4. A change counts as progress ONLY if `lake build` succeeds **and**
   `bash scripts/check_integrity.sh` passes.

## Workflow each run

1. Read `blueprint/PROGRESS.md` — it is the lab notebook and lemma tree.
2. Pick the next unproven frontier lemma (one whose dependencies are proven).
3. Attempt it in `ConjectureProof/Lemmas.lean`. Try standard tactics
   (`simp`, `omega`, `linarith`, `exact?`, `apply?`, library search) before
   anything exotic.
4. Run `lake build` then `bash scripts/check_integrity.sh`.
5. If both pass: update `PROGRESS.md` (mark PROVED, note the tactic that worked),
   commit, and continue to the next lemma.
6. If it fails: revert the broken edit, record in `PROGRESS.md` under that lemma
   what you tried and the exact error, and move to a different frontier lemma.
7. Never leave the build red at the end of a session.

## Useful commands

- `lake exe cache get` — fetch prebuilt mathlib (run if `lake build` recompiles mathlib).
- `lake build` — build the project.
- `bash scripts/check_integrity.sh` — the honesty gate.
