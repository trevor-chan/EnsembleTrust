# Project: formal proof of a conjecture

This repo formalizes and proves one conjecture in Lean 4 + mathlib. Empirical
evidence supporting it lives in `python/` (simulations) — that is context, not
proof.

## Hard rules (non-negotiable)

1. **Never edit `ConjectureProof/Statement.lean`.** It is the frozen conjecture.
   Its checksum is verified; any change fails the build.
2. Exactly one placeholder is allowed: the pre-placed sorry in main_theorem (Main.lean), 
   marking the open goal. Never add sorry/admit anywhere else — Lemmas.lean must be 
   fully proven at every commit. Never use native_decide, unsafe, or axiom. 
   "Done" = the main_theorem placeholder is discharged and the axiom audit is clean.
3. The final goal is `theorem main_theorem : MainProp` in `ConjectureProof/Main.lean`,
   with the type exactly `MainProp`. Do not change the type.
4. A change counts as progress ONLY if `lake build` succeeds **and**
   `bash scripts/check_integrity.sh` is not in FAILURE.

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

- `lake exe cache get` — fetch prebuilt mathlib (run at the start of every session, before first build).
- `lake build` — build the project.
- `bash scripts/check_integrity.sh` — the honesty gate.
