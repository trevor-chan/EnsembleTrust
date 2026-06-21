# Routine prompt (paste this as the routine's prompt)

You are working autonomously on a Lean 4 + mathlib formal proof. There is no
human to ask; the prompt and the repo are everything you have.

Read `CLAUDE.md` and `blueprint/PROGRESS.md` first. Follow CLAUDE.md's hard rules
exactly — especially: never edit `ConjectureProof/Statement.lean`; never use
`sorry`, `admit`, `native_decide`, `unsafe`, or `axiom`.

Your job this session:
1. From `blueprint/PROGRESS.md`, choose the next unproven frontier lemma (its
   dependencies are already proven). If the lemma tree is empty or thin, first
   decompose `MainProp` from `ConjectureProof/Statement.lean` into a tree of
   smaller named lemmas and write them into PROGRESS.md as TODO.
2. Prove as many frontier lemmas as you can in `ConjectureProof/Lemmas.lean`,
   then advance `ConjectureProof/Main.lean` toward `theorem main_theorem : MainProp`.
3. After EACH lemma: run `lake build`, then `bash scripts/check_integrity.sh`.
   A lemma is accepted only if BOTH pass. If a build recompiles mathlib from
   scratch, run `lake exe cache get` first.
4. Commit only accepted work. Update PROGRESS.md every time: mark lemmas
   PROVED/BLOCKED, and log the tactic that worked or the exact error that didn't.
5. If an attempt fails, revert it, record why in PROGRESS.md, and try a
   different frontier lemma. Never end with a red build.

Definition of done for the session: the build is green, the integrity check
passes, PROGRESS.md reflects reality, and your work is committed and pushed to a
`claude/`-prefixed branch with a PR opened or updated summarizing what changed
and what the next frontier is.

If you cannot make any lemma pass this session, that is fine — commit an updated
PROGRESS.md documenting what you tried and the blockers, so the next session
starts informed.
