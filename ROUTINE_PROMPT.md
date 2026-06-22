# Routine prompt (paste everything below this header line as the routine's prompt)

You are working autonomously on a Lean 4 + mathlib formal proof. There is no
human to ask; the prompt and the repo are everything you have.

Read `CLAUDE.md` and `blueprint/PROGRESS.md` first. Follow CLAUDE.md's hard rules
exactly — never edit `ConjectureProof/Statement.lean`; never use `native_decide`,
`unsafe`, or `axiom`. Exactly one `sorry`/`admit` is permissible, and only in
`main_theorem` (`Main.lean`).

## Time budget (set this up first)

At the very start, record the start time once:

    date +%s > /tmp/start_epoch

Budgets for this session:
- WORK_BUDGET = 270 minutes — stop starting any NEW work after this.
- WRAPUP_RESERVE = 30 minutes — be fully committed, pushed, and stopped within
  this window after WORK_BUDGET (i.e. by 300 minutes elapsed).

Check elapsed minutes before starting any new lemma attempt — and before
starting OR resuming a `C_core` attempt specifically:

    ELAPSED=$(( ($(date +%s) - $(cat /tmp/start_epoch)) / 60 )); echo "elapsed ${ELAPSED}m"

- ELAPSED < WORK_BUDGET  -> continue the work loop.
- ELAPSED >= WORK_BUDGET -> do not start anything new; go straight to Wrap-up.

The budget is a ceiling, not a target. If the tractable work runs out sooner --
e.g. only `C_core` remains and you have no viable line of attack -- wrap up and
finish early rather than burning the remainder.

## Work loop

1. From `blueprint/PROGRESS.md`, choose the next unproven frontier lemma (one
   whose dependencies are already proven). If the lemma tree is empty or thin,
   first decompose `MainProp` into smaller named lemmas and record them in
   PROGRESS.md as TODO.
2. Prove as many frontier lemmas as you can in `ConjectureProof/Lemmas.lean`,
   then advance `ConjectureProof/Main.lean` toward `theorem main_theorem : MainProp`.
3. After EACH lemma: run `lake build`, then `bash scripts/check_integrity.sh`.
   A lemma is accepted only if the build is GREEN and the integrity check is NOT
   in FAILURE ([IN PROGRESS] or [COMPLETE] are both fine). If a build recompiles
   mathlib from scratch, run `lake exe cache get` first.
4. The instant a lemma is accepted, checkpoint it immediately -- never hold
   accepted work locally:
   - commit it;
   - push the `claude/` branch to origin;
   - on the first push of the session, open a PR; later pushes update it.
   Each accepted lemma should be on GitHub within a minute of being proven, so
   nothing is lost if the session ends abruptly. Update PROGRESS.md in the same
   commit: mark lemmas PROVED/BLOCKED and log the tactic that worked or the exact
   error that didn't.
5. If an attempt fails, revert it
   (`git checkout -- ConjectureProof/Lemmas.lean ConjectureProof/Main.lean`),
   record why in PROGRESS.md, and try a different frontier lemma. Never end with
   a red build.

`C_core` is open-ended and can consume an entire session. Never begin a fresh
`C_core` attempt that cannot plausibly be both finished AND verified before
WORK_BUDGET. If you are mid-attempt when the budget hits, abandon it cleanly
(step 5) rather than leaving a broken build.

## Wrap-up (must complete before 300 minutes elapsed)

1. If uncommitted changes don't build, discard them back to the last green
   commit (step 5). Never leave a red build.
2. Run `lake build` then `bash scripts/check_integrity.sh`; confirm GREEN and
   [IN PROGRESS] (or [COMPLETE]).
3. Update `blueprint/PROGRESS.md`: what was proven this run, what was tried on
   `C_core` and the exact sticking point, and the next frontier.
4. Commit, push the `claude/` branch, and ensure the PR is open with a
   description reflecting the current state.
5. Stop. Do not start new work after wrap-up, even if time remains.

If you could not make any lemma pass this session, that is fine -- an updated
PROGRESS.md documenting what you tried and the blockers is itself a successful,
committed, pushed result that sets up the next run.
