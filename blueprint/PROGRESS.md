# PROGRESS — lab notebook & lemma tree

This file is the memory across nightly runs. The agent reads it at the start and
updates it at the end of every session.

## Target

`theorem main_theorem : MainProp`  (MainProp defined in `ConjectureProof/Statement.lean`)

## Lemma tree

Status legend: TODO · ATTEMPTED · BLOCKED · PROVED

- [ ] **lemma_A** — <one-line statement>
  - depends on: (none)
  - status: TODO
- [ ] **lemma_B** — <one-line statement>
  - depends on: lemma_A
  - status: TODO
- [ ] **main_theorem** — combines lemma_A, lemma_B
  - depends on: lemma_A, lemma_B
  - status: TODO

(Replace the above with the real decomposition of your conjecture.)

## Session log

> Append newest entries at the top. One block per run.

### YYYY-MM-DD
- Worked on: ...
- Proved: ...
- Failed / blocked: ... (include the exact Lean error)
- Tactics that worked: ...
- Next frontier: ...
