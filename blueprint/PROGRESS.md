# PROGRESS — lab notebook & lemma tree

Memory across nightly runs. Read at the start of each session, update at the end.

## Target

`theorem main_theorem : MainProp` — for `P : Params` (pC,pI,pR > 0, sum 1),
`n ≥ 2`, `1 ≤ k`, `k+1 ≤ n`:
`Trust P n (k+1) > Trust P n k  ↔  pC > pI`.

## Strategy

Let `ρ(k) := PC(k) / PI(k)`. Because `Trust = 1/(1 + PI/PC)` is strictly
increasing in `ρ`, trust-monotonicity is ratio-monotonicity. The `c ↔ i`
symmetry of the index set reduces the `iff` to one implication; the real work is
that single core inequality.

## Lemma tree

Status legend: TODO · ATTEMPTED · BLOCKED · PROVED

- [ ] **A0_pos** — `0 < PC P n k` and `0 < PI P n k` for all `k ≤ n`.
  - why: needed for the ratio and the denominator of Trust. The all-correct term
    `pC^n` (resp. `pI^n`) is always in range and positive.
  - depends on: (none) · status: TODO
- [ ] **A_trust_iff_ratio** — `Trust P n (k+1) > Trust P n k ↔ ρ(k+1) > ρ(k)`.
  - algebra over positives; cross-multiply with A0_pos.
  - depends on: A0_pos · status: TODO
- [ ] **B_swap** — `PI P n k = PC P' n k` where `P'` swaps pC and pI.
  - reindex the double sum by `c ↔ i`; `M` is symmetric under the swap.
  - depends on: (none) · status: TODO
- [ ] **B_branches** — from B_swap: pC = pI ⟹ ρ constant (Trust ≡ ½);
    pC < pI ⟹ ρ strictly decreasing. Gives the two non-`<½` directions.
  - depends on: B_swap, C_core · status: TODO
- [ ] **C_delta** — closed forms for the boundary increments:
    `PC(k) − PC(k+1) = pC^k · C(n,k) · Bsum(pI)` and
    `PI(k) − PI(k+1) = pI^k · C(n,k) · Bsum(pC)`,
    where `Bsum(x) = Σ_{j=0}^{min(k-1,n-k)} C(n-k,j) x^j pR^{(n-k)-j}`.
  - depends on: (none) · status: TODO
- [ ] **C_ratio_step** — `ρ(k+1) > ρ(k) ↔ PC(k)·(PI(k)−PI(k+1)) > PI(k)·(PC(k)−PC(k+1))`.
  - depends on: A0_pos · status: TODO
- [ ] **C_core** — pC > pI (with pR > 0) ⟹ the C_ratio_step inequality holds,
    i.e. `pI^k Bsum(pC) · PC(k) > pC^k Bsum(pI) · PI(k)` for all valid k.
  - THE HARD PART. Likely induction on k and/or a log-concavity / ratio argument.
  - depends on: C_delta, C_ratio_step · status: TODO
- [ ] **main_theorem** — assemble A_trust_iff_ratio + B_branches + C_core into the iff.
  - depends on: all of the above · status: TODO

## Session log

> Newest entry on top. One block per run.

### (seed)
- Statement frozen. Placeholder `main_theorem` open. Lemma tree above is the plan.
- First frontier: A0_pos, B_swap, C_delta (all independent, all TODO).
- Next frontier: nothing proven yet.
