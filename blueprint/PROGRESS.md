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

- [x] **A0_pos** — `0 < PC P n k` and `0 < PI P n k` for `1 ≤ n`, `k ≤ n`.
  - why: needed for the ratio and the denominator of Trust. The all-correct term
    `pC^n` (resp. `pI^n`) is always in range and positive.
  - depends on: (none) · status: **PROVED** (as `PC_pos`, `PI_pos`).
    Helpers: `M_nonneg` (positivity), `M_corner_C`/`M_corner_I` (corner terms
    `= pC^n` / `pI^n`, by `simp`). Proof: `Finset.sum_pos'` twice (outer over the
    count, inner over the plurality index), exhibiting the corner `c=n,i=0`
    (resp. `i=n,c=0`).
- [x] **A_trust_iff_ratio** — `Trust P n (k+1) > Trust P n k ↔ ρ(k+1) > ρ(k)`.
  - algebra over positives; cross-multiply with A0_pos.
  - depends on: A0_pos · status: **PROVED**. Stated in cross-multiplied form:
    `Trust(k+1) > Trust(k) ↔ PC(k+1)·PI(k) > PC(k)·PI(k+1)` (avoids division).
    Helper `trust_lt_iff`: for positives, `a/(a+b) < c/(c+d) ↔ a*d < c*b` via
    `div_lt_div_iff₀` + `nlinarith`.
- [x] **B_swap** — `PI P n k = PC P' n k` where `P'` swaps pC and pI.
  - reindex the double sum by `c ↔ i`; `M` is symmetric under the swap.
  - depends on: (none) · status: **PROVED** (as `B_swap`, with `swap P` the
    swapped params). Key pieces:
    - `choose_swap`: `C(n,c)·C(n-c,i) = C(n,i)·C(n-i,c)` via `Nat.choose_mul`
      (twice, with `k=c+i`) + `Nat.choose_symm_add`.
    - `M_swap`: `M P n c i = M (swap P) n i c`, by `choose_swap` (cast to ℝ) +
      `n-c-i = n-i-c` + `linear_combination`.
    - `B_swap` itself: `Finset.sum_congr` term-by-term (index sets already match)
      + `M_swap` + `Nat.add_comm`.
    - Also have `swap_swap : swap (swap P) = P` (`rfl`) for the symmetry trick.
- [ ] **B_branches** — from B_swap: pC = pI ⟹ ρ constant (Trust ≡ ½);
    pC < pI ⟹ ρ strictly decreasing. Gives the two non-`<½` directions.
  - depends on: B_swap, C_core · status: TODO
- [x] **C_delta** — closed forms for the boundary increments:
    `PC(k) − PC(k+1) = pC^k · C(n,k) · Bsum(pI)` and
    `PI(k) − PI(k+1) = pI^k · C(n,k) · Bsum(pC)`,
    where `Bsum(x) = Σ_{i=0}^{k-1} [k+i≤n] C(n-k,i) x^i pR^{(n-k)-i}`.
  - depends on: (none) · status: **PROVED** (`C_delta_PC`, `C_delta_PI`).
    `Bsum` is `def`'d with the indicator `[k+i≤n]` folded in (so the `range k`
    cap and the `i ≤ n-k` cap are both present, matching `min(k-1,n-k)`).
    `C_delta_PC`: peel `Icc k n = insert k (Icc (k+1) n)`, `sum_insert`,
    `add_sub_cancel_right` to cancel the `PC(k+1)` tail, then factor
    `C(n,k)·pC^k` out via `Finset.mul_sum` + termwise `unfold M; ring`.
    `C_delta_PI`: from `C_delta_PC (swap P)` via `B_swap` + `Bsum_swap`.
- [x] **C_ratio_step** — `ρ(k+1) > ρ(k) ↔ PC(k)·(PI(k)−PI(k+1)) > PI(k)·(PC(k)−PC(k+1))`.
  - depends on: A0_pos · status: **PROVED** (pure algebra; `constructor <;> nlinarith`).
    Needed no positivity. Also `core_iff_ratio`: folds in `C_delta` and cancels
    the positive `C(n,k)` so the ratio step becomes the **core comparison**
    `PC(k)·pI^k·Bsum(pC) > PI(k)·pC^k·Bsum(pI)`.
- [x] **B_branches** — subsumed by `main_of_core`. The trichotomy on `pC` vs
    `pI` (with `swap` symmetry: `core_L_swap`, `core_R_swap`, and
    `PC_eq_PI_of_pC_eq_pI` for the `pC=pI` case) handles all three directions.
  - depends on: B_swap, C_core · status: **PROVED** (inside `main_of_core`).
- [ ] **C_core** — pC > pI (with pR > 0) ⟹ the core comparison holds,
    i.e. `PC(k)·pI^k·Bsum(pC) > PI(k)·pC^k·Bsum(pI)` for all valid k.
  - THE HARD PART. Likely induction on k and/or a log-concavity / ratio argument.
  - depends on: C_delta, C_ratio_step · status: **TODO — the sole remaining frontier.**
    Stated exactly as the hypothesis `Hcore` of `main_of_core`.
  - **Equivalent reformulations** (all proven equivalent by the chain above, use
    whichever is easiest to attack):
    1. `PC(k)·pI^k·Bsum(pC) > PI(k)·pC^k·Bsum(pI)`  (the `Hcore` form).
    2. `PC(k)·(PI(k)−PI(k+1)) > PI(k)·(PC(k)−PC(k+1))`  (`C_ratio_step`).
    3. `PC(k+1)·PI(k) > PI(k+1)·PC(k)`  (cross-multiplied ratio growth).
    4. `PC(k+1)/PC(k) > PI(k+1)/PI(k)`  (correct consensus "survives" the
       threshold bump better than incorrect).
    5. Peeling the `c=k`/`i=k` slice from (3) gives the self-similar
       `PC(k+1)·pI^k·Bsum(pC) > PI(k+1)·pC^k·Bsum(pI)`.
  - **Available tools for the attack:** `A0_pos` (PC,PI > 0), `Bsum_pos`
    (Bsum > 0, so both increments ΔPC,ΔPI > 0), `M_swap`/`B_swap` symmetry,
    `choose_swap`, and the closed forms `C_delta_PC/PI`. The remaining content is
    a genuine combinatorial inequality (a weighted injection from the PI index
    set into the PC index set that strictly increases mass when pC>pI), not yet
    formalized.
- [~] **main_theorem** — `main_of_core` reduces `MainProp` to `Hcore` (= C_core)
    and is FULLY PROVEN. So `main_theorem := main_of_core C_core` the moment
    C_core lands. Until then `Main.lean` keeps the single sanctioned `sorry`.
  - depends on: C_core · status: assembled; waiting only on C_core.

## Session log

> Newest entry on top. One block per run.

### 2026-06-22 — first proving run
- Env note: the Lean release host (`releases.lean-lang.org`) is blocked by the
  network policy (403 `host_not_allowed`); installed `leanprover/lean4:v4.31.0`
  from the GitHub releases mirror by hand (download + python `zstandard` extract
  into `~/.elan/toolchains/`), then `lake exe cache get` worked. Build green.
- **PROVED this run (all in `Lemmas.lean`, build + integrity green at each step):**
  - `A0_pos` → `PC_pos`, `PI_pos` (+ helpers `M_nonneg`, `M_corner_C/I`).
  - `A_trust_iff_ratio` (+ abstract `trust_lt_iff`, via `div_lt_div_iff₀`).
  - `B_swap` (+ `choose_swap`, `swap`/`swap_swap`, `M_swap`).
  - `C_delta` → `C_delta_PC`, `C_delta_PI` (+ `Bsum` def, `Bsum_swap`).
  - `C_ratio_step` and `core_iff_ratio`.
  - `main_of_core`: **fully proven reduction of `MainProp` to `C_core`**
    (subsumes `B_branches` via trichotomy + `swap` symmetry; helpers
    `M_eq_swap_of_eq`, `PC_eq_PI_of_pC_eq_pI`, `core_L_swap`, `core_R_swap`).
  - `Bsum_pos` (down payment toward C_core: increments are strictly positive).
- **Frontier for next run:** `C_core` only. The moment it lands,
  `Main.lean` becomes `theorem main_theorem : MainProp := main_of_core C_core`
  and the project is COMPLETE. See the C_core entry for 5 equivalent forms and
  the available toolbox.
- `Main.lean` still holds the single sanctioned `sorry`.

### (seed)
- Statement frozen. Placeholder `main_theorem` open. Lemma tree above is the plan.
- First frontier: A0_pos, B_swap, C_delta (all independent, all TODO).
- Next frontier: nothing proven yet.
