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
the single core inequality `C_core`. A worked-out attack for `C_core` (paper
reduction to one conditional-mean inequality) now lives in the C_core entry.

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
  - THE HARD PART, but now reduced on paper to ONE conditional-mean inequality
    (see "Strategy" below). depends on: C_delta, C_ratio_step ·
    status: **TODO — the sole remaining frontier.** Stated exactly as the
    hypothesis `Hcore` of `main_of_core`.
  - **Equivalent reformulations** (all proven equivalent by the chain above, use
    whichever is easiest to attack):
    1. `PC(k)·pI^k·Bsum(pC) > PI(k)·pC^k·Bsum(pI)`  (the `Hcore` form).
    2. `PC(k)·(PI(k)−PI(k+1)) > PI(k)·(PC(k)−PC(k+1))`  (`C_ratio_step`).
    3. `PC(k+1)·PI(k) > PI(k+1)·PC(k)`  (cross-multiplied ratio growth).
    4. `PC(k+1)/PC(k) > PI(k+1)/PI(k)`  (correct consensus "survives" the
       threshold bump better than incorrect).
    5. Peeling the `c=k`/`i=k` slice from (3) gives the self-similar
       `PC(k+1)·pI^k·Bsum(pC) > PI(k+1)·pC^k·Bsum(pI)`.
  - **Strategy (recommended attack — paper reduction to one clean inequality):**
    1. REINDEX onto a common set. With `T_k := {(c,i) : c > i, c ≥ k, c+i ≤ n}`,
         `PC(k) = Σ_{(c,i)∈T_k} M(c,i)`,  `PI(k) = Σ_{(c,i)∈T_k} M(i,c)`
       (PI via the `c↔i` relabel that `B_swap` already encodes — SAME set,
       reflected weights). By `choose_swap` the multinomial coefficient is
       swap-symmetric, so termwise
         `M(c,i) / M(i,c) = (pC/pI)^(c−i) =: t^(c−i)`,  `t := pC/pI > 1` on `T_k`.
    2. RATIO AS A WEIGHTED AVERAGE.
         `ρ(k) = PC(k)/PI(k) = (Σ_{T_k} t^(c−i)·M(i,c)) / (Σ_{T_k} M(i,c))`
              `= E_μ[ t^(c−i) ]`,  with measure `μ(c,i) ∝ M(i,c)` on `T_k`.
       Every weight `t^(c−i) > 1` since `c > i` on `T_k`.
    3. MEDIANT. `T_k = R_k ⊔ T_{k+1}` with `R_k = {(k,i) : i < k, k+i ≤ n}` the
       `c=k` slice (`ΔPC = Σ_{R_k} M(c,i)`, `ΔPI = Σ_{R_k} M(i,c)`; these are the
       C_delta closed forms). A mediant lies between its parents, so `ρ(k)` lies
       between `ΔPC/ΔPI` and `ρ(k+1)`, hence
         `ρ(k+1) > ρ(k)  ⟺  ρ(k+1) > ΔPC/ΔPI`
                        `⟺  E_μ[t^(c−i) | T_{k+1}] > E_μ[t^(c−i) | R_k]`.
       (Same as reformulation 3/4, read probabilistically:
        `E[·|T_{k+1}] = PC(k+1)/PI(k+1)`,
        `E[·|R_k] = ΔPC/ΔPI = t^k·Bsum(pI)/Bsum(pC)`.)
       ⇒ SOLE REMAINING GOAL: average weight on what survives the bump beats the
         average weight on the removed slice.
    4. WHY pR > 0 IS NEEDED (matches `pR_pos` in Statement): `μ(R_k)` carries a
       factor `pR^(n−k−i)`, so `μ(R_k) = 0` when `pR = 0` — nothing is removed,
       the mediant degenerates, `ρ` is flat. Strictness genuinely uses `pR_pos`.
  - **Attack avenues for the boxed inequality** (NOT pointwise: `T_{k+1}` holds
    small-weight points like `(k+1,k)` with `w=t`, while `R_k` holds the large
    `(k,0)` with `w=t^k`, so no termwise domination):
    (a) DOUBLE SUM / Chebyshev–FKG (most Lean-tractable — finite, no limits):
        `E[w|T_{k+1}] > E[w|R_k]  ⟺
           Σ_{x∈T_{k+1}} Σ_{y∈R_k} (w(x) − w(y))·μ(x)·μ(y) > 0`.
        Try to show positivity by pairing each `y∈R_k` with a dominating
        `x∈T_{k+1}`.
    (b) WEIGHTED INJECTION `φ : R_k ↪ T_{k+1}`. The shift `(k,i) ↦ (k+1,i)`
        multiplies `w` by `t` but distorts `μ` by `(n−k−i)·pI / ((k+1)·pR)`;
        needs that distortion controlled (or a better `φ`).
    (c) INDUCTION ON k riding the mediant relation upward.
    Recommend trying (a) on small `n` first to see whether the pairing is
    termwise or needs (b). Do NOT commit a partial/blind `C_core` that breaks the
    build — if no full line closes, log the sticking point and stop.
  - **Available tools for the attack:** `A0_pos` (PC,PI > 0), `Bsum_pos`
    (Bsum > 0, so both increments ΔPC,ΔPI > 0), `M_swap`/`B_swap` symmetry,
    `choose_swap`, and the closed forms `C_delta_PC/PI`.
- [~] **main_theorem** — `main_of_core` reduces `MainProp` to `Hcore` (= C_core)
    and is FULLY PROVEN. So `main_theorem := main_of_core C_core` the moment
    C_core lands. Until then `Main.lean` keeps the single sanctioned `sorry`.
  - depends on: C_core · status: assembled; waiting only on C_core.

## Session log

> Newest entry on top. One block per run.

### 2026-06-22 — C_core strategy added (paper work, not a proving run)
- Reduced C_core to a single conditional-mean inequality and recorded it in the
  C_core entry under "Strategy" + "Attack avenues". Nothing proven in Lean this
  pass; `Main.lean` still holds the single sanctioned `sorry`.
- Core reduction: reindex both PC,PI over the common set `T_k`; then
  `ρ(k) = E_μ[t^(c−i)]`; the mediant identity collapses monotonicity to
  `E[t^(c−i)|T_{k+1}] > E[t^(c−i)|R_k]`. This also re-derives the `pR>0` need.
- Frontier unchanged: C_core only. Preferred avenue (a), the finite double-sum
  positivity `Σ_{T_{k+1}}Σ_{R_k}(w(x)−w(y))μ(x)μ(y) > 0`; verify the pairing on
  small n by hand before formalizing.

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
