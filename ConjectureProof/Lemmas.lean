/-
  LEMMA TREE — the agent's main workspace.

  Decompose `MainProp` into named, independently-provable lemmas here.
  Each lemma gets an entry in blueprint/PROGRESS.md with a status.
  The agent proves lemmas bottom-up; `Main.lean` assembles them into the
  final theorem.

  Integrity rules (the full, explicit list is in CLAUDE.md and is enforced by
  scripts/check_integrity.sh): no proof placeholders, no compiler-trusting
  decision procedures, no kernel-bypassing declarations, and no newly
  introduced assumptions. A lemma counts as done only when `lake build` is
  green AND the integrity check passes.
-/
import ConjectureProof.Statement

namespace ConjectureProof

open Finset
open scoped Nat

/-! ## Basic facts about the multinomial weight `M`. -/

/-- Every multinomial weight is nonnegative (product of nonnegative factors). -/
lemma M_nonneg (P : Params) (n c i : ℕ) : 0 ≤ M P n c i := by
  have := P.pC_pos; have := P.pI_pos; have := P.pR_pos
  unfold M
  positivity

/-- The "all correct" corner term: `c = n`, `i = 0`. -/
lemma M_corner_C (P : Params) (n : ℕ) : M P n n 0 = P.pC ^ n := by
  unfold M
  simp

/-- The "all specious" corner term: `c = 0`, `i = n`. -/
lemma M_corner_I (P : Params) (n : ℕ) : M P n 0 n = P.pI ^ n := by
  unfold M
  simp

/-- The "boundary sum" appearing in the threshold increment: the contribution
of the agents *not* in the winning bloc, with `x` the per-agent weight of the
losing-but-counted side.  Only `P.pR` is used from `P`. -/
noncomputable def Bsum (P : Params) (n k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k,
    if k + i ≤ n then ((n - k).choose i : ℝ) * x ^ i * P.pR ^ (n - k - i) else 0

/-! ## A0_pos — strict positivity of the two consensus probabilities. -/

/-- `PC` is strictly positive: the all-correct outcome `c = n, i = 0` is always
in range and contributes `pC^n > 0`. -/
lemma PC_pos (P : Params) (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) : 0 < PC P n k := by
  have hpC := P.pC_pos
  unfold PC
  apply Finset.sum_pos'
  · intro c _
    apply Finset.sum_nonneg
    intro i _
    split_ifs with h
    · exact M_nonneg P n c i
    · exact le_refl 0
  · refine ⟨n, Finset.mem_Icc.mpr ⟨hk, le_refl n⟩, ?_⟩
    apply Finset.sum_pos'
    · intro i _
      split_ifs with h
      · exact M_nonneg P n n i
      · exact le_refl 0
    · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      rw [if_pos (by omega), M_corner_C]
      positivity

/-- `PI` is strictly positive: the all-specious outcome `i = n, c = 0` is always
in range and contributes `pI^n > 0`. -/
lemma PI_pos (P : Params) (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) : 0 < PI P n k := by
  have hpI := P.pI_pos
  unfold PI
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro c _
    split_ifs with h
    · exact M_nonneg P n c i
    · exact le_refl 0
  · refine ⟨n, Finset.mem_Icc.mpr ⟨hk, le_refl n⟩, ?_⟩
    apply Finset.sum_pos'
    · intro c _
      split_ifs with h
      · exact M_nonneg P n c n
      · exact le_refl 0
    · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      rw [if_pos (by omega), M_corner_I]
      positivity

/-! ## B_swap — the `c ↔ i` symmetry of the index set. -/

/-- The multinomial coefficient is symmetric under exchanging the two counts:
`C(n,c)·C(n-c,i) = C(n,i)·C(n-i,c)` (both equal `n! / (c! i! (n-c-i) !)`). -/
lemma choose_swap (n c i : ℕ) :
    n.choose c * (n - c).choose i = n.choose i * (n - i).choose c := by
  have h1 := Nat.choose_mul (n := n) (k := c + i) (s := c) (Nat.le_add_right c i)
  have h2 := Nat.choose_mul (n := n) (k := c + i) (s := i) (Nat.le_add_left i c)
  have e1 : c + i - c = i := by omega
  have e2 : c + i - i = c := by omega
  rw [e1] at h1
  rw [e2] at h2
  rw [Nat.choose_symm_add] at h1
  rw [← h1]; exact h2

/-- The parameter triple with the correct and specious probabilities exchanged. -/
def swap (P : Params) : Params where
  pC := P.pI
  pI := P.pC
  pR := P.pR
  pC_pos := P.pI_pos
  pI_pos := P.pC_pos
  pR_pos := P.pR_pos
  sum_one := by have := P.sum_one; linarith

@[simp] lemma swap_pC (P : Params) : (swap P).pC = P.pI := rfl
@[simp] lemma swap_pI (P : Params) : (swap P).pI = P.pC := rfl
@[simp] lemma swap_pR (P : Params) : (swap P).pR = P.pR := rfl

/-- `swap` is an involution. -/
lemma swap_swap (P : Params) : swap (swap P) = P := rfl

/-- The multinomial weight is symmetric: exchanging the two counts is the same
as swapping the two probabilities. -/
lemma M_swap (P : Params) (n c i : ℕ) : M P n c i = M (swap P) n i c := by
  simp only [M, swap_pC, swap_pI, swap_pR]
  have hch : (n.choose c : ℝ) * ((n - c).choose i : ℝ)
      = (n.choose i : ℝ) * ((n - i).choose c : ℝ) := by
    exact_mod_cast choose_swap n c i
  have hsub : n - c - i = n - i - c := by omega
  rw [hsub]
  linear_combination (P.pC ^ c * P.pI ^ i * P.pR ^ (n - i - c)) * hch

/-- The specious-consensus probability for `P` equals the correct-consensus
probability for the swapped parameters: reindex the double sum by `c ↔ i`. -/
lemma B_swap (P : Params) (n k : ℕ) : PI P n k = PC (swap P) n k := by
  unfold PI PC
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [M_swap P n b a, Nat.add_comm b a]

/-! ## C_delta — closed forms for the threshold increments. -/

/-- `Bsum` only depends on `P` through `P.pR`, which `swap` fixes. -/
lemma Bsum_swap (P : Params) (n k : ℕ) (x : ℝ) :
    Bsum (swap P) n k x = Bsum P n k x := by
  simp only [Bsum, swap_pR]

/-- `Bsum` is strictly positive for a positive weight: the `i = 0` term is
`pR^(n-k) > 0` and the rest are nonnegative. (Needs `1 ≤ k ≤ n`.) -/
lemma Bsum_pos (P : Params) (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) {x : ℝ}
    (hx : 0 < x) : 0 < Bsum P n k x := by
  have hpR := P.pR_pos
  unfold Bsum
  apply Finset.sum_pos'
  · intro i _
    split_ifs with h
    · positivity
    · exact le_refl 0
  · refine ⟨0, Finset.mem_range.mpr hk1, ?_⟩
    rw [if_pos (by omega)]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
    positivity

/-- The `if k+i ≤ n` guard in `Bsum` is redundant: when `i > n-k` the binomial
coefficient `C(n-k,i)` already vanishes.  Dropping it gives a plain `range`-sum,
the convenient form for the double-sum manipulations behind `C_core`. -/
lemma Bsum_eq (P : Params) (n k : ℕ) (hkn : k ≤ n) (x : ℝ) :
    Bsum P n k x
      = ∑ i ∈ Finset.range k, ((n - k).choose i : ℝ) * x ^ i * P.pR ^ (n - k - i) := by
  unfold Bsum
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (show n - k < i by omega), Nat.cast_zero]; ring

/-- Raising the threshold removes exactly the `c = k` slice of the correct-
consensus sum: `PC(k) − PC(k+1) = C(n,k)·pC^k·Bsum(pI)`. -/
lemma C_delta_PC (P : Params) (n k : ℕ) (hk : k ≤ n) :
    PC P n k - PC P n (k + 1)
      = (n.choose k : ℝ) * P.pC ^ k * Bsum P n k P.pI := by
  have hins : Finset.Icc k n = insert k (Finset.Icc (k + 1) n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnm : k ∉ Finset.Icc (k + 1) n := by simp [Finset.mem_Icc]
  unfold PC
  rw [hins, Finset.sum_insert hnm, add_sub_cancel_right, Bsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · unfold M; ring
  · ring

/-- The specious counterpart, by the `c ↔ i` symmetry:
`PI(k) − PI(k+1) = C(n,k)·pI^k·Bsum(pC)`. -/
lemma C_delta_PI (P : Params) (n k : ℕ) (hk : k ≤ n) :
    PI P n k - PI P n (k + 1)
      = (n.choose k : ℝ) * P.pI ^ k * Bsum P n k P.pC := by
  rw [B_swap P n k, B_swap P n (k + 1), C_delta_PC (swap P) n k hk, swap_pC,
    swap_pI, Bsum_swap]

/-! ## Slice decomposition — `PC`/`PI` as sums of per-`c` slices.

Each fixed correct-count `c ≥ k` contributes `C(n,c)·pC^c·Bsum(n,c,pI)` to `PC`
(`Bsum P n c x` is the boundary generator `S_c(x)` for that slice).  This rewrites
the consensus probabilities as single sums over the winning count, the form used
to attack `C_core` slice-by-slice. -/

/-- The inner `c`-slice of the correct-consensus sum factors as
`C(n,c)·pC^c·Bsum(n,c,pI)`. -/
lemma PC_inner (P : Params) (n c : ℕ) :
    (∑ i ∈ Finset.range c, if c + i ≤ n then M P n c i else 0)
      = (n.choose c : ℝ) * P.pC ^ c * Bsum P n c P.pI := by
  rw [Bsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · unfold M; ring
  · ring

/-- `PC` as a sum of per-`c` slices. -/
lemma PC_slice (P : Params) (n k : ℕ) :
    PC P n k
      = ∑ c ∈ Finset.Icc k n, (n.choose c : ℝ) * P.pC ^ c * Bsum P n c P.pI := by
  unfold PC
  exact Finset.sum_congr rfl (fun c _ => PC_inner P n c)

/-- `PI` as a sum of per-`c` slices, via the `c ↔ i` symmetry. -/
lemma PI_slice (P : Params) (n k : ℕ) :
    PI P n k
      = ∑ c ∈ Finset.Icc k n, (n.choose c : ℝ) * P.pI ^ c * Bsum P n c P.pC := by
  rw [B_swap, PC_slice]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [swap_pC, swap_pI, Bsum_swap]

/-! ## Binomial-coefficient inequality — the combinatorial core of a slice.

`bracket_c`'s double-sum kernel is antisymmetric under `(a,b) ↦ (b+u, a−u)`, so its
positivity reduces to a weight comparison that is, after clearing the `pR` factors,
the pure inequality `binom_key`.  No probabilities appear here. -/

/-- A factorial monotonicity template: for `p ≤ q`,
`(p+t) !·q! ≤ (q+t) !·p!`.  (Equivalent to `C(p+t,t) ≤ C(q+t,t)`.) -/
lemma fact_template (p q t : ℕ) (h : p ≤ q) :
    (p + t) ! * q ! ≤ (q + t) ! * p ! := by
  have hp : (p + t).choose t * t ! * p ! = (p + t) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show t ≤ p + t by omega)
    rwa [Nat.add_sub_cancel] at this
  have hq : (q + t).choose t * t ! * q ! = (q + t) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show t ≤ q + t by omega)
    rwa [Nat.add_sub_cancel] at this
  have hc : (p + t).choose t ≤ (q + t).choose t := Nat.choose_le_choose t (by omega)
  calc (p + t) ! * q !
      = ((p + t).choose t * t ! * p !) * q ! := by rw [hp]
    _ = ((p + t).choose t * t ! * q !) * p ! := by ring
    _ ≤ ((q + t).choose t * t ! * q !) * p ! := by gcongr
    _ = (q + t) ! * p ! := by rw [hq]

/-- **The combinatorial core.**  For `s < b` (any `N, u`):
`C(N,b+u)·C(N+u,s) ≤ C(N,u+s)·C(N+u,b)`.
Both sides equal `N!·(N+u) !` divided by a product of four factorials; the claim is
that the left multiplier dominates the right, which `fact_template` supplies. -/
lemma binom_key (N u s b : ℕ) (hsb : s < b) :
    N.choose (b + u) * (N + u).choose s ≤ N.choose (u + s) * (N + u).choose b := by
  by_cases hbu : b + u ≤ N
  · -- the generic case: clear to factorials and compare the multipliers
    have hus : u + s ≤ N := by omega
    have hb : b ≤ N + u := by omega
    have hs : s ≤ N + u := by omega
    set L := N.choose (b + u) * (N + u).choose s with hL_def
    set R := N.choose (u + s) * (N + u).choose b with hR_def
    set Da := (u + s) ! * (N - (u + s)) ! * (b ! * (N + u - b) !) with hDa_def
    set Db := (b + u) ! * (N - (b + u)) ! * (s ! * (N + u - s) !) with hDb_def
    have e1 : N.choose (u + s) * (u + s) ! * (N - (u + s)) ! = N ! :=
      Nat.choose_mul_factorial_mul_factorial hus
    have e2 : (N + u).choose b * b ! * (N + u - b) ! = (N + u) ! :=
      Nat.choose_mul_factorial_mul_factorial hb
    have e3 : N.choose (b + u) * (b + u) ! * (N - (b + u)) ! = N ! :=
      Nat.choose_mul_factorial_mul_factorial hbu
    have e4 : (N + u).choose s * s ! * (N + u - s) ! = (N + u) ! :=
      Nat.choose_mul_factorial_mul_factorial hs
    -- both `L·Db` and `R·Da` reorganise to `N!·(N+u) !`
    have hLDb : L * Db = N ! * (N + u) ! := by
      have : L * Db
          = (N.choose (b + u) * (b + u) ! * (N - (b + u)) !)
            * ((N + u).choose s * s ! * (N + u - s) !) := by
        rw [hL_def, hDb_def]; ring
      rw [this, e3, e4]
    have hRDa : R * Da = N ! * (N + u) ! := by
      have : R * Da
          = (N.choose (u + s) * (u + s) ! * (N - (u + s)) !)
            * ((N + u).choose b * b ! * (N + u - b) !) := by
        rw [hR_def, hDa_def]; ring
      rw [this, e1, e2]
    have E : L * Db = R * Da := hLDb.trans hRDa.symm
    -- the multiplier comparison `Da ≤ Db`, from two `fact_template`s
    have i1 : (u + s) ! * b ! ≤ (b + u) ! * s ! := by
      have h := fact_template s b u (le_of_lt hsb)
      rwa [Nat.add_comm s u] at h
    have i2 : (N - (u + s)) ! * (N + u - b) ! ≤ (N - (b + u)) ! * (N + u - s) ! := by
      have h := fact_template (N - (b + u)) (N - (u + s)) (2 * u) (by omega)
      have ea : N - (b + u) + 2 * u = N + u - b := by omega
      have eb : N - (u + s) + 2 * u = N + u - s := by omega
      rw [ea, eb] at h
      calc (N - (u + s)) ! * (N + u - b) !
          = (N + u - b) ! * (N - (u + s)) ! := by ring
        _ ≤ (N + u - s) ! * (N - (b + u)) ! := h
        _ = (N - (b + u)) ! * (N + u - s) ! := by ring
    have hDa_le_Db : Da ≤ Db := by
      calc Da = ((u + s) ! * b !) * ((N - (u + s)) ! * (N + u - b) !) := by
                rw [hDa_def]; ring
        _ ≤ ((b + u) ! * s !) * ((N - (b + u)) ! * (N + u - s) !) := Nat.mul_le_mul i1 i2
        _ = Db := by rw [hDb_def]; ring
    have hDa_pos : 0 < Da := by
      rw [hDa_def]
      exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
        (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
    -- conclude by cancelling the positive `Da`
    have hfin : L * Da ≤ R * Da :=
      calc L * Da ≤ L * Db := Nat.mul_le_mul (le_refl L) hDa_le_Db
        _ = R * Da := E
    exact Nat.le_of_mul_le_mul_right hfin hDa_pos
  · -- degenerate: `C(N,b+u) = 0`, so the left side vanishes
    have hz : N.choose (b + u) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, Nat.zero_mul]
    exact Nat.zero_le _

/-- The ratio step rewritten via the boundary increments: cross-multiplied
ratio growth is equivalent to a comparison of the two increments weighted by the
opposite probability. -/
lemma C_ratio_step (P : Params) (n k : ℕ) :
    PC P n (k + 1) * PI P n k > PC P n k * PI P n (k + 1) ↔
      PC P n k * (PI P n k - PI P n (k + 1))
        > PI P n k * (PC P n k - PC P n (k + 1)) := by
  constructor <;> intro h <;> nlinarith [h]

/-- Cross-multiplied ratio growth is, after cancelling the positive factor
`C(n,k)`, exactly the "core" comparison `PC·pI^k·Bsum(pC) > PI·pC^k·Bsum(pI)`. -/
lemma core_iff_ratio (P : Params) (n k : ℕ) (hk : k ≤ n) :
    PC P n (k + 1) * PI P n k > PC P n k * PI P n (k + 1) ↔
      PC P n k * P.pI ^ k * Bsum P n k P.pC
        > PI P n k * P.pC ^ k * Bsum P n k P.pI := by
  rw [C_ratio_step, C_delta_PI P n k hk, C_delta_PC P n k hk]
  have hc : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  constructor <;> intro h <;> nlinarith [hc, h]

/-! ## Symmetry of the core comparison under `swap`. -/

/-- The two probabilities coincide when `pC = pI` (then `P` and `swap P` agree). -/
lemma M_eq_swap_of_eq (P : Params) (n c i : ℕ) (h : P.pC = P.pI) :
    M P n c i = M (swap P) n c i := by
  unfold M; rw [swap_pC, swap_pI, swap_pR, h]

lemma PC_eq_PI_of_pC_eq_pI (P : Params) (n k : ℕ) (h : P.pC = P.pI) :
    PC P n k = PI P n k := by
  rw [B_swap]; unfold PC
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [M_eq_swap_of_eq P n c i h]

/-- Swapping the parameters exchanges the two sides of the core comparison:
`LHS_core (swap P) = RHS_core P`. -/
lemma core_L_swap (P : Params) (n k : ℕ) :
    PC (swap P) n k * (swap P).pI ^ k * Bsum (swap P) n k (swap P).pC
      = PI P n k * P.pC ^ k * Bsum P n k P.pI := by
  rw [← B_swap, swap_pI, swap_pC, Bsum_swap]

/-- `RHS_core (swap P) = LHS_core P`. -/
lemma core_R_swap (P : Params) (n k : ℕ) :
    PI (swap P) n k * (swap P).pC ^ k * Bsum (swap P) n k (swap P).pI
      = PC P n k * P.pI ^ k * Bsum P n k P.pC := by
  rw [B_swap (swap P) n k, swap_swap, swap_pC, swap_pI, Bsum_swap]

/-! ## A_trust_iff_ratio — trust-monotonicity is ratio-monotonicity. -/

/-- Abstract monotonicity: for positive `a b c d`, `a/(a+b) < c/(c+d)` iff the
cross-product `a*d < c*b`.  (`x ↦ x/(x+y)` is increasing in the ratio `x/y`.) -/
lemma trust_lt_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : a / (a + b) < c / (c + d) ↔ a * d < c * b := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Raising the threshold raises trust iff the consensus *ratio* `PC/PI` rises,
expressed in cross-multiplied form (no division). -/
lemma A_trust_iff_ratio (P : Params) (n k : ℕ) (hn : 1 ≤ n) (hk1 : k ≤ n)
    (hk2 : k + 1 ≤ n) :
    Trust P n (k + 1) > Trust P n k ↔
      PC P n (k + 1) * PI P n k > PC P n k * PI P n (k + 1) := by
  unfold Trust
  have h := trust_lt_iff (PC_pos P n k hn hk1) (PI_pos P n k hn hk1)
    (PC_pos P n (k + 1) hn hk2) (PI_pos P n (k + 1) hn hk2)
  rw [gt_iff_lt, h]


/-! ## bracket_pos — strict positivity of each slice bracket (the crux of C_core).

Using the slice decomposition, `C_core` reduces to showing each per-`c` bracket
`pC^(c-k)·Bsum(n,c,pI)·Bsum(n,k,pC) − pI^(c-k)·Bsum(n,c,pC)·Bsum(n,k,pI)` is positive.
This is a correlation/FKG-type inequality: its double-sum kernel is antisymmetric
under `(a,b) ↦ (b+u, a−u)` (`u=c−k`), and the weight monotonicity that makes the
paired terms nonnegative is exactly `binom_key`. -/
lemma bracket_pos (P : Params) (n k c : ℕ) (hk1 : 1 ≤ k) (hkc : k < c) (hcn : c ≤ n)
    (hlt : P.pI < P.pC) :
    P.pI ^ (c - k) * Bsum P n c P.pC * Bsum P n k P.pI
      < P.pC ^ (c - k) * Bsum P n c P.pI * Bsum P n k P.pC := by
  have hkn : k ≤ n := by omega
  have hpC := P.pC_pos
  have hpI := P.pI_pos
  have hpR := P.pR_pos
  set u := c - k with hu
  -- weight and kernel of the (a,b) double sum
  set W : ℕ → ℕ → ℝ := fun a b =>
    ((n - c).choose a : ℝ) * ((n - k).choose b : ℝ) * P.pR ^ (n - c - a) * P.pR ^ (n - k - b)
    with hW
  set Kr : ℕ → ℕ → ℝ := fun a b =>
    P.pC ^ (u + b) * P.pI ^ a - P.pI ^ (u + b) * P.pC ^ a with hKr
  -- a helper to expand `e * (∑ F) * (∑ G)` into a double sum
  have expand : ∀ (e : ℝ) (F G : ℕ → ℝ),
      e * (∑ a ∈ range c, F a) * (∑ b ∈ range k, G b)
        = ∑ a ∈ range c, ∑ b ∈ range k, e * F a * G b := by
    intro e F G
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  -- the core identity: RHS - LHS = double sum of W*Kr
  have key : P.pC ^ u * Bsum P n c P.pI * Bsum P n k P.pC
      - P.pI ^ u * Bsum P n c P.pC * Bsum P n k P.pI
      = ∑ a ∈ range c, ∑ b ∈ range k, W a b * Kr a b := by
    rw [Bsum_eq P n c hcn, Bsum_eq P n c hcn, Bsum_eq P n k hkn, Bsum_eq P n k hkn]
    rw [expand (P.pC ^ u)
          (fun a => ((n - c).choose a : ℝ) * P.pI ^ a * P.pR ^ (n - c - a))
          (fun b => ((n - k).choose b : ℝ) * P.pC ^ b * P.pR ^ (n - k - b)),
        expand (P.pI ^ u)
          (fun a => ((n - c).choose a : ℝ) * P.pC ^ a * P.pR ^ (n - c - a))
          (fun b => ((n - k).choose b : ℝ) * P.pI ^ b * P.pR ^ (n - k - b))]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hW, hKr]
    ring
  -- reduce the goal to positivity of the double sum
  rw [← sub_pos]
  have hgoal : P.pC ^ (c - k) * Bsum P n c P.pI * Bsum P n k P.pC
      - P.pI ^ (c - k) * Bsum P n c P.pC * Bsum P n k P.pI
      = ∑ a ∈ range c, ∑ b ∈ range k, W a b * Kr a b := by
    rw [← hu]; exact key
  rw [hgoal]
  -- nonnegativity of the weight
  have hWnn : ∀ a b, 0 ≤ W a b := by
    intro a b; rw [hW]; positivity
  -- strict kernel positivity when the exponent of the larger probability dominates
  have kernel_pos : ∀ (m a : ℕ), a < m → P.pI ^ m * P.pC ^ a < P.pC ^ m * P.pI ^ a := by
    intro m a ham
    have hpow : P.pI ^ (m - a) < P.pC ^ (m - a) :=
      pow_lt_pow_left₀ hlt (le_of_lt hpI) (by omega)
    have h1 : P.pI ^ m = P.pI ^ (m - a) * P.pI ^ a := by rw [← pow_add]; congr 1; omega
    have h2 : P.pC ^ m = P.pC ^ (m - a) * P.pC ^ a := by rw [← pow_add]; congr 1; omega
    calc P.pI ^ m * P.pC ^ a = P.pI ^ (m - a) * (P.pI ^ a * P.pC ^ a) := by rw [h1]; ring
      _ < P.pC ^ (m - a) * (P.pI ^ a * P.pC ^ a) := by
            apply mul_lt_mul_of_pos_right hpow; positivity
      _ = P.pC ^ m * P.pI ^ a := by rw [h2]; ring
  -- the kernel is positive on the relevant region
  have hKr_pos : ∀ a b, a < u + b → 0 < Kr a b := by
    intro a b hab
    rw [hKr]
    have := kernel_pos (u + b) a hab
    linarith
  -- weight monotonicity, the heart of the pairing, supplied by `binom_key`
  have Wmono : ∀ a b, u ≤ a → a < c → b < k → a < u + b →
      W (b + u) (a - u) ≤ W a b := by
    intro a b hua hac hbk hab
    have hnk : n - k = (n - c) + u := by omega
    have hnat : (n - c).choose (b + u) * (n - k).choose (a - u)
        ≤ (n - c).choose a * (n - k).choose b := by
      have hkey := binom_key (n - c) u (a - u) b (by omega)
      rw [show u + (a - u) = a by omega] at hkey
      rw [hnk]; exact hkey
    by_cases hzero : (n - c).choose (b + u) * (n - k).choose (a - u) = 0
    · have hz : W (b + u) (a - u) = 0 := by
        have hz2 : ((n - c).choose (b + u) : ℝ) * ((n - k).choose (a - u) : ℝ) = 0 := by
          rw [← Nat.cast_mul, hzero, Nat.cast_zero]
        simp only [hW]
        linear_combination
          (P.pR ^ (n - c - (b + u)) * P.pR ^ (n - k - (a - u))) * hz2
      rw [hz]; exact hWnn a b
    · -- all four coefficients in range, so the `pR` powers match
      have hbu : b + u ≤ n - c := by
        by_contra h
        apply hzero
        rw [show (n - c).choose (b + u) = 0 from Nat.choose_eq_zero_of_lt (by omega),
          Nat.zero_mul]
      have hau : a - u ≤ n - k := by
        by_contra h
        apply hzero
        rw [show (n - k).choose (a - u) = 0 from Nat.choose_eq_zero_of_lt (by omega),
          Nat.mul_zero]
      have han : a ≤ n - c := by
        by_contra h
        apply hzero
        have h0 : (n - c).choose a * (n - k).choose b = 0 := by
          rw [show (n - c).choose a = 0 from Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]
        omega
      have hbn : b ≤ n - k := by
        by_contra h
        apply hzero
        have h0 : (n - c).choose a * (n - k).choose b = 0 := by
          rw [show (n - k).choose b = 0 from Nat.choose_eq_zero_of_lt (by omega), Nat.mul_zero]
        omega
      have hExp : (n - c - (b + u)) + (n - k - (a - u)) = (n - c - a) + (n - k - b) := by omega
      have hReq : P.pR ^ (n - c - (b + u)) * P.pR ^ (n - k - (a - u))
          = P.pR ^ (n - c - a) * P.pR ^ (n - k - b) := by
        rw [← pow_add, ← pow_add, hExp]
      have hcast : ((n - c).choose (b + u) : ℝ) * ((n - k).choose (a - u) : ℝ)
          ≤ ((n - c).choose a : ℝ) * ((n - k).choose b : ℝ) := by exact_mod_cast hnat
      simp only [hW]
      calc ((n - c).choose (b + u) : ℝ) * ((n - k).choose (a - u) : ℝ)
              * P.pR ^ (n - c - (b + u)) * P.pR ^ (n - k - (a - u))
          = (((n - c).choose (b + u) : ℝ) * ((n - k).choose (a - u) : ℝ))
              * (P.pR ^ (n - c - (b + u)) * P.pR ^ (n - k - (a - u))) := by ring
        _ = (((n - c).choose (b + u) : ℝ) * ((n - k).choose (a - u) : ℝ))
              * (P.pR ^ (n - c - a) * P.pR ^ (n - k - b)) := by rw [hReq]
        _ ≤ (((n - c).choose a : ℝ) * ((n - k).choose b : ℝ))
              * (P.pR ^ (n - c - a) * P.pR ^ (n - k - b)) := by
            apply mul_le_mul_of_nonneg_right hcast; positivity
        _ = ((n - c).choose a : ℝ) * ((n - k).choose b : ℝ)
              * P.pR ^ (n - c - a) * P.pR ^ (n - k - b) := by ring
  -- the kernel is anti-symmetric under the pairing `(a,b) ↦ (b+u, a-u)`
  have hKr_neg : ∀ a b, u ≤ a → Kr (b + u) (a - u) = - Kr a b := by
    intro a b hua
    simp only [hKr]
    rw [show u + (a - u) = a by omega]; ring
  set F : ℕ → ℝ := fun a => ∑ b ∈ range k, W a b * Kr a b with hF
  -- split the outer range at `u`
  have hsplit : (∑ a ∈ range c, F a)
      = (∑ a ∈ range u, F a) + ∑ a ∈ Ico u c, F a := by
    rw [range_eq_Ico, range_eq_Ico]
    exact (Finset.sum_Ico_consecutive F (Nat.zero_le u) (by omega)).symm
  rw [show (∑ a ∈ range c, ∑ b ∈ range k, W a b * Kr a b) = ∑ a ∈ range c, F a from rfl, hsplit]
  -- the `a < u` block is strictly positive
  have hExtra : 0 < ∑ a ∈ range u, F a := by
    apply Finset.sum_pos'
    · intro a ha
      rw [Finset.mem_range] at ha
      rw [hF]
      apply Finset.sum_nonneg
      intro b hb
      rw [Finset.mem_range] at hb
      exact mul_nonneg (hWnn a b) (le_of_lt (hKr_pos a b (by omega)))
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hF]
      apply Finset.sum_pos'
      · intro b hb
        rw [Finset.mem_range] at hb
        exact mul_nonneg (hWnn 0 b) (le_of_lt (hKr_pos 0 b (by omega)))
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        have hWpos : 0 < W 0 0 := by
          rw [hW]; simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]; positivity
        exact mul_pos hWpos (hKr_pos 0 0 (by omega))
  -- the `a ≥ u` block is nonnegative, by the involution doubling
  have hPair : 0 ≤ ∑ a ∈ Ico u c, F a := by
    simp only [hF]
    rw [← Finset.sum_product']
    set prod := (Ico u c) ×ˢ (range k) with hprod
    set σ : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 + u, p.1 - u) with hσ
    have hmem : ∀ p ∈ prod, σ p ∈ prod := by
      intro p hp
      simp only [hprod, Finset.mem_product, Finset.mem_Ico, Finset.mem_range, hσ] at hp ⊢
      omega
    have hinv : ∀ p ∈ prod, σ (σ p) = p := by
      intro p hp
      simp only [hprod, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hp
      simp only [hσ, Prod.ext_iff]
      omega
    -- reindex by σ
    have hreindex : (∑ p ∈ prod, W p.1 p.2 * Kr p.1 p.2)
        = ∑ p ∈ prod, W (σ p).1 (σ p).2 * Kr (σ p).1 (σ p).2 := by
      refine Finset.sum_nbij' σ σ hmem hmem hinv hinv ?_
      intro p hp
      rw [hinv p hp]
    -- f(σp) = - W(σp) * Kr(p)
    have hB : (∑ p ∈ prod, W (σ p).1 (σ p).2 * Kr (σ p).1 (σ p).2)
        = - ∑ p ∈ prod, W (σ p).1 (σ p).2 * Kr p.1 p.2 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hprod, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hp
      have : Kr (σ p).1 (σ p).2 = - Kr p.1 p.2 := by
        rw [hσ]; exact hKr_neg p.1 p.2 (by omega)
      rw [this]; ring
    -- 2A = ∑ (W p - W σp) Kr p
    have hdouble : 2 * (∑ p ∈ prod, W p.1 p.2 * Kr p.1 p.2)
        = ∑ p ∈ prod, (W p.1 p.2 - W (σ p).1 (σ p).2) * Kr p.1 p.2 := by
      have hAeq : (∑ p ∈ prod, W p.1 p.2 * Kr p.1 p.2)
          = - ∑ p ∈ prod, W (σ p).1 (σ p).2 * Kr p.1 p.2 := hreindex.trans hB
      have hexp : ∑ p ∈ prod, (W p.1 p.2 - W (σ p).1 (σ p).2) * Kr p.1 p.2
          = (∑ p ∈ prod, W p.1 p.2 * Kr p.1 p.2)
            - ∑ p ∈ prod, W (σ p).1 (σ p).2 * Kr p.1 p.2 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p _; ring
      rw [hexp]; linarith [hAeq]
    -- each term is nonnegative
    have hterm : ∀ p ∈ prod, 0 ≤ (W p.1 p.2 - W (σ p).1 (σ p).2) * Kr p.1 p.2 := by
      intro p hp
      rw [hprod, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hp
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      rcases lt_trichotomy p.1 (u + p.2) with hlt' | heq' | hgt'
      · -- Kr > 0, W p ≥ W σp
        have hKpos : 0 < Kr p.1 p.2 := hKr_pos p.1 p.2 hlt'
        have hWle : W (σ p).1 (σ p).2 ≤ W p.1 p.2 := by
          rw [hσ]; exact Wmono p.1 p.2 h1 h2 h3 hlt'
        nlinarith [hKpos, hWle]
      · -- Kr = 0
        have hz : Kr p.1 p.2 = 0 := by rw [hKr, heq']; ring
        simp [hz]
      · -- Kr < 0, W p ≤ W σp
        have hKneg : Kr p.1 p.2 < 0 := by
          rw [hKr]
          have := kernel_pos p.1 (u + p.2) (by omega)
          nlinarith [this]
        have hWle : W p.1 p.2 ≤ W (σ p).1 (σ p).2 := by
          rw [hσ]
          have hh := Wmono (p.2 + u) (p.1 - u) (by omega) (by omega) (by omega) (by omega)
          rw [show (p.1 - u) + u = p.1 by omega, show (p.2 + u) - u = p.2 by omega] at hh
          exact hh
        nlinarith [hKneg, hWle]
    have hsum_nn : 0 ≤ ∑ p ∈ prod, (W p.1 p.2 - W (σ p).1 (σ p).2) * Kr p.1 p.2 :=
      Finset.sum_nonneg hterm
    linarith [hdouble, hsum_nn]
  linarith

/-! ## Assembly — `MainProp` modulo the single core inequality `C_core`. -/

/-- **Reduction of the conjecture to one inequality.**  Granting `C_core` — that
`pC > pI` forces the core comparison for every valid `(P, n, k)` — the full
biconditional `MainProp` follows, via `A_trust_iff_ratio`, `C_ratio_step`,
`C_delta`, and the `swap` symmetry (trichotomy on `pC` vs `pI`). -/
lemma main_of_core
    (Hcore : ∀ (P : Params) (n k : ℕ), 1 ≤ n → 1 ≤ k → k + 1 ≤ n → P.pC > P.pI →
      PC P n k * P.pI ^ k * Bsum P n k P.pC
        > PI P n k * P.pC ^ k * Bsum P n k P.pI) :
    MainProp := by
  intro P n k hn hk1 hk2
  have h1n : 1 ≤ n := by omega
  have hkn : k ≤ n := by omega
  rw [A_trust_iff_ratio P n k h1n hkn hk2, core_iff_ratio P n k hkn]
  constructor
  · intro hcore
    by_contra hle
    rw [not_lt] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hlt' : (swap P).pC > (swap P).pI := by rw [swap_pC, swap_pI]; exact hlt
      have hsw := Hcore (swap P) n k h1n hk1 hk2 hlt'
      rw [core_L_swap, core_R_swap] at hsw
      linarith
    · rw [PC_eq_PI_of_pC_eq_pI P n k heq, heq] at hcore
      exact absurd hcore (lt_irrefl _)
  · intro hgt
    exact Hcore P n k h1n hk1 hk2 hgt

end ConjectureProof
