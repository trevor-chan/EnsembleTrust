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
`C(n,c)·C(n-c,i) = C(n,i)·C(n-i,c)` (both equal `n! / (c! i! (n-c-i)!)`). -/
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

end ConjectureProof
