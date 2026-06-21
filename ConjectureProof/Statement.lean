/-
  ╔══════════════════════════════════════════════════════════════════════╗
  ║  FROZEN FILE — DO NOT EDIT.                                            ║
  ║  This file states the conjecture. The agent is forbidden to touch it. ║
  ║  Its sha256 is checked by scripts/check_integrity.sh on every run.    ║
  ║  After editing, refreeze with:                                        ║
  ║    sha256sum ConjectureProof/Statement.lean > scripts/statement.sha256║
  ╚══════════════════════════════════════════════════════════════════════╝

  Trust monotonicity for homogeneous voting ensembles.

  An agent answers a fixed question; its single-shot answer is Correct, the
  dominant specious Incorrect answer, or some Random other answer, with
  probabilities (pC, pI, pR).  In the paper's parameters,
      pC = (1-η)(1-δ),   pI = (1-η)δ,   pR = η,
  and positivity of all three is exactly 0 < δ < 1 and 0 < η < 1.  Note
      pC - pI = (1-η)(1-2δ),     so for η < 1:   pC > pI  ⟺  δ < ½.

  n agents vote with threshold k.  An answer wins iff it reaches k votes and is
  the strict plurality; otherwise the verdict is "no consensus".  Trust is the
  fraction of conclusive verdicts that are correct.  The conjecture: raising the
  threshold strictly raises trust iff the correct answer is individually more
  likely than the specious one.
-/
import Mathlib

namespace ConjectureProof

/-- An agent's single-answer distribution over {Correct, specious Incorrect,
Random}, abstracted to three strictly-positive reals summing to one.  Strict
positivity of `pR` (i.e. η > 0) is required: with η = 0 trust is locally
constant below the majority line and the strict claim fails. -/
structure Params where
  pC : ℝ
  pI : ℝ
  pR : ℝ
  pC_pos : 0 < pC
  pI_pos : 0 < pI
  pR_pos : 0 < pR
  sum_one : pC + pI + pR = 1

/-- Multinomial weight of the outcome "c correct, i specious, n−c−i random"
among n independent agents.  Written with `C(n,c)·C(n−c,i)` so the coefficient
stays in ℕ before casting (no factorial division). -/
noncomputable def M (P : Params) (n c i : ℕ) : ℝ :=
  (n.choose c : ℝ) * ((n - c).choose i : ℝ)
    * P.pC ^ c * P.pI ^ i * P.pR ^ (n - c - i)

/-- Probability the ensemble reaches a CORRECT consensus at threshold k:
the correct count `c` is at least `k` and is the strict plurality (`i < c`). -/
noncomputable def PC (P : Params) (n k : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc k n, ∑ i ∈ Finset.range c, if c + i ≤ n then M P n c i else 0

/-- Probability the ensemble reaches an INCORRECT (specious) consensus at
threshold k: the specious count `i` is at least `k` and the strict plurality. -/
noncomputable def PI (P : Params) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc k n, ∑ c ∈ Finset.range i, if c + i ≤ n then M P n c i else 0

/-- Trust: the fraction of conclusive verdicts that are correct,
`P(C) / (P(C) + P(I))`. -/
noncomputable def Trust (P : Params) (n k : ℕ) : ℝ :=
  PC P n k / (PC P n k + PI P n k)

/-- **THE CONJECTURE.**  For any nontrivial agent distribution (all three
outcome probabilities positive) and any ensemble of size `n ≥ 2` with threshold
`k` in `[1, n-1]`, raising the threshold by one strictly increases trust iff the
correct answer is individually more likely than the specious one (δ < ½). -/
def MainProp : Prop :=
  ∀ (P : Params) (n k : ℕ), 2 ≤ n → 1 ≤ k → k + 1 ≤ n →
    (Trust P n (k + 1) > Trust P n k ↔ P.pC > P.pI)

end ConjectureProof
