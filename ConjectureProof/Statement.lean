/-
  ╔══════════════════════════════════════════════════════════════════════╗
  ║  FROZEN FILE — DO NOT EDIT.                                            ║
  ║  This file states the conjecture. The agent is forbidden to touch it. ║
  ║  Its sha256 is checked by scripts/check_integrity.sh on every run.    ║
  ║                                                                        ║
  ║  YOU (the human) edit this ONCE to encode your real conjecture, then  ║
  ║  run:   sha256sum ConjectureProof/Statement.lean > scripts/statement.sha256
  ║  and commit. After that, it is frozen for the agent.                  ║
  ╚══════════════════════════════════════════════════════════════════════╝
-/
import Mathlib   -- pulls all of mathlib; fine for a single proof. Narrow later if you want faster builds.

namespace ConjectureProof

/-
  Put any DEFINITIONS your conjecture needs here. Example placeholder:
  a "perfect-ish" predicate. Replace all of this with your real objects.
-/
def IsExample (n : ℕ) : Prop := 0 < n ∧ n % 2 = 0

/--
  THE CONJECTURE. Replace the body with the precise proposition your Python
  simulations support. This is the single source of truth the agent proves.
  It must be a closed `Prop` (no free variables).
-/
def MainProp : Prop :=
  ∀ n : ℕ, IsExample n → 2 ≤ n

end ConjectureProof
