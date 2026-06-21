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

-- Example of how a frontier lemma looks. Delete and replace with your tree.
-- Mark unfinished lemmas by leaving them OUT of the build (commented) rather
-- than stubbing them, so the build stays honest.

-- lemma step_one (n : ℕ) (h : IsExample n) : 0 < n := h.1

end ConjectureProof
