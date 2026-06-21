/-
  FINAL ASSEMBLY.

  The agent must produce exactly this declaration:

      theorem main_theorem : MainProp := <proof>

  The type MUST be `MainProp` (the frozen proposition). The integrity check
  greps for the literal signature `main_theorem : MainProp`, so the agent
  cannot quietly prove a weaker statement.
-/
import ConjectureProof.Statement
import ConjectureProof.Lemmas

namespace ConjectureProof

theorem main_theorem : MainProp := by
  unfold MainProp
  intro n h
  unfold IsExample at h
  omega

end ConjectureProof
