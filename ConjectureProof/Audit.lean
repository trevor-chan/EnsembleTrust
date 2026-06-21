/-
  AXIOM AUDIT. This prints the axioms the final theorem actually depends on.
  A genuine proof shows only:  [propext, Classical.choice, Quot.sound]
  If `sorryAx` appears, the proof is incomplete/faked. If any other name
  appears, an extra axiom was smuggled in. check_integrity.sh parses this.
-/
import ConjectureProof.Main

open ConjectureProof

#print axioms main_theorem
