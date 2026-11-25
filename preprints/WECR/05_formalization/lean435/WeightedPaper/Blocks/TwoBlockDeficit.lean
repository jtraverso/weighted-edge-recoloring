import WeightedPaper.Blocks.BlockDeficit

namespace WeightedPaper.Blocks
open Finset

private def deltaTwo (j : Bool) : ℤ := if j then -1 else 1
private def onlyBlock (j : Bool) (_ : Unit) (k : Bool) : Prop := k = j
private def eitherBlock (_ : Unit) (_ : Bool) : Prop := True

/-- The greatest violated cut drops from two to one to zero as the right
exception and then the left exception become eligible in both blocks. -/
theorem two_block_deficits :
    transportDeficit (onlyBlock false) (onlyBlock true) deltaTwo = 2 ∧
    transportDeficit (onlyBlock false) eitherBlock deltaTwo = 1 ∧
    transportDeficit eitherBlock eitherBlock deltaTwo = 0 := by
  classical
  have cuts : (univ : Finset (Finset Bool)) = {∅,{false},{true},{false,true}} := by decide
  simp [transportDeficit, cutGap, cuts, onlyBlock, eitherBlock, deltaTwo, Bool.forall_bool]

#print axioms two_block_deficits
end WeightedPaper.Blocks
