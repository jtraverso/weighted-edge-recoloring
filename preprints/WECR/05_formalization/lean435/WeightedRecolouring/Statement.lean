module

public import OverfullWork.EquitableComponents

@[expose] public section


namespace WeightedRecolouring
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

/-- The weight of the vertices covered by a colour's matching. -/
def load (C : M.EdgeColoring k) (w : V → ℝ) (i : Fin k) : ℝ :=
  ∑ v, w v * (C.colourGraph i).degree v

end WeightedRecolouring
