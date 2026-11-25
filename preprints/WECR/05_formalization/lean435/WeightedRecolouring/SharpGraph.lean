module

public import WeightedRecolouring.Statement
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fin.VecNotation

@[expose] public section


namespace WeightedRecolouring.Example
open Finset SimpleGraph

def edge (i : Fin 6) : Sym2 (Fin 6) :=
  ![s(0,1),s(0,2),s(1,2),s(0,3),s(3,5),s(1,4)] i

/-- The triangle abc with additional edges ad, de and bf. -/
def graph : MultiGraph (Fin 6) where
  mult e := if ∃ j, edge j=e then 1 else 0
  loopless := by
    intro e h
    have hd : ∀ j,(edge j).IsDiag → False := by decide
    split_ifs with he
    · obtain ⟨j,rfl⟩ := he
      exact False.elim (hd j h)
    · rfl

def heavy (v : Fin 6) : ℕ := if v=2 ∨ v=4 then 1 else 0

def weights (v : Fin 6) : ℝ := heavy v

def support : SimpleGraph (Fin 6) where
  Adj u v := 0<graph.mult s(u,v)
  symm := ⟨fun _ _ h => by simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨fun v h => by
    have hz := graph.loopless s(v,v) (by simp)
    omega⟩

instance : DecidableRel support.Adj := fun u v =>
  inferInstanceAs (Decidable (0<graph.mult s(u,v)))

end WeightedRecolouring.Example
