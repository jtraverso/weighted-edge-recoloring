module

public import GridHost

@[expose] public section


namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

theorem forbidden_card {q b : ℕ} (m : Marked q ↪ CellVertex q b) :
    (forbidden m).card = 2*Nat.sqrt q+4 := by
  simp [forbidden,Marked,Fintype.card_sum,Fintype.card_prod]
  omega

theorem coordinates_apply {q b : ℕ} (m : Marked q ↪ CellVertex q b)
    (x : Ordinary (Fin (Nat.sqrt q)) (Intact m)) : coordinates m x = placeFn m x := rfl

noncomputable def holePosition {q b : ℕ} (m : Marked q ↪ CellVertex q b) : Fin (Nat.sqrt q) ↪ CellVertex q b :=
  ⟨fun h => m (.inr (.inr (h,false))),by
    intro h k e
    have heus := m.injective e
    exact congrArg Prod.fst (Sum.inr.inj (Sum.inr.inj heus))⟩

theorem support_degrees {q b : ℕ} (m : Marked q ↪ CellVertex q b) :
    (∀ x, (univ.filter (support m x)).card = b*(2*q-1)) ∧
    (∀ y, (univ.filter (fun x => support m x y)).card = b*(2*q-1)) := by
  classical
  have left (x : Ordinary (Fin (Nat.sqrt q)) (Intact m)) : (univ.filter (support m x)).card = b*(2*q-1) := by
    have eq : (univ.filter (support m x)).map (coordinates m).toEmbedding = gridNeighbors (coordinates m x) := by
      ext y
      simp only [mem_map,mem_filter,mem_univ,true_and,support,Equiv.toEmbedding_apply]
      exact ⟨fun ⟨z,h,e⟩ => e ▸ h,fun h => ⟨(coordinates m).symm y,by simpa using h,by simp⟩⟩
    rw [← gridNeighbors_card (coordinates m x),← eq,card_map]
  refine ⟨left,fun y => ?_⟩
  have e : (univ.filter fun x => support m x y) = (univ.filter (support m y)) := by
    ext z
    rw [mem_filter,mem_filter]
    exact and_congr_right (fun _ => gridNeighbors_symmetric (coordinates m z) (coordinates m y))
  exact (congrArg card e).trans (left y)
end WeightedPaper.Repair.Grid
