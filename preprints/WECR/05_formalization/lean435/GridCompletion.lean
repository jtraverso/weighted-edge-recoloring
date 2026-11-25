import GridDegrees
import GridLayout

namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

variable {q b : ℕ}

set_option maxHeartbeats 1500000 in
theorem factorization_of_grid_layout (hb : 0 < b) (hq : 12 ≤ q)
    (m : Marked q ↪ CellVertex q b) :
    let d := b*(2*q-1)
    let C := CrossingCopy (capacity (support m) d)
    ∃ color : (Fin d × Bool) ⊕ C → Fin (3*d),
      ∀ (v : Side (Fin (Nat.sqrt q)) (Intact m) ⊕ Side (Fin (Nat.sqrt q)) (Intact m)) i,
        (univ.filter (fun e => color (.inl e) = i ∧ (endpoint 0 e = v ∨ endpoint 1 e = v))).card +
        ((univ : Finset C).filter (fun e => color (.inr e) = i ∧
          (Sum.inl e.1.1 = v ∨ Sum.inr e.1.2 = v))).card = 1 := by
  intro d C
  have forbid h : holePosition m h ∈ forbidden m := mem_map.mpr ⟨_,mem_univ _,rfl⟩
  obtain ⟨f,tag,p,good,once,swap,stay⟩ := grid_detour_matchings b q hb hq (holePosition m)
    (forbidden m) (by rw [forbidden_card]) forbid
  have uses (i : Fin d) h :
      ordinary (support m) (mark h false) (ordinaryHelper (f i h)) ∧
      ordinary (support m) (ordinaryHelper (f i h)) (mark h false) := ⟨(good i h).1,(good i h).2.1⟩
  have bound := grid_round_spending (support m) d f tag p uses once swap stay
  obtain ⟨regA,regB⟩ := grid_degrees (support m) d (support_degrees m).1 (support_degrees m).2
  let V := Side (Fin (Nat.sqrt q)) (Intact m)
  let c := capacity (support m) d
  have loop (e : Fin d × Bool) : (endpoint 0 e : V ⊕ V) ≠ endpoint 1 e := by
    obtain ⟨i,z⟩ := e
    cases z <;> simp [endpoint,V,leftInternal,rightInternal,Side,Ordinary]
  have row i (x : V) : (univ.filter (fun e : Fin d × Bool => e.1 = i ∧
      (endpoint 0 e = .inl x ∨ endpoint 1 e = .inl x))).card +
      (univ.filter (fun y => (x,y) ∈ roundPairs (p i))).card = 1 := by
    have f := internal_seed_count d i x
    have g := roundRows (p i) x
    calc
      _ = (if x ∈ Set.range (leftInternal : Fin 2 → V) then 1 else 0) + (if x ∈ Set.range (leftFree : Free (Fin (Nat.sqrt q)) (Intact m) ↪ V) then 1 else 0) := by
        convert congrArg₂ (· + ·) f g using 2 <;> first | (congr 1; ext; simp) | (split_ifs <;> rfl)
      _ = 1 := by
        by_cases e : x ∈ Set.range (leftInternal : Fin 2 → V)
        · have no : ¬ (x ∈ Set.range (leftFree : Free (Fin (Nat.sqrt q)) (Intact m) ↪ V)) := fun h => (leftFree_range x).mp h e
          simp only [ite_eq_left e,ite_eq_right no,add_zero]
        · have yes : x ∈ Set.range (leftFree : Free (Fin (Nat.sqrt q)) (Intact m) ↪ V) := (leftFree_range x).mpr e
          simp only [ite_eq_right e,ite_eq_left yes,zero_add]
  have col i (y : V) : (univ.filter (fun e : Fin d × Bool => e.1 = i ∧
      (endpoint 0 e = .inr y ∨ endpoint 1 e = .inr y))).card +
      (univ.filter (fun x => (x,y) ∈ roundPairs (p i))).card = 1 := by
    have f := internal_seed_count' d i y
    have g := roundCols (p i) y
    calc
      _ = (if y ∈ Set.range (rightInternal : Fin 2 → V) then 1 else 0) + (if y ∈ Set.range (rightFree : Free (Fin (Nat.sqrt q)) (Intact m) ↪ V) then 1 else 0) := by
        convert congrArg₂ (· + ·) f g using 2 <;> first | (congr 1; ext; simp) | (split_ifs <;> rfl)
      _ = 1 := by
        by_cases e : y ∈ Set.range (rightInternal : Fin 2 → V)
        · have no : ¬ (y ∈ Set.range (rightFree : Free (Fin (Nat.sqrt q)) (Intact m) ↪ V)) := fun h => (rightFree_range y).mp h e
          simp only [ite_eq_left e,ite_eq_right no,add_zero]
        · have yes : y ∈ Set.range (rightFree : Free (Fin (Nat.sqrt q)) (Intact m) ↪ V) := (rightFree_range y).mpr e
          simp only [ite_eq_right e,ite_eq_left yes,zero_add]
  have kD : Fintype.card (Fin d) ≤ 3*d := by simp; omega
  obtain ⟨_,color,_,h⟩ := factorize_regular_host c (endpoint 0) (endpoint 1) loop Prod.fst
    (fun i => roundPairs (p i)) (3*d) kD
    (fun x => by convert regA x using 2 <;> congr 1 <;> ext <;> simp)
    (fun y => by convert regB y using 2 <;> congr 1 <;> ext <;> simp)
    (fun i x => by convert row i x using 2 <;> congr 1 <;> ext <;> simp)
    (fun i y => by convert col i y using 2 <;> congr 1 <;> ext <;> simp) bound
  refine ⟨color,fun v i => ?_⟩
  convert h v i using 2 <;> congr 1 <;> ext <;> simp
end WeightedPaper.Repair.Grid
