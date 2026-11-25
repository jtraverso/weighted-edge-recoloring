import GridHost

namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

abbrev Marked (q : ℕ) := Fin 2 ⊕ (Fin 2 ⊕ (Fin (Nat.sqrt q) × Bool))

theorem two_root_le (q : ℕ) (hq : 12 ≤ q) : 2*Nat.sqrt q ≤ q := by
  have h := Nat.sqrt_le q
  by_cases small : Nat.sqrt q ≤ 1
  · omega
  · nlinarith

/-- A fixed placement in the original grid. Internal endpoints use rows 0
and q/2. All switched positions use row q/2+1. -/
noncomputable def markedEmbedding (q b : ℕ) (hq : 12 ≤ q) (hb : 0 < b) :
    Marked q ↪ CellVertex q b := by
  let col : Fin (Nat.sqrt q) × Bool ↪ Fin q :=
    (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by
      simpa [mul_comm] using two_root_le q hq))
  let l (i : Fin 2) : CellVertex q b := (⟨0,by omega⟩,Fin.castLE (by omega) i,⟨0,hb⟩)
  let r (i : Fin 2) : CellVertex q b := (⟨q/2,by omega⟩,Fin.castLE (by omega) i,⟨0,hb⟩)
  let sw (j : Fin (Nat.sqrt q) × Bool) : CellVertex q b := (⟨q/2+1,by omega⟩,col j,⟨0,hb⟩)
  refine ⟨Sum.elim l (Sum.elim r sw),?_⟩
  intro u v e
  rcases u with u | (u|u) <;> rcases v with v | (v|v)
  · have h : u.val = v.val := congrArg (fun c : CellVertex q b => c.2.1.val) e
    obtain rfl := Fin.ext h
    rfl
  · have h : 0 = q/2 := congrArg (fun c : CellVertex q b => c.1.val) e
    omega
  · have h : 0 = q/2+1 := congrArg (fun c : CellVertex q b => c.1.val) e
    omega
  · have h : q/2 = 0 := congrArg (fun c : CellVertex q b => c.1.val) e
    omega
  · have h : u.val = v.val := congrArg (fun c : CellVertex q b => c.2.1.val) e
    obtain rfl := Fin.ext h
    rfl
  · have h : q/2 = q/2+1 := congrArg (fun c : CellVertex q b => c.1.val) e
    omega
  · have h : q/2+1 = 0 := congrArg (fun c : CellVertex q b => c.1.val) e
    omega
  · have h : q/2+1 = q/2 := congrArg (fun c : CellVertex q b => c.1.val) e
    omega
  · have h : col u = col v := congrArg (fun c : CellVertex q b => c.2.1) e
    exact congrArg (fun j => Sum.inr (Sum.inr j)) (col.injective h)

noncomputable def forbidden {q b : ℕ} (m : Marked q ↪ CellVertex q b) : Finset (CellVertex q b) :=
  univ.map m

theorem forbidden_card {q b : ℕ} (m : Marked q ↪ CellVertex q b) :
    (forbidden m).card = 2*Nat.sqrt q+4 := by
  simp [forbidden,Marked,Fintype.card_sum,Fintype.card_prod]
  omega

abbrev Intact {q b : ℕ} (m : Marked q ↪ CellVertex q b) := {x // x ∉ forbidden m}

def placeFn {q b : ℕ} (m : Marked q ↪ CellVertex q b) : Ordinary (Fin (Nat.sqrt q)) (Intact m) → CellVertex q b
  | .inl i => m (.inl i)
  | .inr (.inl i) => m (.inr (.inl i))
  | .inr (.inr (.inl s)) => m (.inr (.inr s))
  | .inr (.inr (.inr w)) => w.val

noncomputable def coordinates {q b : ℕ} (m : Marked q ↪ CellVertex q b) :
    Ordinary (Fin (Nat.sqrt q)) (Intact m) ≃ CellVertex q b := by
  classical
  let e : Ordinary (Fin (Nat.sqrt q)) (Intact m) ≃ Marked q ⊕ Intact m :=
    (Equiv.sumAssoc _ _ _).symm.trans ((Equiv.sumAssoc _ _ _).symm.trans
      (Equiv.sumCongr (Equiv.sumAssoc _ _ _) (Equiv.refl _)))
  let mark : Marked q ≃ ↥(forbidden m) := Equiv.ofBijective
    (fun x => ⟨m x,mem_map.mpr ⟨x,mem_univ _,rfl⟩⟩)
    ⟨fun x y e => m.injective (congrArg Subtype.val e),by
      intro y
      obtain ⟨x,_,e⟩ := mem_map.mp y.property
      exact ⟨x,Subtype.ext e⟩⟩
  let comb := e.trans ((Equiv.sumCongr mark (Equiv.refl _)).trans (Equiv.sumCompl fun x => x ∈ forbidden m))
  refine Equiv.ofBijective (placeFn m) ?_
  have he : placeFn m = comb := by
    funext x
    rcases x with i | (j | (s | w)) <;> rfl
  rw [he]
  exact comb.bijective

theorem coordinates_apply {q b : ℕ} (m : Marked q ↪ CellVertex q b)
    (x : Ordinary (Fin (Nat.sqrt q)) (Intact m)) : coordinates m x = placeFn m x := rfl

noncomputable def holePosition {q b : ℕ} (m : Marked q ↪ CellVertex q b) : Fin (Nat.sqrt q) ↪ CellVertex q b :=
  ⟨fun h => m (.inr (.inr (h,false))),by
    intro h k e
    have heus := m.injective e
    exact congrArg Prod.fst (Sum.inr.inj (Sum.inr.inj heus))⟩

def support {q b : ℕ} (m : Marked q ↪ CellVertex q b)
    (x y : Ordinary (Fin (Nat.sqrt q)) (Intact m)) : Prop :=
  coordinates m y ∈ gridNeighbors (coordinates m x)

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
