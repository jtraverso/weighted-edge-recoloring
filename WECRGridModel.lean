module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Vertex coordinates and crossing capacity for the sparse grid. -/

open Finset
open scoped Classical

namespace WeightedPaper.Repair

abbrev CellVertex (q b : ℕ) := Fin q × Fin q × Fin b

def gridNeighbors {q b : ℕ} (x : CellVertex q b) : Finset (CellVertex q b) :=
  ({x.1} ×ˢ (univ ×ˢ univ)) ∪ (univ ×ˢ ({x.2.1} ×ˢ univ))

namespace Grid

open Filter Asymptotics
open scoped Topology

abbrev Ordinary (H W : Type) := Fin 2 ⊕ (Fin 2 ⊕ ((H × Bool) ⊕ W))
abbrev Side (H W : Type) := Ordinary H W ⊕ H

section
variable {H W : Type} [Fintype H] [Fintype W]

def leftInternal (i : Fin 2) : Side H W := .inl (.inl i)
def rightInternal (i : Fin 2) : Side H W := .inl (.inr (.inl i))

@[reducible] def static : Side H W → Side H W → Prop
  | .inl (.inr (.inl i)), .inl (.inl j) => i = j
  | .inl (.inr (.inr (.inr w))), .inl (.inr (.inr (.inr v))) => w = v
  | .inl (.inr (.inr (.inl (h,_)))), .inr j => h = j
  | .inr h, .inl (.inr (.inr (.inl (j,_)))) => h = j
  | .inr h, .inr j => h = j
  | _, _ => False

@[reducible] def ordinary (R : Ordinary H W → Ordinary H W → Prop) : Side H W → Side H W → Prop
  | .inl x, .inl y => R x y
  | _, _ => False

noncomputable def capacity (R : Ordinary H W → Ordinary H W → Prop) (d : ℕ) (x y : Side H W) :=
  (if static x y then d else 0) + (if ordinary R x y then 2 else 0)

def endpoint (k : Fin 2) (e : Fin d × Bool) : Side H W ⊕ Side H W :=
  if e.2 then .inl (leftInternal k) else .inr (rightInternal k)
end

abbrev Marked (q : ℕ) := Fin 2 ⊕ (Fin 2 ⊕ (Fin (Nat.sqrt q) × Bool))

theorem two_root_le (q : ℕ) (hq : 12 ≤ q) : 2*Nat.sqrt q ≤ q := by
  have h := Nat.sqrt_le q
  by_cases small : Nat.sqrt q ≤ 1
  · omega
  · nlinarith

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

def support {q b : ℕ} (m : Marked q ↪ CellVertex q b)
    (x y : Ordinary (Fin (Nat.sqrt q)) (Intact m)) : Prop :=
  coordinates m y ∈ gridNeighbors (coordinates m x)

end Grid

end WeightedPaper.Repair
