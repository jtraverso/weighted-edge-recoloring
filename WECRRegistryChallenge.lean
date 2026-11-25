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

/-! Theorem 9 and Corollary 10 of WECR Preprint 1.0. -/

open Finset
open scoped Classical

namespace Pseudorandom

variable {V : Type*} [DecidableEq V]

/-- Degree and codegree definitions from PseudorandomLib.Defs (EGJ formalization). -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

end Pseudorandom


namespace WeightedPaper

structure RowReserves {I A B : Type*} (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B) where
  weight : A → B → ℝ
  charge : A → ℝ
  bound : ℝ
  bound_pos : 0 < bound
  charge_nonneg : ∀ x ∈ X, 0 ≤ charge x
  capacity : ∀ x ∈ X, ∀ y ∉ Y, 0 ≤ weight x y ∧ weight x y ≤ charge x * cap x y
  column : ∀ y ∉ Y, (∑ x ∈ X, weight x y) ≤ bound
  reserve : ∀ i ∈ K, ∀ x ∈ (U i).filter (· ∈ X),
    bound + (K.card - 1 : ℕ) * charge x ≤ ∑ y ∈ (W i).filter (· ∉ Y), weight x y

end WeightedPaper


namespace WeightedPaper.Repair

abbrev CrossingCopy {A B : Type*} (cap : A → B → ℕ) :=
  Σ p : A × B, Fin (cap p.1 p.2)

abbrev CellVertex (q b : ℕ) := Fin q × Fin q × Fin b

def gridNeighbors {q b : ℕ} (x : CellVertex q b) : Finset (CellVertex q b) :=
  ({x.1} ×ˢ (univ ×ˢ univ)) ∪ (univ ×ˢ ({x.2.1} ×ˢ univ))

abbrev DemandVertex (I A B E : Type) := (I × A) ⊕ ((I × B) ⊕ E)

section
variable {I A B E : Type} [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E]

def triple (a : E → A) (b : E → B) (p : I × E) : Finset (DemandVertex I A B E) :=
  {.inl (p.1, a p.2), .inr (.inl (p.1, b p.2)), .inr (.inr p.2)}
end

abbrev TestIndex (I A B : Type) := (A ⊕ B) ⊕ ((I × A) ⊕ (I × B))

section
variable {I A B E C : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype E] [Fintype C]

def HasSeededFactorization (l r : E → A ⊕ B) (a : C → A) (b : C → B)
    (seed : E → I) (D : ℕ) : Prop :=
  ∃ (rename : I ↪ Fin D) (color : E ⊕ C → Fin D),
    (∀ e, color (.inl e) = rename (seed e)) ∧
    ∀ (v : A ⊕ B) i,
      (univ.filter (fun e => color (.inl e) = i ∧ (l e = v ∨ r e = v))).card +
      (univ.filter (fun e => color (.inr e) = i ∧
        (Sum.inl (a e) = v ∨ Sum.inr (b e) = v))).card = 1
end

section
variable {I A B : Type*} [Fintype A] [Fintype B]

noncomputable def pairsOf {X : Finset A} {Y : Finset B} (f : X → Y) : Finset (A × B) :=
  univ.image (fun x => (x.val,(f x).val))

noncomputable def spending (K : Finset I) (P : I → Finset (A × B)) (a : A) (b : B) : ℕ :=
  (K.filter fun i => (a,b) ∈ P i).card
end

section
variable {I A B E : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype E]

noncomputable def transposePairs (P : Finset (B × A)) : Finset (A × B) :=
  P.map (Equiv.prodComm B A).toEmbedding

noncomputable def remaining (U : Finset A) (P : Finset (A × B)) :=
  U \ P.image Prod.fst
end

section
open Pseudorandom
variable {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E] [Nonempty A]

noncomputable def demandError (δ Δ η : ℝ) (z : ℕ) :=
  max ((η+Δ^(-(δ/450)))*z) (3*Δ^δ/(1-η))

structure HybridCertificate (δ Δ₀ : ℝ)
    (a : E → A) (b : E → B) (R : A → B → Prop) [DecidableRel R]
    (X : I → Finset A) (Y : I → Finset B) where
  pairs : Finset (I × E)
  Δ : ℝ
  η : ℝ
  d : ℕ
  σ : ℝ
  β : ℝ
  h : ℕ
  large : Δ₀ ≤ Δ
  eta0 : 0 ≤ η
  eta1 : η < 1
  positive : 0 < d
  regA : ∀ x, (univ.filter (R x)).card = d
  regB : ∀ y, (univ.filter (fun x => R x y)).card = d
  sideCard : Fintype.card A = Fintype.card B
  freeCard : ∀ i, (X i).card = (Y i).card
  eligible : ∀ p ∈ pairs, a p.2 ∈ X p.1 ∧ b p.2 ∈ Y p.1
  degree_le : ∀ v, (degree (pairs.image (triple a b)) v : ℝ) ≤ Δ
  codegree_le : ∀ u v, u ≠ v → (codegree (pairs.image (triple a b)) u v : ℝ) ≤ Δ^(1-δ)
  size_le : ((pairs.image (triple a b)).card : ℝ) ≤ Real.exp (Δ^((δ/450)^2))
  test_le : (Fintype.card (TestIndex I A B) : ℝ) ≤ Real.exp (Δ^((δ/450)^2))
  demandA : ∀ i x, x ∈ X i → (1-η)*Δ ≤ (degree (pairs.image (triple a b)) (.inl (i,x)) : ℝ)
  demandB : ∀ i y, y ∈ Y i → (1-η)*Δ ≤ (degree (pairs.image (triple a b)) (.inr (.inl (i,y))) : ℝ)
  sigma0 : 0 ≤ σ
  sigma1 : σ ≤ 1
  beta0 : 0 ≤ β
  spectrum : ∀ f : A → ℝ, ∑ x, f x = 0 →
    (∑ y, (∑ x, f x * (if R x y then 1/(d:ℝ) else 0))^2) ≤ σ^2 * ∑ x, (f x)^2
  missedA : ∀ i x, (((Y i)ᶜ.filter (R x)).card : ℝ) ≤ β*d
  missedB : ∀ i y, (((X i)ᶜ.filter (fun x => R x y)).card : ℝ) ≤ β*d
  length : 0 < h
  mixing : σ^h ≤ 1/(2*(Fintype.card A : ℝ))
  budget1 : 3*(2*h : ℕ)*(β+demandError δ Δ η d/d) ≤ 1/2
  budget2 :
    let t := demandError δ Δ η (Fintype.card I)
    let ρ := β+demandError δ Δ η d/d
    (2*(h:ℝ)+1)*(6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d) +
      (2*(h:ℝ))*(6*(2*h : ℕ)*ρ) ≤ 4/27

noncomputable def ordinaryCapacity (a : E → A) (b : E → B)
    (R : A → B → Prop) [DecidableRel R] (x : A) (y : B) :=
  (univ.filter (fun e => a e = x ∧ b e = y)).card + if R x y then 1 else 0
end

noncomputable def pullback {V W : Type*} [Fintype V] (j : V ↪ W) (S : Finset W) :=
  univ.filter fun x => j x ∈ S

def WeightedNibbleAt (δ Δ₀ : ℝ) : Prop :=
  ∀ {I A B A₀ B₀ E T : Type}
      [Fintype I] [Fintype A] [Fintype B] [Fintype A₀] [Fintype B₀] [Fintype E] [Fintype T]
      [DecidableEq I] [DecidableEq A₀] [DecidableEq B₀] [DecidableEq E] [Nonempty A₀],
    ∀ (cap leftCap rightCap ordinaryCap : A → B → ℕ)
    (l r : T → A ⊕ B) (loopless : ∀ e, l e ≠ r e) (seed : T → I) (D : ℕ),
    Fintype.card I ≤ D →
    (∀ a b, leftCap a b + rightCap a b + ordinaryCap a b ≤ cap a b) →
    ∀ (U : I → Finset A) (W : I → Finset B) (X : Finset A) (Y : Finset B)
      (jA : A₀ ↪ A) (jB : B₀ ↪ B) (a : E → A₀) (b : E → B₀)
      (R : A₀ → B₀ → Prop) [decR : DecidableRel R],
    (∀ x ∉ X, x ∈ Set.range jA) → (∀ y ∉ Y, y ∈ Set.range jB) →
    (∀ x y, ordinaryCapacity a b R x y ≤ ordinaryCap (jA x) (jB y)) →
    (∀ x, (univ.filter (fun e => l e = .inl x ∨ r e = .inl x)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.1 = x)).card = D) →
    (∀ y, (univ.filter (fun e => l e = .inr y ∨ r e = .inr y)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.2 = y)).card = D) →
    (∀ i x, (univ.filter (fun e => seed e = i ∧ (l e = .inl x ∨ r e = .inl x))).card =
      if x ∈ U i then 0 else 1) →
    (∀ i y, (univ.filter (fun e => seed e = i ∧ (l e = .inr y ∨ r e = .inr y))).card =
      if y ∈ W i then 0 else 1) →
    WeightedPaper.RowReserves U W leftCap univ X Y →
    WeightedPaper.RowReserves W U (fun y x => rightCap x y) univ Y X →
    (∀ (P : I → Finset (A × B)),
      (∀ x y, spending univ P x y ≤ leftCap x y + rightCap x y) →
      (∀ i, ∃ (f : ↥(U i ∩ X) ↪ ↥(W i \ Y)) (g : ↥(W i ∩ Y) ↪ ↥(U i \ X)),
        P i = pairsOf f ∪ transposePairs (pairsOf g)) →
      Nonempty (HybridCertificate δ Δ₀ a b R
        (fun i => pullback jA (remaining (U i) (P i)))
        (fun i => pullback jB (remaining (W i) (transposePairs (P i)))))) →
    HasSeededFactorization l r
      (fun e : CrossingCopy cap => e.1.1) (fun e : CrossingCopy cap => e.1.2) seed D

theorem factorization_from_weighted_nibble (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ Δ₀ : ℝ, WeightedNibbleAt δ Δ₀ := by
  sorry


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

theorem sparse_grid_growth (b : ℕ) (hb : 0 < b) :
    ((fun q : ℕ => (b*(2*(q:ℝ)-1) : ℝ)) =Θ[atTop]
      (fun q : ℕ => √((b:ℝ)*q^2))) ∧
    ((fun q : ℕ => (Nat.sqrt q : ℝ)) =Θ[atTop]
      (fun q : ℕ => ((b:ℝ)*q^2) ^ (1/4:ℝ))) := by
  sorry

end Grid


end WeightedPaper.Repair
