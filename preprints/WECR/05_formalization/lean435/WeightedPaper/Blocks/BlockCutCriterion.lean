import WeightedPaper.Blocks.BlockFactorization
import WeightedPaper.Blocks.BlockTransport
import WeightedPaper.Cut.PairDegreeCuts

namespace WeightedPaper.Blocks

open Finset SimpleGraph
open scoped Classical

variable {J A B : Type*} [Fintype J] [Fintype A] [Fintype B]

noncomputable def imbalance (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (j : J) : ℤ :=
  ((fiber (U \ X) left j).card : ℤ) - (fiber (W \ Y) right j).card

omit [Fintype A] in
theorem sum_fiber_card (U : Finset A) (f : A → J) :
    (∑ j, (fiber U f j).card) = U.card := by
  classical
  simp only [fiber,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

noncomputable def extendAssignment (U X : Finset A) (left : A → J) (a : ↥(U ∩ X) → J) (x : A) : J :=
  if hx : x ∈ U ∩ X then a ⟨x,hx⟩ else left x

omit [Fintype J] [Fintype A] in
theorem routed_ordinary (U X : Finset A) (left : A → J) (a : ↥(U ∩ X) → J) (j : J) :
    fiber U (extendAssignment U X left a) j \ X = fiber (U \ X) left j := by
  classical
  ext x
  by_cases hx : x ∈ X <;> simp [mem_fiber,extendAssignment,hx]

omit [Fintype J] [Fintype A] in
theorem routed_exceptional (U X : Finset A) (left : A → J)
    (a : ↥(U ∩ X) → J) (j : J) :
    (fiber U (extendAssignment U X left a) j ∩ X).card = (univ.filter fun x => a x = j).card := by
  classical
  symm
  apply card_bij (fun x _ => x.val)
  · intro x hx
    have H := mem_inter.mp x.2
    exact mem_inter.mpr ⟨mem_fiber.mpr ⟨H.1,by simpa [extendAssignment,x.2] using (mem_filter.mp hx).2⟩,H.2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨ht,hxX⟩ := mem_inter.mp hx
    obtain ⟨hxU,he⟩ := mem_fiber.mp ht
    have hx' := mem_inter.mpr ⟨hxU,hxX⟩
    exact ⟨⟨x,hx'⟩,mem_filter.mpr ⟨mem_univ _,by simpa [extendAssignment,hx'] using he⟩,rfl⟩

omit [Fintype A] [Fintype B] in
theorem sum_imbalance (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (hUW : U.card = W.card) :
    (∑ j, imbalance U W X Y left right j) =
      (Fintype.card (↥(W ∩ Y)) : ℤ) - Fintype.card (↥(U ∩ X)) := by
  classical
  simp only [imbalance,sum_sub_distrib,← Nat.cast_sum,sum_fiber_card,Fintype.card_coe]
  have h₁ := card_sdiff_add_card_inter U X
  have h₂ := card_sdiff_add_card_inter W Y
  omega

/-- The free sides must have equal size. Each block has enough width
for its ordinary completion after assigning exceptions, and the
exceptional eligibility relation satisfies the quotient cuts. -/
def BlockCuts (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ) (eA : A → J → Prop) (eB : B → J → Prop) : Prop :=
  U.card = W.card ∧
  (∀ j, threshold j + (W ∩ Y).card ≤ (fiber (U \ X) left j).card) ∧
  TransportCuts (fun (x : ↥(U ∩ X)) j => eA x j) (fun (y : ↥(W ∩ Y)) j => eB y j)
    (imbalance U W X Y left right)

omit [Fintype A] [Fintype B] in
set_option maxHeartbeats 600000 in
/-- A cut certificate routes the exceptional vertices. The width bound
reserves enough space even if every right exceptional vertex uses a single block. -/
theorem route_of_block_cuts (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ)
    (eA : A → J → Prop) (eB : B → J → Prop)
    (cuts : BlockCuts U W X Y left right threshold eA eB) :
    Nonempty (Routing U W X Y left right threshold eA eB) := by
  classical
  obtain ⟨hUW,width,cuts⟩ := cuts
  have hδ := sum_imbalance U W X Y left right hUW
  obtain ⟨a,b,ha,hb,hbal⟩ := assign_of_transport_cuts _ _ _ hδ cuts
  let a' := extendAssignment U X left a
  let b' := extendAssignment W Y right b
  refine ⟨⟨a',b',?_,?_,?_,?_,?_,?_⟩⟩
  · intro x hx
    simp [a',extendAssignment,(mem_sdiff.mp hx).2]
  · intro y hy
    simp [b',extendAssignment,(mem_sdiff.mp hy).2]
  · intro x hx
    simpa [a',extendAssignment,hx] using ha ⟨x,hx⟩
  · intro y hy
    simpa [b',extendAssignment,hy] using hb ⟨y,hy⟩
  · intro j
    have h₁ := card_sdiff_add_card_inter (fiber U a' j) X
    have h₂ := card_sdiff_add_card_inter (fiber W b' j) Y
    rw [routed_ordinary U X left a j, routed_exceptional U X left a j] at h₁
    rw [routed_ordinary W Y right b j, routed_exceptional W Y right b j] at h₂
    have hh := hbal j
    dsimp [imbalance] at hh
    simp only [Finset.univ_eq_attach] at hh h₁ h₂
    omega
  · intro j
    have h₁ := card_sdiff_add_card_inter (fiber U a' j) X
    rw [routed_ordinary U X left a j] at h₁
    have h₂ : (fiber W b' j ∩ Y).card ≤ (W ∩ Y).card :=
      card_le_card (fun y hy => mem_inter.mpr ⟨(mem_fiber.mp (mem_inter.mp hy).1).1,(mem_inter.mp hy).2⟩)
    have := width j
    omega

/-- The transport cuts suffice for factorization with certified row
reserves and locally resilient ordinary blocks. -/
theorem exists_factorization_of_block_cuts {V : Type*} [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k ≤ D) (hreg : M.IsRegularOfDegree D)
    (C : (M.internalPart L).EdgeColoring k) (X : Finset L) (Y : Finset (Lᶜ : Finset V))
    (left : L → J) (right : (Lᶜ : Finset V) → J) (threshold : J → ℕ)
    (eligibleA : Fin k → L → J → Prop) (eligibleB : Fin k → (Lᶜ : Finset V) → J → Prop)
    (hrect : ∀ j, Rectangle (fun x y => M.mult s(x.val,y.val))
      (fiber (ordinary X) left j) (fiber (ordinary Y) right j) (threshold j) k)
    (rowsA : BlockReserves (missingOn C L) (missingOn C Lᶜ) (fun x y => M.mult s(x.val,y.val))
      univ X Y right eligibleA)
    (rowsB : BlockReserves (missingOn C Lᶜ) (missingOn C L) (fun y x => M.mult s(x.val,y.val))
      univ Y X left eligibleB)
    (cuts : ∀ i, BlockCuts (missingOn C L i) (missingOn C Lᶜ i)
      X Y left right threshold (eligibleA i) (eligibleB i)) :
    ∃ F : M.EdgeColoring D, F.IsFactorization :=
  exists_factorization_of_block_routing M L D k hk hreg C X Y left right threshold eligibleA eligibleB
    hrect rowsA rowsB (fun i => route_of_block_cuts _ _ X Y left right threshold _ _ (cuts i))

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.route_of_block_cuts
#print axioms WeightedPaper.Blocks.exists_factorization_of_block_cuts
