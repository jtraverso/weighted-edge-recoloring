module

public import NibblePacking

@[expose] public section


namespace WeightedPaper.Repair
open Finset Pseudorandom
variable {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E]

/-- The four test families count all colors at one vertex or all free
neighbors of a reserve vertex in one color, on either ordinary side. -/
abbrev TestIndex (I A B : Type) := (A ⊕ B) ⊕ ((I × A) ⊕ (I × B))

def demandTest (freeA : I → Finset A) (freeB : I → Finset B) (nbrA : A → Finset B)
    (nbrB : B → Finset A) : TestIndex I A B → Finset (DemandVertex I A B E)
  | .inl (.inl a) => (univ.filter fun i => a ∈ freeA i).image (fun i => .inl (i,a))
  | .inl (.inr b) => (univ.filter fun i => b ∈ freeB i).image (fun i => .inr (.inl (i,b)))
  | .inr (.inl (i,a)) => (nbrA a ∩ freeB i).image (fun b => .inr (.inl (i,b)))
  | .inr (.inr (i,b)) => (nbrB b ∩ freeA i).image (fun a => .inl (i,a))

theorem demandTest_size (freeA : I → Finset A) (freeB : I → Finset B)
    (nbrA : A → Finset B) (nbrB : B → Finset A) (d : ℕ)
    (ha : ∀ a, (nbrA a).card ≤ d) (hb : ∀ b, (nbrB b).card ≤ d) (j : TestIndex I A B) :
    (demandTest (E := E) freeA freeB nbrA nbrB j).card ≤
      Sum.elim (fun _ => Fintype.card I) (fun _ => d) j := by
  rcases j with (a|b) | (⟨i,a⟩|⟨i,b⟩)
  · exact card_image_le.trans (card_le_univ _)
  · exact card_image_le.trans (card_le_univ _)
  · exact card_image_le.trans ((card_le_card inter_subset_left).trans (ha a))
  · exact card_image_le.trans ((card_le_card inter_subset_left).trans (hb b))

theorem test_vertex_free (freeA : I → Finset A) (freeB : I → Finset B)
    (nbrA : A → Finset B) (nbrB : B → Finset A) (j : TestIndex I A B)
    (v : DemandVertex I A B E) (hv : v ∈ demandTest (E := E) freeA freeB nbrA nbrB j) :
    (∃ i a, a ∈ freeA i ∧ v = .inl (i,a)) ∨
    (∃ i b, b ∈ freeB i ∧ v = .inr (.inl (i,b))) := by
  rcases j with (a|b) | (⟨i,a⟩|⟨i,b⟩)
  · obtain ⟨i,h,rfl⟩ := mem_image.mp hv
    exact Or.inl ⟨_,_,(mem_filter.mp h).2,rfl⟩
  · obtain ⟨i,h,rfl⟩ := mem_image.mp hv
    exact Or.inr ⟨_,_,(mem_filter.mp h).2,rfl⟩
  · obtain ⟨b,h,rfl⟩ := mem_image.mp hv
    exact Or.inr ⟨_,_,(mem_inter.mp h).2,rfl⟩
  · obtain ⟨a,h,rfl⟩ := mem_image.mp hv
    exact Or.inl ⟨_,_,(mem_inter.mp h).2,rfl⟩

/-- Apply the registered nibble to all physical-vertex and reserve-neighborhood
tests simultaneously. Test sizes are bounded by the palette size or by d.
The left/right maps give the endpoints of each physical bulk copy. -/
theorem exists_packing_with_repair_tests (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
      [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E],
    ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ η : ℝ, 0 ≤ η → η < 1 →
    ∀ (a : E → A) (b : E → B) (pairs : Finset (I × E))
      (freeA : I → Finset A) (freeB : I → Finset B) (nbrA : A → Finset B) (nbrB : B → Finset A)
      (d : ℕ), (∀ x, (nbrA x).card ≤ d) → (∀ y, (nbrB y).card ≤ d) →
      (∀ p ∈ pairs, a p.2 ∈ freeA p.1 ∧ b p.2 ∈ freeB p.1) →
      let H := pairs.image (triple a b)
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ^(1-δ)) →
      (H.card : ℝ) ≤ Real.exp (Δ^((δ/450)^2)) →
      (Fintype.card (TestIndex I A B) : ℝ) ≤ Real.exp (Δ^((δ/450)^2)) →
      (∀ i x, x ∈ freeA i → (1-η)*Δ ≤ (degree H (.inl (i,x)) : ℝ)) →
      (∀ i y, y ∈ freeB i → (1-η)*Δ ≤ (degree H (.inr (.inl (i,y))) : ℝ)) →
      ∃ P ⊆ pairs, validPacking a b P ∧ (∀ p ∈ P, a p.2 ∈ freeA p.1 ∧ b p.2 ∈ freeB p.1) ∧ ∀ j : TestIndex I A B,
        let T := demandTest (E := E) freeA freeB nbrA nbrB j
        let z : ℕ := Sum.elim (fun _ => Fintype.card I) (fun _ => d) j
        ((T \ covered a b P).card : ℝ) ≤ max ((η+Δ^(-(δ/450)))*z) (3*Δ^δ/(1-η)) := by
  obtain ⟨Δ₀,th⟩ := exists_nibble_packing δ hδ hδ'
  refine ⟨max Δ₀ 1, ?_⟩
  intro I A B E _ _ _ _ _ _ _ _ Δ hΔ η hη he a b pairs freeA freeB nbrA nbrB d hA hB eligible H deg cod size count lowA lowB
  have hpos : 0 ≤ Δ := (zero_le_one.trans (le_max_right _ _)).trans hΔ
  let T := demandTest (E := E) freeA freeB nbrA nbrB
  have low j v (hv : v ∈ T j) : (1-η)*Δ ≤ (degree H v : ℝ) := by
    rcases test_vertex_free freeA freeB nbrA nbrB j v hv with ⟨i,x,h,rfl⟩ | ⟨i,y,h,rfl⟩
    · exact lowA _ _ h
    · exact lowB _ _ h
  obtain ⟨P,sub,pack,test⟩ := th Δ ((le_max_left _ _).trans hΔ) η hη he I A B E _ a b pairs T
    deg cod size count low
  refine ⟨P,sub,pack,fun p hp => eligible p (sub hp),fun j => (test j).trans (max_le_max ?_ le_rfl)⟩
  apply mul_le_mul_of_nonneg_left _ (add_nonneg hη (Real.rpow_nonneg hpos _))
  exact_mod_cast demandTest_size (E := E) freeA freeB nbrA nbrB d hA hB j
end WeightedPaper.Repair
