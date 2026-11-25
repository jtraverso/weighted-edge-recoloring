module

public import PseudorandomLib.Defs

@[expose] public section


namespace WeightedPaper.Repair
open Finset

/-- A left demand, a right demand, or a physical crossing copy. -/
abbrev DemandVertex (I A B E : Type) := (I × A) ⊕ ((I × B) ⊕ E)

variable {I A B E : Type} [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E]

def triple (a : E → A) (b : E → B) (p : I × E) : Finset (DemandVertex I A B E) :=
  {.inl (p.1, a p.2), .inr (.inl (p.1, b p.2)), .inr (.inr p.2)}

theorem triple_card (a : E → A) (b : E → B) (p : I × E) : (triple a b p).card = 3 := by
  simp [triple]

theorem triple_injective (a : E → A) (b : E → B) : Function.Injective (triple a b : I × E → _) := by
  intro p q eq
  have hc : Sum.inr (Sum.inr p.2) ∈ triple a b q := eq ▸ (by simp [triple] : _ ∈ triple a b p)
  have hl : Sum.inl (p.1,a p.2) ∈ triple a b q := eq ▸ (by simp [triple] : _ ∈ triple a b p)
  simp only [triple, mem_insert, mem_singleton, Sum.inr.injEq, Sum.inl.injEq,
    reduceCtorEq, or_false, false_or, Prod.mk.injEq] at hc hl
  exact Prod.ext hl.1 hc

def covered (a : E → A) (b : E → B) (P : Finset (I × E)) : Finset (DemandVertex I A B E) :=
  P.biUnion (triple a b)

def validPacking (a : E → A) (b : E → B) (P : Finset (I × E)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    p.2 ≠ q.2 ∧ (p.1 = q.1 → a p.2 ≠ a q.2 ∧ b p.2 ≠ b q.2)

/-- Read an actual color/copy packing from a matching of incidence triples. -/
theorem packing_from_triples (a : E → A) (b : E → B) (pairs : Finset (I × E))
    (M : Finset (Finset (DemandVertex I A B E))) (sub : M ⊆ pairs.image (triple a b))
    (matching : Pseudorandom.IsMatching M) :
    ∃ P ⊆ pairs, validPacking a b P ∧ covered a b P = M.biUnion id := by
  classical
  let P := pairs.filter fun p => triple a b p ∈ M
  refine ⟨P, filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq neq
    have dis := disjoint_left.mp (matching _ (mem_filter.mp hp).2 _ (mem_filter.mp hq).2
      ((triple_injective a b).ne neq))
    constructor
    · intro h
      exact dis (a := Sum.inr (Sum.inr p.2)) (by simp [triple]) (by simp [triple,h])
    · intro h
      constructor
      · intro ha
        exact dis (a := Sum.inl (p.1, a p.2)) (by simp [triple]) (by simp [triple,h,ha])
      · intro hb
        exact dis (a := Sum.inr (Sum.inl (p.1, b p.2))) (by simp [triple]) (by simp [triple,h,hb])
  · ext v
    simp only [covered, mem_biUnion, id_eq, P, mem_filter]
    constructor
    · rintro ⟨p,⟨_,h⟩,hv⟩
      exact ⟨_,h,hv⟩
    · rintro ⟨t,ht,hv⟩
      obtain ⟨p,hp,rfl⟩ := mem_image.mp (sub ht)
      exact ⟨p,⟨hp,ht⟩,hv⟩

end WeightedPaper.Repair
