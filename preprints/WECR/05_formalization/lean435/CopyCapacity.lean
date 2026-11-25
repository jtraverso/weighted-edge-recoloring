import HybridRepair

namespace WeightedPaper.Repair
open Finset
variable {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E]

/-- The two physical pools give exactly the capacity needed to pass from a
color-by-color matching to a multiplicity bound. This also permits parallel
bulk copies with the same two endpoints. -/
theorem hybrid_spending_le (a : E → A) (b : E → B) (R : A → B → Prop) [DecidableRel R]
    (P : Finset (I × E)) (pack : validPacking a b P)
    (alloc : I → Finset (A × B)) (disj : ∀ i j, i ≠ j → Disjoint (alloc i) (alloc j))
    (X : I → Finset A) (Y : I → Finset B) (F : ∀ i, ↥(X i) ≃ ↥(Y i))
    (uses : ∀ i (u : ↥(X i)), (∃ e, (i,e) ∈ P ∧ a e = u.val ∧ b e = (F i u).val) ∨
       (R u (F i u) ∧ (u.val,(F i u).val) ∈ alloc i)) (x : A) (y : B) :
    let colors := univ.filter fun i => ∃ u : ↥(X i), u.val = x ∧ (F i u).val = y
    colors.card ≤ (univ.filter (fun e => a e = x ∧ b e = y)).card + (if R x y then 1 else 0) := by
  classical
  intro colors
  let bulk := colors.filter fun i => ∃ e, (i,e) ∈ P ∧ a e = x ∧ b e = y
  let other := colors \ bulk
  have bulk_card : bulk.card ≤ (univ.filter fun e => a e = x ∧ b e = y).card := by
    choose f h using fun i : ↥bulk => (mem_filter.mp i.property).2
    let target := univ.filter fun e => a e = x ∧ b e = y
    let g (i : ↥bulk) : ↥target := ⟨f i,mem_filter.mpr ⟨mem_univ _,(h i).2⟩⟩
    have inj : Function.Injective g := by
      intro i j eq
      apply Subtype.ext
      by_contra ne
      exact (pack _ (h i).1 _ (h j).1 (fun e => ne (congrArg Prod.fst e))).1 (congrArg Subtype.val eq)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g inj
  have atReserve i (hi : i ∈ other) : R x y ∧ (x,y) ∈ alloc i := by
    obtain ⟨hc,hb⟩ := mem_sdiff.mp hi
    obtain ⟨u,hx,hy⟩ := (mem_filter.mp hc).2
    rcases uses i u with ⟨e,he,ha,hb'⟩ | ⟨hr,al⟩
    · exact False.elim (hb (mem_filter.mpr ⟨hc,e,he,ha.trans hx,hb'.trans hy⟩))
    · simpa [hx,hy] using And.intro hr al
  have other_card : other.card ≤ if R x y then 1 else 0 := by
    by_cases hr : R x y
    · simp only [hr,ite_true]
      apply card_le_one.mpr
      intro i hi j hj
      by_contra ne
      exact disjoint_left.mp (disj i j ne) (atReserve i hi).2 (atReserve j hj).2
    · have empty : other = ∅ := eq_empty_iff_forall_notMem.mpr (fun i hi => hr (atReserve i hi).1)
      simp [hr,empty]
  have sub : bulk ⊆ colors := filter_subset _ _
  have size : other.card = colors.card-bulk.card := card_sdiff_of_subset sub
  have bound := card_le_card sub
  omega
end WeightedPaper.Repair
