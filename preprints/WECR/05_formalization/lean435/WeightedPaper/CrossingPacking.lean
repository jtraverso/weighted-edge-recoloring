import WeightedPaper.ScaledHall

/-! Crossing matchings are packed against the actual multiplicities of a
cut. The spending bound grows by at most one per vertex at each step. -/
namespace WeightedPaper
open Finset
open scoped Classical

variable {I A B : Type*} [Fintype A] [Fintype B]

noncomputable def spent (F : I → Finset (A × B)) (J : Finset I) (a : A) (b : B) : ℕ :=
  (J.filter fun i => (a,b) ∈ F i).card

structure CrossingPacking (U : I → Finset A) (W : I → Finset B) (cap : A → B → ℕ)
    (J : Finset I) where
  pairs : I → Finset (A × B)
  row : ∀ i ∈ J, ∀ a, (univ.filter fun b => (a,b) ∈ pairs i).card = if a ∈ U i then 1 else 0
  col : ∀ i ∈ J, ∀ b, (univ.filter fun a => (a,b) ∈ pairs i).card = if b ∈ W i then 1 else 0
  bounded : ∀ a b, spent pairs J a b ≤ cap a b

theorem CrossingPacking.row_spending {U : I → Finset A} {W : I → Finset B}
    {cap : A → B → ℕ} {J : Finset I} (P : CrossingPacking U W cap J) (a : A) :
    (∑ b, spent P.pairs J a b) ≤ J.card := by
  simp only [spent, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  have h := P.row i hi a
  simp only [card_eq_sum_ones, sum_filter] at h
  rw [h]
  split <;> omega

theorem CrossingPacking.col_spending {U : I → Finset A} {W : I → Finset B}
    {cap : A → B → ℕ} {J : Finset I} (P : CrossingPacking U W cap J) (b : B) :
    (∑ a, spent P.pairs J a b) ≤ J.card := by
  simp only [spent, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  have h := P.col i hi b
  simp only [card_eq_sum_ones, sum_filter] at h
  rw [h]
  split <;> omega

private noncomputable def matchPairs {U : Finset A} {W : Finset B} (f : U ≃ W) :
    Finset (A × B) :=
  univ.image (fun a : U => (a.val,(f a).val))

private theorem mem_matchPairs {U : Finset A} {W : Finset B} (f : U ≃ W) (a : A) (b : B) :
    (a,b) ∈ matchPairs f ↔ ∃ x : U, x.val = a ∧ (f x).val = b := by
  simp [matchPairs]

private theorem matchPairs_row {U : Finset A} {W : Finset B} (f : U ≃ W) (a : A) :
    (univ.filter fun b => (a,b) ∈ matchPairs f).card = if a ∈ U then 1 else 0 := by
  have hk (b : B) := mem_matchPairs f a b
  by_cases ha : a ∈ U
  · have h : (univ.filter fun b => (a,b) ∈ matchPairs f) = {↑(f ⟨a,ha⟩)} := by
      ext b
      simp only [mem_filter,mem_univ,true_and,mem_singleton,hk]
      constructor
      · rintro ⟨x,hx,rfl⟩
        congr
        exact Subtype.ext hx
      · rintro rfl
        exact ⟨⟨a,ha⟩,rfl,rfl⟩
    simp [ha,h]
  · have h : (univ.filter fun b => (a,b) ∈ matchPairs f) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨x,hx,_⟩ := (hk b).mp (mem_filter.mp hb).2
      exact ha (hx ▸ x.2)
    simp [ha,h]

private theorem matchPairs_col {U : Finset A} {W : Finset B} (f : U ≃ W) (b : B) :
    (univ.filter fun a => (a,b) ∈ matchPairs f).card = if b ∈ W then 1 else 0 := by
  have h : (univ.filter fun a => (a,b) ∈ matchPairs f) =
      univ.filter (fun a => (b,a) ∈ matchPairs f.symm) := by
    ext a
    simp only [mem_filter,mem_univ,true_and,mem_matchPairs]
    constructor
    · rintro ⟨x,hx,h⟩
      exact ⟨f x,h,by simpa using hx⟩
    · rintro ⟨y,hy,h⟩
      exact ⟨f.symm y,h,by simpa using hy⟩
  rw [h,matchPairs_row]

/-- Complete the crossing matchings in succession. It suffices to solve
one matching problem for any feasible spending whose row and column sums
are at most the number of earlier colours. -/
theorem exists_crossing_packing (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I)
    (hstep : ∀ i ∈ K, ∀ loss : A → B → ℕ,
      (∀ a, (∑ b, loss a b) ≤ K.card - 1) →
      (∀ b, (∑ a, loss a b) ≤ K.card - 1) →
      ∃ f : U i ≃ W i, ∀ a : U i, 0 < cap a (f a) - loss a (f a)) :
    Nonempty (CrossingPacking U W cap K) := by
  suffices h : ∀ J ⊆ K, Nonempty (CrossingPacking U W cap J) from h K Subset.rfl
  intro J
  induction J using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨⟨fun _ => ∅,by simp,by simp,by simp [spent]⟩⟩
  | insert i J hi ih =>
      intro hK
      obtain ⟨P⟩ := ih (fun _ hj => hK (mem_insert_of_mem hj))
      have hsize : J.card ≤ K.card - 1 := by
        have h := card_le_card hK
        rw [card_insert_of_notMem hi] at h
        omega
      obtain ⟨f,hf⟩ := hstep i (hK (mem_insert_self i J)) (spent P.pairs J)
        (fun a => (P.row_spending a).trans hsize) (fun b => (P.col_spending b).trans hsize)
      let F : I → Finset (A × B) := Function.update P.pairs i (matchPairs f)
      refine ⟨⟨F,?_,?_,?_⟩⟩
      · intro j hj a
        rcases mem_insert.mp hj with rfl|hj
        · simpa [F] using matchPairs_row f a
        · have hn : j ≠ i := fun h => hi (h ▸ hj)
          simpa [F,Function.update_of_ne hn] using P.row j hj a
      · intro j hj b
        rcases mem_insert.mp hj with rfl|hj
        · simpa [F] using matchPairs_col f b
        · have hn : j ≠ i := fun h => hi (h ▸ hj)
          simpa [F,Function.update_of_ne hn] using P.col j hj b
      · intro a b
        have heq : (J.filter fun j => (a,b) ∈ F j) =
            J.filter (fun j => (a,b) ∈ P.pairs j) := by
          apply filter_congr
          intro j hj
          simp [F, Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))]
        have hc := P.bounded a b
        by_cases h : (a,b) ∈ matchPairs f
        · obtain ⟨x,rfl,rfl⟩ := (mem_matchPairs f a b).mp h
          rw [spent, filter_insert, show F i = matchPairs f by simp [F], if_pos h,
            card_insert_of_notMem (fun hh => hi (mem_filter.mp hh).1), heq]
          exact Nat.succ_le_of_lt (by have hh := hf x; unfold spent at hh; omega)
        · rw [spent, filter_insert, show F i = matchPairs f by simp [F], if_neg h, heq]
          exact hc

end WeightedPaper
