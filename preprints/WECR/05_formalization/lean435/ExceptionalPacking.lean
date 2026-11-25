import WeightedPaper.CrossingReserves
import Mathlib.Tactic

namespace WeightedPaper.Repair
open Finset
open scoped Classical
variable {I A B : Type*} [Fintype A] [Fintype B]

/-- Physical pairs used by an injection between two free sets. -/
noncomputable def pairsOf {X : Finset A} {Y : Finset B} (f : X → Y) : Finset (A × B) :=
  univ.image (fun x => (x.val,(f x).val))

theorem mem_pairsOf {X : Finset A} {Y : Finset B} (f : X → Y) (a : A) (b : B) :
    (a,b) ∈ pairsOf f ↔ ∃ x : X, x.val = a ∧ (f x).val = b := by
  simp [pairsOf]

theorem pairsOf_row {X : Finset A} {Y : Finset B} (f : X → Y) (a : A) :
    (univ.filter fun b => (a,b) ∈ pairsOf f).card = if a ∈ X then 1 else 0 := by
  classical
  by_cases h : a ∈ X
  · have e : (univ.filter fun b => (a,b) ∈ pairsOf f) = {(f ⟨a,h⟩).val} := by
      ext b
      simp only [mem_filter,mem_univ,true_and,mem_pairsOf,mem_singleton]
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact congrArg (fun z => (f z).val) (Subtype.ext hx)
      · rintro rfl; exact ⟨_,rfl,rfl⟩
    simp [e,h]
  · have e : (univ.filter fun b => (a,b) ∈ pairsOf f) = ∅ := by
      ext b
      simp only [mem_filter,mem_univ,true_and,mem_pairsOf,notMem_empty,iff_false]
      rintro ⟨x,hx,_⟩
      exact h (hx ▸ x.property)
    simp [e,h]

theorem pairsOf_col_le {X : Finset A} {Y : Finset B} (f : X ↪ Y) (b : B) :
    (univ.filter fun a => (a,b) ∈ pairsOf f).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro a ha a' ha'
  obtain ⟨x,rfl,hx⟩ := (mem_pairsOf f a b).mp (mem_filter.mp ha).2
  obtain ⟨y,rfl,hy⟩ := (mem_pairsOf f a' b).mp (mem_filter.mp ha').2
  exact congrArg Subtype.val (f.injective (Subtype.ext (hx.trans hy.symm)))

noncomputable def spending (K : Finset I) (P : I → Finset (A × B)) (a : A) (b : B) : ℕ :=
  (K.filter fun i => (a,b) ∈ P i).card

private theorem injection_of_reserve {I : Type*} (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B)
    (cert : WeightedPaper.RowReserves U W cap K X Y)
    (i : I) (hi : i ∈ K) (loss : A → B → ℕ) (ok : ∀ a, ∑ b, loss a b ≤ K.card-1) :
    ∃ f : ↥(U i ∩ X) ↪ ↥(W i \ Y), ∀ x : ↥(U i ∩ X), 0 < cap x (f x)-loss x (f x) := by
  classical
  let S := U i ∩ X
  let T := W i \ Y
  let R (a : S) (b : T) := 0 < cap a b - loss a b
  have hall (F : Finset S) : F.card ≤ (univ.filter fun b : T => ∃ a ∈ F, R a b).card := by
    let V := F.image Subtype.val
    have sub : V ⊆ (U i).filter (· ∈ X) := by
      rintro _ h
      obtain ⟨a,_,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr (mem_inter.mp a.property)
    have h := cert.hall i hi loss ok V sub
    rw [show V.card = F.card from card_image_of_injective _ Subtype.val_injective] at h
    refine h.trans_eq ?_
    apply card_bij (fun b hb => (⟨b, mem_sdiff.mpr ⟨(mem_filter.mp hb).1,(mem_filter.mp hb).2.1⟩⟩ : T))
    · intro b hb
      obtain ⟨a,ha,hr⟩ := (mem_filter.mp hb).2.2
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      exact mem_filter.mpr ⟨mem_univ _,x,hx,hr⟩
    · intro b _ b' _ e
      exact congrArg Subtype.val e
    · intro b hb
      obtain ⟨a,ha,hr⟩ := (mem_filter.mp hb).2
      refine ⟨b.val,mem_filter.mpr ⟨(mem_sdiff.mp b.property).1,(mem_sdiff.mp b.property).2,?_⟩,rfl⟩
      exact ⟨a.val,mem_image_of_mem Subtype.val ha,hr⟩
  obtain ⟨f,inj,use⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hall
  exact ⟨⟨f,inj⟩,use⟩

/-- Spend the weighted budget one color at a time. Both applications of
this theorem use exceptional-to-ordinary pairs, in opposite orientations. -/
theorem pack_exceptional_rows (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B)
    (cert : WeightedPaper.RowReserves U W cap K X Y) :
    ∃ (P : I → Finset (A × B)),
      (∀ i ∈ K, ∃ f : ↥(U i ∩ X) ↪ ↥(W i \ Y), P i = pairsOf f) ∧
      ∀ a b, spending K P a b ≤ cap a b := by
  classical
  suffices claim : ∀ J ⊆ K, ∃ (P : I → Finset (A × B)),
      (∀ i ∈ J, ∃ f : ↥(U i ∩ X) ↪ ↥(W i \ Y), P i = pairsOf f) ∧
      ∀ a b, spending J P a b ≤ cap a b from claim K Subset.rfl
  intro J
  induction J using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => ∅,by simp,by simp [spending]⟩
  | insert i J hi ih =>
    intro sub
    obtain ⟨P,matchP,bound⟩ := ih (fun _ hj => sub (mem_insert_of_mem hj))
    have size : J.card ≤ K.card-1 := by
      have h := card_le_card sub
      rw [card_insert_of_notMem hi] at h
      omega
    have loss (a : A) : ∑ b, spending J P a b ≤ K.card-1 := by
      apply le_trans _ size
      simp only [spending,card_eq_sum_ones,sum_filter]
      rw [sum_comm]
      calc
        _ ≤ ∑ j ∈ J, 1 := by
          apply sum_le_sum
          intro j hj
          obtain ⟨f,e⟩ := matchP j hj
          rw [e,← sum_filter]
          simp only [sum_const,nsmul_one,pairsOf_row]
          split <;> omega
        _ = _ := by simp
    obtain ⟨f,hf⟩ := injection_of_reserve U W cap K X Y cert i (sub (mem_insert_self i J)) _ loss
    let Q := Function.update P i (pairsOf f)
    refine ⟨Q,?_,?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl|hj
      · exact ⟨f,by simp [Q]⟩
      · obtain ⟨g,hg⟩ := matchP j hj
        exact ⟨g,by simpa [Q,Function.update_of_ne (show j ≠ i from fun e => hi (e ▸ hj))] using hg⟩
    · intro a b
      have e : J.filter (fun j => (a,b) ∈ Q j) = J.filter (fun j => (a,b) ∈ P j) := by
        apply filter_congr
        intro j hj
        simp [Q, Function.update_of_ne (show j ≠ i from fun e => hi (e ▸ hj))]
      rw [spending, filter_insert, show Q i = pairsOf f by simp [Q],e]
      by_cases h : (a,b) ∈ pairsOf f
      · rw [if_pos h,card_insert_of_notMem (fun q => hi (mem_filter.mp q).1)]
        obtain ⟨x,rfl,rfl⟩ := (mem_pairsOf f a b).mp h
        have j := hf x
        unfold spending at j
        omega
      · rw [if_neg h]
        exact bound a b
end WeightedPaper.Repair
