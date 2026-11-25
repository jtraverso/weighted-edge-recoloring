import WeightedPaper.Blocks.BlockMatching

namespace WeightedPaper.Blocks

open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
/-- Preserve one Hall witness for all subsets by keeping the image of
a single injection from the exceptional vertices. -/
private theorem hall_image (Q : Finset A) (W : Finset B) (Rel : A → B → Prop)
    (hall : ∀ S ⊆ Q, S.card ≤ (W.filter fun y => ∃ x ∈ S, Rel x y).card) :
    ∃ P ⊆ W, P.card = Q.card ∧
      ∀ S ⊆ Q, S.card ≤ (P.filter fun y => ∃ x ∈ S, Rel x y).card := by
  classical
  let nbr (x : Q) := W.filter (Rel x.val)
  have hall' (S : Finset Q) : S.card ≤ (S.biUnion nbr).card := by
    let T := S.image Subtype.val
    have hsub : T ⊆ Q := by
      intro x hx
      obtain ⟨y,_,rfl⟩ := mem_image.mp hx
      exact y.2
    have hEq : S.biUnion nbr = W.filter (fun y => ∃ x ∈ T, Rel x y) := by
      ext y
      simp only [mem_biUnion, nbr, mem_filter, T, mem_image]
      constructor
      · rintro ⟨x,hx,hy,he⟩
        exact ⟨hy,x,⟨x,hx,rfl⟩,he⟩
      · rintro ⟨hy,x,⟨x',hx',rfl⟩,he⟩
        exact ⟨x',hx',hy,he⟩
    rw [hEq, ← card_image_of_injective S Subtype.val_injective]
    exact hall T hsub
  obtain ⟨f,hf,hrel⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective nbr).mp hall'
  let P := Q.attach.image f
  refine ⟨P,?_,?_,?_⟩
  · intro y hy
    obtain ⟨x,_,rfl⟩ := mem_image.mp hy
    exact (mem_filter.mp (hrel x)).1
  · rw [card_image_of_injective _ hf,card_attach]
  · intro S hS
    let inc : S ↪ Q := ⟨fun x => ⟨x,hS x.2⟩,fun _ _ h => Subtype.ext (congrArg (fun z : Q => z.val) h)⟩
    let g : S → B := f ∘ inc
    have hsub : S.attach.image g ⊆ P.filter (fun y => ∃ x ∈ S, Rel x y) := by
      intro y hy
      obtain ⟨x,_,rfl⟩ := mem_image.mp hy
      exact mem_filter.mpr ⟨mem_image_of_mem f (mem_attach _ (inc x)),x,x.2,(mem_filter.mp (hrel (inc x))).2⟩
    have hh := card_le_card hsub
    rw [card_image_of_injective _ (show Function.Injective g from hf.comp inc.injective),card_attach] at hh
    exact hh

private theorem extend_to_card {V : Type*} (P U : Finset V) (hP : P ⊆ U) (r : ℕ)
    (hr : P.card ≤ r) (hU : r ≤ U.card) :
    ∃ U' ⊆ U, P ⊆ U' ∧ U'.card = r := by
  classical
  obtain ⟨E,hE,hEc⟩ := exists_subset_card_eq (s := U \ P) (n := r-P.card) (by
    rw [card_sdiff_of_subset hP]
    omega)
  refine ⟨E ∪ P,union_subset (hE.trans sdiff_subset) hP,subset_union_right,?_⟩
  have hd : Disjoint E P := by
    rw [disjoint_left]
    exact fun x hx hxp => (mem_sdiff.mp (hE hx)).2 hxp
  rw [card_union_of_disjoint hd,hEc]
  omega

set_option maxHeartbeats 800000 in
/-- Complete an unbalanced block to the size of its smaller side,
covering all exceptions. Both sides must have enough ordinary vertices
to keep the exceptional Hall witnesses through the trimming. -/
theorem trim_and_match_of_rectangle (U : Finset A) (W : Finset B)
    (X L : Finset A) (Y R : Finset B) (cap loss : A → B → ℕ)
    (threshold k : ℕ) (hk : 0 < k)
    (hL : U \ X ⊆ L) (hR : W \ Y ⊆ R)
    (hsize : threshold + (U ∩ X).card + (W ∩ Y).card ≤ min U.card W.card)
    (hrow : ∀ x, (∑ y, loss x y) ≤ k-1)
    (hcol : ∀ y, (∑ x, loss x y) ≤ k-1)
    (hexA : ∀ S ⊆ U ∩ X,
      S.card ≤ ((W \ Y).filter fun y => ∃ x ∈ S, 0 < cap x y-loss x y).card)
    (hexB : ∀ T ⊆ W ∩ Y,
      T.card ≤ ((U \ X).filter fun x => ∃ y ∈ T, 0 < cap x y-loss x y).card)
    (H : Rectangle cap L R threshold k) :
    ∃ U' ⊆ U, ∃ W' ⊆ W, (U ∩ X) ⊆ U' ∧ (W ∩ Y) ⊆ W' ∧
      U'.card = min U.card W.card ∧ (∃ f : U' ≃ W', ∀ x : U', 0 < cap x (f x)-loss x (f x)) := by
  classical
  let size := min U.card W.card
  obtain ⟨P,hP,hPc,hPh⟩ := @hall_image B A (W ∩ Y) (U \ X) (fun y x => 0 < cap x y-loss x y) (by
    intro S hS
    convert hexB S hS using 2
    ext x
    simp)
  obtain ⟨Q,hQ,hQc,hQh⟩ := @hall_image A B (U ∩ X) (W \ Y) (fun x y => 0 < cap x y-loss x y) (by
    intro S hS
    convert hexA S hS using 2
    ext y
    simp)
  obtain ⟨U',hU',hKeepA,hUc⟩ := extend_to_card (P ∪ (U ∩ X)) U
    (union_subset (hP.trans sdiff_subset) inter_subset_left) size (by
      have he := card_union_le P (U ∩ X)
      omega) (min_le_left _ _)
  obtain ⟨W',hW',hKeepB,hWc⟩ := extend_to_card (Q ∪ (W ∩ Y)) W
    (union_subset (hQ.trans sdiff_subset) inter_subset_left) size (by
      have he := card_union_le Q (W ∩ Y)
      omega) (min_le_right _ _)
  refine ⟨U',hU',W',hW',subset_union_right.trans hKeepA,subset_union_right.trans hKeepB,hUc,?_⟩
  apply matching_of_rectangle U' W' X L Y R cap loss threshold k hk (hUc.trans hWc.symm)
    _ _ _ hrow hcol _ _ H
  · exact (sdiff_subset_sdiff hU' (Subset.rfl : X ⊆ X)).trans hL
  · exact (sdiff_subset_sdiff hW' (Subset.rfl : Y ⊆ Y)).trans hR
  · have hA := card_le_card (inter_subset_inter hU' (Subset.rfl : X ⊆ X))
    have hB := card_le_card (inter_subset_inter hW' (Subset.rfl : Y ⊆ Y))
    omega
  · intro S hS
    apply (hQh S (hS.trans (inter_subset_inter hU' (Subset.rfl : X ⊆ X)))).trans
    apply card_le_card
    intro y hy
    simp only [mem_filter] at hy ⊢
    exact ⟨hKeepB (mem_union_left _ hy.1),hy.2⟩
  · intro T hT
    apply (hPh T (hT.trans (inter_subset_inter hW' (Subset.rfl : Y ⊆ Y)))).trans
    apply card_le_card
    intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hKeepA (mem_union_left _ hx.1),hx.2⟩

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.trim_and_match_of_rectangle
