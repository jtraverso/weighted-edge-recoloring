import WeightedPaper.CrossingReserves
import WeightedPaper.CrossingPacking

/-! The dense cut criterion with shared exceptional neighbours and real
row scales. The internal colouring determines the two sets still missing
each colour and the row weight available on those sets. -/
namespace WeightedPaper
open Finset
open scoped Classical

variable {A B I : Type*} [Fintype A] [Fintype B]

/-- Hall's condition stated directly on two finite sets of active vertices. -/
theorem exists_equiv_of_finset_hall (U : Finset A) (W : Finset B) (R : A → B → Prop)
    (heq : U.card = W.card)
    (hall : ∀ S ⊆ U, S.card ≤ (W.filter fun b => ∃ a ∈ S, R a b).card) :
    ∃ f : U ≃ W, ∀ a : U, R a (f a) := by
  classical
  have hall' (S : Finset U) :
      S.card ≤ (univ.filter fun b : W => ∃ a ∈ S, R a b).card := by
    let E := S.image Subtype.val
    have hCard : E.card = S.card := card_image_of_injective S Subtype.val_injective
    have hEU : E ⊆ U := by
      intro a ha
      obtain ⟨b,_,rfl⟩ := mem_image.mp ha
      exact b.2
    have hh := hall E hEU
    rw [hCard] at hh
    have hn : (univ.filter (fun b : W => ∃ a ∈ S, R a b)).card =
        (W.filter (fun b => ∃ a ∈ E, R a b)).card := by
      apply card_bij (fun b _ => b.val)
      · intro b hb
        obtain ⟨a,ha,hab⟩ := (mem_filter.mp hb).2
        exact mem_filter.mpr ⟨b.2,a.val,mem_image_of_mem Subtype.val ha,hab⟩
      · intro b _ c _ hc
        exact Subtype.ext hc
      · intro b hb
        obtain ⟨hbW,a,ha,hab⟩ := mem_filter.mp hb
        obtain ⟨a',ha',rfl⟩ := mem_image.mp ha
        exact ⟨⟨b,hbW⟩,mem_filter.mpr ⟨mem_univ _,a',ha',hab⟩,rfl⟩
    exact hh.trans_eq hn.symm
  obtain ⟨f,hf,hR⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun a : U => fun b : W => R a b)).mp hall'
  have hcard : Fintype.card U = Fintype.card W := by simpa using heq
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),hR⟩

theorem exists_matching_on_finsets_of_exceptional_hall (U : Finset A) (W : Finset B)
    (X : Finset A) (Y : Finset B) (R : A → B → Prop) (dA dB : ℕ)
    (heq : U.card = W.card) (hd : U.card ≤ dA + dB)
    (hA : ∀ a ∈ U, a ∉ X → dA ≤ (W.filter fun b => b ∉ Y ∧ R a b).card)
    (hB : ∀ b ∈ W, b ∉ Y → dB ≤ (U.filter fun a => a ∉ X ∧ R a b).card)
    (hX : ∀ S ⊆ U.filter (· ∈ X),
      S.card ≤ (W.filter fun b => b ∉ Y ∧ ∃ a ∈ S, R a b).card)
    (hY : ∀ T ⊆ W.filter (· ∈ Y),
      T.card ≤ (U.filter fun a => a ∉ X ∧ ∃ b ∈ T, R a b).card) :
    ∃ f : U ≃ W, ∀ a : U, R a (f a) := by
  classical
  apply exists_equiv_of_finset_hall U W R heq
  intro S hS
  let N := W.filter (fun b => ∃ a ∈ S, R a b)
  change S.card ≤ N.card
  have hSU := card_le_card hS
  by_cases hSX : S ⊆ U.filter (· ∈ X)
  · exact (hX S hSX).trans (card_le_card fun b hb =>
      mem_filter.mpr ⟨(mem_filter.mp hb).1,(mem_filter.mp hb).2.2⟩)
  · have hEx : ∃ a ∈ S, a ∉ X := by
      by_contra! hh
      exact hSX (fun a ha => mem_filter.mpr ⟨hS ha,hh a ha⟩)
    obtain ⟨a,ha,hax⟩ := hEx
    by_cases hs : S.card ≤ dA
    · exact hs.trans ((hA a (hS ha) hax).trans (card_le_card fun b hb =>
        mem_filter.mpr ⟨(mem_filter.mp hb).1,a,ha,(mem_filter.mp hb).2.2⟩))
    · have hNY : W \ N ⊆ W.filter (· ∈ Y) := by
        intro b hb
        obtain ⟨hbW,hbN⟩ := mem_sdiff.mp hb
        apply mem_filter.mpr
        refine ⟨hbW,?_⟩
        by_contra hn
        have hsub : (U.filter fun a => a ∉ X ∧ R a b) ⊆ U \ S := by
          intro a ha
          exact mem_sdiff.mpr ⟨(mem_filter.mp ha).1,fun has =>
            hbN (mem_filter.mpr ⟨hbW,a,has,(mem_filter.mp ha).2.2⟩)⟩
        have hh := (hB b hbW hn).trans (card_le_card hsub)
        rw [card_sdiff_of_subset hS] at hh
        omega
      have hsub : (U.filter fun a => a ∉ X ∧ ∃ b ∈ W \ N, R a b) ⊆ U \ S := by
        intro a ha
        obtain ⟨b,hb,hr⟩ := (mem_filter.mp ha).2.2
        exact mem_sdiff.mpr ⟨(mem_filter.mp ha).1,fun has =>
          (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1,a,has,hr⟩)⟩
      have hh := (hY (W \ N) hNY).trans (card_le_card hsub)
      have hN : N ⊆ W := filter_subset _ _
      rw [card_sdiff_of_subset hN,card_sdiff_of_subset hS] at hh
      have hc := card_le_card hN
      omega

/-- Remove at most `q` vertices from the target side and at most `p`
copies incident at the source vertex. Each lost neighbour costs at least one. -/
theorem ordinary_degree_after_spending {V : Type*} [Fintype V] (O W : Finset V)
    (w loss : V → ℕ) (q p d : ℕ)
    (hcover : (O \ W).card ≤ q) (hcost : (∑ v,loss v) ≤ p)
    (hdegree : d ≤ (O.filter fun v => 0 < w v).card) :
    d - q - p ≤ ((O ∩ W).filter fun v => 0 < w v - loss v).card := by
  classical
  let N := O.filter fun v => 0 < w v
  let T := O ∩ W
  have hremove : (N \ W).card ≤ q :=
    (card_le_card (sdiff_subset_sdiff (filter_subset _ _) Subset.rfl)).trans hcover
  have hsplit := card_sdiff_add_card_inter N W
  have hEq : N ∩ W = T.filter (fun v => 0 < w v) := by
    ext v
    simp only [N,T,mem_inter,mem_filter]
    tauto
  rw [hEq] at hsplit
  have hl := MultiCentreHall.support_loss_under_spending T w loss
  have hc : (∑ v ∈ T, loss v) ≤ p := (sum_le_sum_of_subset_of_nonneg
    (subset_univ T) (fun v _ _ => Nat.zero_le (loss v))).trans hcost
  change d ≤ N.card at hdegree
  change _ ≤ (T.filter fun v => 0 < w v - loss v).card
  omega

/-- Dense completion for all colours with their exact covered sizes.
The reserves are measured on the ordinary vertices missing that colour. -/
theorem exists_crossing_packing_of_dense_cut (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B)
    (m a δA δB : ℕ) (ai : I → ℕ)
    (hmA : Fintype.card A = m) (hmB : Fintype.card B = m)
    (hsize : ∀ i ∈ K, (U i).card + 2 * ai i = m ∧ (W i).card + 2 * ai i = m ∧ ai i ≤ a)
    (hdense : m + 2 * a + 2 * (K.card - 1) ≤ δA + δB)
    (hδA : ∀ x ∉ X, δA ≤ (Yᶜ.filter fun y => 0 < cap x y).card)
    (hδB : ∀ y ∉ Y, δB ≤ (Xᶜ.filter fun x => 0 < cap x y).card)
    (rowsA : RowReserves U W cap K X Y)
    (rowsB : RowReserves W U (fun y x => cap x y) K Y X) :
    Nonempty (CrossingPacking U W cap K) := by
  classical
  apply exists_crossing_packing U W cap K
  intro i hi loss hLossA hLossB
  obtain ⟨hU,hW,ha⟩ := hsize i hi
  let p := K.card - 1
  have hcoverA : ((U i)ᶜ).card = 2 * ai i := by rw [card_compl,hmA]; omega
  have hcoverB : ((W i)ᶜ).card = 2 * ai i := by rw [card_compl,hmB]; omega
  let R := fun x y => 0 < cap x y - loss x y
  apply exists_matching_on_finsets_of_exceptional_hall (U i) (W i) X Y R
    (δA - 2 * ai i - p) (δB - 2 * ai i - p)
  · omega
  · dsimp [p]
    omega
  · intro x _ hx
    have hcover : (Yᶜ \ W i).card ≤ 2 * ai i := by
      rw [← hcoverB]
      apply card_le_card
      intro v hv
      exact mem_compl.mpr (mem_sdiff.mp hv).2
    have h := ordinary_degree_after_spending Yᶜ (W i) (cap x) (loss x)
      (2 * ai i) p δA hcover (hLossA x) (hδA x hx)
    convert h using 2
    ext y
    simp [R,and_assoc,and_comm]
  · intro y _ hy
    have hcover : (Xᶜ \ U i).card ≤ 2 * ai i := by
      rw [← hcoverA]
      apply card_le_card
      intro v hv
      exact mem_compl.mpr (mem_sdiff.mp hv).2
    have h := ordinary_degree_after_spending Xᶜ (U i) (fun x => cap x y) (fun x => loss x y)
      (2 * ai i) p δB hcover (hLossB y) (hδB y hy)
    convert h using 2
    ext x
    simp [R,and_assoc,and_comm]
  · intro S hS
    have h := rowsA.hall i hi loss hLossA S hS
    convert h using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [R])
  · intro T hT
    have h := rowsB.hall i hi (fun y x => loss x y) hLossB T hT
    convert h using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [R])

end WeightedPaper
