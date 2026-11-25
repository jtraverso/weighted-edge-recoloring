import WeightedPaper.DenseCut

/-! The ordinary robust neighbourhood has enough slack for the
covered vertices and the exceptional vertices. Hall can be checked
directly on the whole uncovered cut. -/
namespace WeightedPaper
open Finset
open scoped Classical

variable {I A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
private theorem count_ordinary (S X : Finset A) :
    S.card ≤ (S \ X).card + X.card := by
  have hsplit := card_sdiff_add_card_inter S X
  have hc : (S ∩ X).card ≤ X.card := card_le_card inter_subset_right
  omega

theorem exists_matching_of_robust_exceptional_hall (U : Finset A) (W : Finset B)
    (X : Finset A) (Y : Finset B) (R Q : A → B → Prop) (r t : ℕ)
    (heq : U.card = W.card) (hLost : (Yᶜ \ W).card + X.card ≤ r)
    (hA : ∀ a ∈ U, a ∉ X → t + X.card ≤ (W.filter fun b => b ∉ Y ∧ Q a b).card)
    (hB : ∀ b ∈ W, b ∉ Y → t ≤ (U.filter fun a => a ∉ X ∧ Q a b).card)
    (hEdge : ∀ b ∈ W, b ∉ Y → (U.filter (fun a => R a b ∧ ¬Q a b)).card < r)
    (hExpand : ∀ S ⊆ Xᶜ, t ≤ S.card → S.card + t ≤ (Xᶜ : Finset A).card →
      S.card + r ≤ (Yᶜ.filter (fun b => r ≤ (S.filter (fun a => R a b)).card)).card)
    (hX : ∀ S ⊆ U.filter (· ∈ X),
      S.card ≤ (W.filter fun b => b ∉ Y ∧ ∃ a ∈ S, Q a b).card)
    (hY : ∀ T ⊆ W.filter (· ∈ Y),
      T.card ≤ (U.filter fun a => a ∉ X ∧ ∃ b ∈ T, Q a b).card) :
    ∃ f : U ≃ W, ∀ a : U, Q a (f a) := by
  classical
  apply exists_equiv_of_finset_hall U W Q heq
  intro S hS
  let N := W.filter (fun b => ∃ a ∈ S, Q a b)
  let S₀ := S \ X
  change S.card ≤ N.card
  have hSN := count_ordinary S X
  have hSub₀ : S₀ ⊆ (Xᶜ : Finset A) := fun _ hv => mem_compl.mpr (mem_sdiff.mp hv).2
  rcases S₀.eq_empty_or_nonempty with hz|⟨a,ha⟩
  · have hSX : S ⊆ U.filter (· ∈ X) := by
      intro a ha
      refine mem_filter.mpr ⟨hS ha,?_⟩
      by_contra hn
      have hh : a ∈ S₀ := mem_sdiff.mpr ⟨ha,hn⟩
      simp [hz] at hh
    exact (hX S hSX).trans (card_le_card fun b hb =>
      mem_filter.mpr ⟨(mem_filter.mp hb).1,(mem_filter.mp hb).2.2⟩)
  have hAOrd := mem_sdiff.mp ha
  by_cases hSmall : S₀.card ≤ t
  · have hsmall' : S.card ≤ t + X.card := by change S.card ≤ S₀.card + X.card at hSN; omega
    exact hsmall'.trans ((hA a (hS hAOrd.1) hAOrd.2).trans (card_le_card fun b hb =>
      mem_filter.mpr ⟨(mem_filter.mp hb).1,a,hAOrd.1,(mem_filter.mp hb).2.2⟩))
  by_cases hLarge : (Xᶜ : Finset A).card < S₀.card + t
  · have hNY : W \ N ⊆ W.filter (· ∈ Y) := by
      intro b hb
      obtain ⟨hbW,hbN⟩ := mem_sdiff.mp hb
      apply mem_filter.mpr
      refine ⟨hbW,?_⟩
      by_contra hn
      have hsub : (U.filter fun a => a ∉ X ∧ Q a b) ⊆ Xᶜ \ S₀ := by
        intro a ha
        obtain ⟨hu,hx,hq⟩ := mem_filter.mp ha
        exact mem_sdiff.mpr ⟨mem_compl.mpr hx,fun hs =>
          hbN (mem_filter.mpr ⟨hbW,a,(mem_sdiff.mp hs).1,hq⟩)⟩
      have hh := (hB b hbW hn).trans (card_le_card hsub)
      rw [card_sdiff_of_subset hSub₀] at hh
      have hc := card_le_card hSub₀
      omega
    have hsub : (U.filter fun a => a ∉ X ∧ ∃ b ∈ W \ N, Q a b) ⊆ U \ S := by
      intro a ha
      obtain ⟨b,hb,hr⟩ := (mem_filter.mp ha).2.2
      exact mem_sdiff.mpr ⟨(mem_filter.mp ha).1,fun has =>
        (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1,a,has,hr⟩)⟩
    have hh := (hY (W \ N) hNY).trans (card_le_card hsub)
    have hN : N ⊆ W := filter_subset _ _
    rw [card_sdiff_of_subset hN,card_sdiff_of_subset hS] at hh
    have hc := card_le_card hN
    have hc' := card_le_card hS
    omega
  · let N₀ := Yᶜ.filter (fun b => r ≤ (S₀.filter (fun a => R a b)).card)
    have hex : S₀.card + r ≤ N₀.card := hExpand S₀ hSub₀ (by omega) (by omega)
    have hKeep : N₀ ∩ W ⊆ N := by
      intro b hb
      obtain ⟨hb₀,hbW⟩ := mem_inter.mp hb
      obtain ⟨hbO,hrob⟩ := mem_filter.mp hb₀
      by_contra hn
      have hSub : (S₀.filter (fun a => R a b)) ⊆ U.filter (fun a => R a b ∧ ¬Q a b) := by
        intro a ha
        obtain ⟨haS,haR⟩ := mem_filter.mp ha
        have hs := (mem_sdiff.mp haS).1
        exact mem_filter.mpr ⟨hS hs,haR,fun hq => hn (mem_filter.mpr ⟨hbW,a,hs,hq⟩)⟩
      exact (not_lt_of_ge (hrob.trans (card_le_card hSub))) (hEdge b hbW (mem_compl.mp hbO))
    have hCount := card_sdiff_add_card_inter N₀ W
    have hLost' : (N₀ \ W).card ≤ (Yᶜ \ W).card :=
      card_le_card (sdiff_subset_sdiff (filter_subset _ _) Subset.rfl)
    have hh := card_le_card hKeep
    change S.card ≤ S₀.card + X.card at hSN
    omega

private theorem lost_neighbors_le_spent {V : Type*} [Fintype V] (S : Finset V)
    (w loss : V → ℕ) (p : ℕ) (hcost : (∑ v, loss v) ≤ p) :
    (S.filter fun v => 0 < w v ∧ ¬ 0 < w v - loss v).card ≤ p := by
  classical
  rw [card_eq_sum_ones]
  refine (sum_le_sum (fun v hv => ?_)).trans
    ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ => Nat.zero_le (loss v))).trans hcost)
  have hv' := (mem_filter.mp hv).2
  omega

/-- Complete all colour classes under the robust ordinary cut margins. -/
theorem exists_crossing_packing_of_robust_cut (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B)
    (m a r t : ℕ) (ai : I → ℕ)
    (hmA : Fintype.card A = m) (hmB : Fintype.card B = m)
    (hsize : ∀ i ∈ K, (U i).card + 2 * ai i = m ∧ (W i).card + 2 * ai i = m ∧ ai i ≤ a)
    (hMargin : 2 * a + max X.card Y.card ≤ r) (hPrev : K.card ≤ r)
    (hδA : ∀ x ∉ X, t + (2 * a + max X.card Y.card) + (K.card - 1) ≤
      (Yᶜ.filter fun y => 0 < cap x y).card)
    (hδB : ∀ y ∉ Y, t + (2 * a + max X.card Y.card) + (K.card - 1) ≤
      (Xᶜ.filter fun x => 0 < cap x y).card)
    (hExpand : ∀ S ⊆ (Xᶜ : Finset A), t ≤ S.card → S.card + t ≤ (Xᶜ : Finset A).card →
      S.card + r ≤ (Yᶜ.filter fun y => r ≤ (S.filter fun x => 0 < cap x y).card).card)
    (rowsA : RowReserves U W cap K X Y)
    (rowsB : RowReserves W U (fun y x => cap x y) K Y X) :
    Nonempty (CrossingPacking U W cap K) := by
  classical
  apply exists_crossing_packing U W cap K
  intro i hi loss hLossA hLossB
  obtain ⟨hU,hW,ha⟩ := hsize i hi
  let p := K.card - 1
  let d := t + (2 * a + max X.card Y.card) + p
  have hcoverA : ((U i)ᶜ).card = 2 * ai i := by rw [card_compl,hmA]; omega
  have hcoverB : ((W i)ᶜ).card = 2 * ai i := by rw [card_compl,hmB]; omega
  have hDelB : (Yᶜ \ W i).card ≤ 2 * ai i := by
    rw [← hcoverB]
    exact card_le_card (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2)
  have hDelA : (Xᶜ \ U i).card ≤ 2 * ai i := by
    rw [← hcoverA]
    exact card_le_card (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2)
  let R := fun x y => 0 < cap x y
  let Q := fun x y => 0 < cap x y - loss x y
  apply exists_matching_of_robust_exceptional_hall (U i) (W i) X Y R Q r t
  · omega
  · have hx := le_max_left X.card Y.card
    omega
  · intro x _ hx
    have h := ordinary_degree_after_spending Yᶜ (W i) (cap x) (loss x)
      (2 * ai i) p d hDelB (hLossA x) (hδA x hx)
    have hD : t + X.card ≤ d - 2 * ai i - p := by
      have hMax := le_max_left X.card Y.card
      dsimp [d]
      omega
    have hEq : ((Yᶜ ∩ W i).filter fun y => 0 < cap x y - loss x y) =
        (W i).filter (fun y => y ∉ Y ∧ Q x y) := by
      ext y
      simp [Q,and_assoc,and_comm]
    rw [hEq] at h
    have hh := hD.trans h
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [Q,R])
  · intro y _ hy
    have h := ordinary_degree_after_spending Xᶜ (U i) (fun x => cap x y) (fun x => loss x y)
      (2 * ai i) p d hDelA (hLossB y) (hδB y hy)
    have hD : t ≤ d - 2 * ai i - p := by dsimp [d]; omega
    have hEq : ((Xᶜ ∩ U i).filter fun x => 0 < cap x y - loss x y) =
        (U i).filter (fun x => x ∉ X ∧ Q x y) := by
      ext x
      simp [Q,and_assoc,and_comm]
    rw [hEq] at h
    have hh := hD.trans h
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [Q,R])
  · intro y _ _
    have hp : p < r := by
      have hk := card_pos.mpr ⟨i,hi⟩
      dsimp [p]
      omega
    have hh := (lost_neighbors_le_spent (U i) (fun x => cap x y) (fun x => loss x y)
      p (hLossB y)).trans_lt hp
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [Q,R])
  · intro S hS ht ht'
    have hh := hExpand S hS ht ht'
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [R])
  · intro S hS
    have h := rowsA.hall i hi loss hLossA S hS
    convert h using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [Q])
  · intro T hT
    have h := rowsB.hall i hi (fun y x => loss x y) hLossB T hT
    convert h using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp [Q])

end WeightedPaper
