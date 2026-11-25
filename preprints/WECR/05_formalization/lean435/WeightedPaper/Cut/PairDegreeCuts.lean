import WeightedPaper.Cut.PairDegreeHall
import WeightedPaper.Cut.SpectralBudget
import WeightedPaper.Cut.SpectralCut
import WeightedPaper.Cut.MixingCoefficient

namespace WeightedPaper
open Finset
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

private theorem support_split {V : Type*} [Fintype V] (O S : Finset V) (P : V → Prop)
    [DecidablePred P]
    (hS : S ⊆ O) : (O.filter P).card ≤ (S.filter P).card + O.card - S.card := by
  classical
  have hF : S.filter P ⊆ O.filter P := filter_subset_filter _ hS
  have hsub : O.filter P \ S.filter P ⊆ O \ S := by
    intro x hx
    obtain ⟨hxO,hxP⟩ := mem_filter.mp (mem_sdiff.mp hx).1
    exact mem_sdiff.mpr ⟨hxO,fun h => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨h,hxP⟩)⟩
  have h₁ := card_sdiff_add_card_eq_card hF
  have h₂ := card_le_card hsub
  rw [card_sdiff_of_subset hS] at h₂
  have h₃ := card_le_card hS
  omega

omit [Fintype A] [Fintype B] in
private theorem card_support_row (cap : A → B → ℕ) (T : Finset B) (x : A) :
    (∑ y ∈ T, supportCapacity cap x y) = (T.filter fun y => 0 < cap x y).card := by
  rw [card_eq_sum_ones,sum_filter]
  rfl

omit [Fintype A] [Fintype B] in
private theorem card_support_column (cap : A → B → ℕ) (S : Finset A) (y : B) :
    (∑ x ∈ S, supportCapacity cap x y) = (S.filter fun x => 0 < cap x y).card := by
  rw [card_eq_sum_ones,sum_filter]
  rfl

theorem pair_degree_of_dense {cap : A → B → ℕ} {X : Finset A} {Y : Finset B} {m a k : ℕ}
    (hmA : Fintype.card A = m) (hmB : Fintype.card B = m) (hk : 0 < k)
    (H : DenseCut cap X Y m a k) : PairDegreeCondition (supportCapacity cap) X Y m a k := by
  obtain ⟨δA,δB,hBound,hA,hB⟩ := H
  intro S hS T hT hNS hNT hLarge
  by_contra! hn
  obtain ⟨x,hx⟩ := hNS
  obtain ⟨y,hy⟩ := hNT
  have hL := (hA x (mem_compl.mp (hS hx))).trans (support_split Yᶜ T (fun y => 0 < cap x y) hT)
  have hR := (hB y (mem_compl.mp (hT hy))).trans (support_split Xᶜ S (fun x => 0 < cap x y) hS)
  have hRow := hn.1 x hx
  have hCol := hn.2 y hy
  rw [card_support_row] at hRow
  rw [card_support_column] at hCol
  have hSizeA := card_compl_add_card X
  have hSizeB := card_compl_add_card Y
  have hSubA := card_le_card hS
  have hSubB := card_le_card hT
  omega

theorem pair_degree_of_robust {cap : A → B → ℕ} {X : Finset A} {Y : Finset B} {m a k : ℕ}
    (hmA : Fintype.card A = m) (hmB : Fintype.card B = m)
    (H : RobustCut cap X Y a k) : PairDegreeCondition (supportCapacity cap) X Y m a k := by
  obtain ⟨r,t,hMargin,hPrev,hA,hB,hExpand⟩ := H
  intro S hS T hT hNS hNT hLarge
  have hSizeA := card_compl_add_card X
  have hSizeB := card_compl_add_card Y
  have hSubA := card_le_card hS
  have hSubB := card_le_card hT
  have hX := le_max_left X.card Y.card
  by_cases hs : S.card ≤ t
  · obtain ⟨x,hx⟩ := hNS
    have h := (hA x (mem_compl.mp (hS hx))).trans (support_split Yᶜ T (fun y => 0 < cap x y) hT)
    rw [←card_support_row] at h
    exact Or.inl ⟨x,hx,by omega⟩
  by_cases hWide : S.card+t ≤ (Xᶜ : Finset A).card
  · let R := Yᶜ.filter fun y => r ≤ (S.filter fun x => 0 < cap x y).card
    have hR : S.card+r ≤ R.card := hExpand S hS (by omega) hWide
    have hUnion := card_le_card (union_subset (filter_subset _ _) hT : R ∪ T ⊆ Yᶜ)
    have hInter := card_union_add_card_inter R T
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (R ∩ T).card by omega)
    have h := (mem_filter.mp (mem_inter.mp hy).1).2
    rw [←card_support_column] at h
    exact Or.inr ⟨y,(mem_inter.mp hy).2,hPrev.trans h⟩
  · obtain ⟨y,hy⟩ := hNT
    have h := (hB y (mem_compl.mp (hT hy))).trans (support_split Xᶜ S (fun x => 0 < cap x y) hS)
    rw [←card_support_column] at h
    exact Or.inr ⟨y,hy,by omega⟩

/-- The variational bound uses the second singular value at most 3d/4. -/
structure SpectralCutThreeFourths (cap : A → B → ℕ) (X : Finset A) (Y : Finset B) (a k : ℕ) where
  N : ℕ
  d : ℕ
  hA : (Xᶜ : Finset A).card = N
  hB : (Yᶜ : Finset B).card = N
  same : X.card = Y.card
  degree_le_order : d ≤ N
  degree_pos : 0 < d
  cost : 8*(2*a+X.card+(k-1)) ≤ d
  leftDegree : ∀ x ∉ X, ((Yᶜ).filter fun y => 0 < cap x y).card = d
  rightDegree : ∀ y ∉ Y, ((Xᶜ).filter fun x => 0 < cap x y).card = d
  spectral : ∀ (u : A → ℝ) (v : B → ℝ),
    (∑ x ∈ Xᶜ,u x)=0 → (∑ y ∈ Yᶜ,v y)=0 →
    16*(∑ x ∈ Xᶜ, u x*(∑ y ∈ Yᶜ,v y*incidence cap x y))^2 ≤
      9*(d:ℝ)^2*(∑ x ∈ Xᶜ,(u x)^2)*(∑ y ∈ Yᶜ,(v y)^2)

private theorem sum_indicator_real {V : Type*} (S : Finset V) (f : V → ℕ) :
    (∑ z ∈ S, if 0<f z then (1:ℝ) else 0) = ((S.filter fun z => 0<f z).card:ℝ) := by
  rw [← sum_filter]
  simp

theorem pair_degree_of_spectral {cap : A → B → ℕ} {X : Finset A} {Y : Finset B} {m a k : ℕ}
    (hmA : Fintype.card A = m) (hk : 0 < k) (H : SpectralCutThreeFourths cap X Y a k) :
    PairDegreeCondition (supportCapacity cap) X Y m a k := by
  apply pair_degree_of_edge_count
  intro S hS T hT hNS hNT hLarge
  by_contra! hSpent
  let e := ∑ x ∈ S, ∑ y ∈ T, supportCapacity cap x y
  have hLeft : e ≤ (k-1)*S.card := hSpent.trans (Nat.mul_le_mul_left _ (min_le_left _ _))
  have hRight : e ≤ (k-1)*T.card := hSpent.trans (Nat.mul_le_mul_left _ (min_le_right _ _))
  -- First handle a small side by averaging the individual loss of neighbors.
  have hLargeS : H.d < S.card + (2*a+X.card) + (k-1) := by
    by_contra! hn
    have hEach (x : A) (hx : x ∈ S) : k ≤ ∑ y ∈ T, supportCapacity cap x y := by
      have h := support_split Yᶜ T (fun y => 0 < cap x y) hT
      rw [H.leftDegree x (mem_compl.mp (hS hx)),H.hB,←card_support_row] at h
      have hSize := card_compl_add_card X
      rw [H.hA,hmA] at hSize
      have hSame := H.same
      have hTbound := card_le_card hT
      rw [H.hB] at hTbound
      omega
    have hsum : (∑ _x ∈ S,k) ≤ e := sum_le_sum hEach
    simp only [sum_const,Nat.nsmul_eq_mul] at hsum
    have hpos := card_pos.mpr hNS
    exact (not_lt_of_ge (hsum.trans hLeft)) (by rw [Nat.mul_comm _ k]; exact Nat.mul_lt_mul_of_pos_right (show k-1 < k by omega) hpos)
  have hLargeT : H.d < T.card + (2*a+X.card) + (k-1) := by
    by_contra! hn
    have hEach (y : B) (hy : y ∈ T) : k ≤ ∑ x ∈ S, supportCapacity cap x y := by
      have h := support_split Xᶜ S (fun x => 0 < cap x y) hS
      rw [H.rightDegree y (mem_compl.mp (hT hy)),H.hA,←card_support_column] at h
      have hSize := card_compl_add_card X
      rw [H.hA,hmA] at hSize
      have hSame := H.same
      have hSbound := card_le_card hS
      rw [H.hA] at hSbound
      omega
    have hsum : (∑ _y ∈ T,k) ≤ e := by rw [show e = ∑ y ∈ T, ∑ x ∈ S, supportCapacity cap x y from sum_comm]; exact sum_le_sum hEach
    simp only [sum_const,Nat.nsmul_eq_mul] at hsum
    have hpos := card_pos.mpr hNT
    exact (not_lt_of_ge (hsum.trans hRight)) (by rw [Nat.mul_comm _ k]; exact Nat.mul_lt_mul_of_pos_right (show k-1 < k by omega) hpos)
  let h := 2*a+X.card
  let p := k-1
  have hN : 0 < H.N := H.degree_pos.trans_le H.degree_le_order
  have hsum : H.N < h + S.card + T.card := by
    have hSize := card_compl_add_card X
    rw [H.hA,hmA] at hSize
    dsimp [h]
    have := H.same
    omega
  have hMix : 16 * (((H.N:ℝ) * (e:ℝ)) - (H.d:ℝ) * S.card * T.card)^2 ≤
      9*(H.d:ℝ)^2*S.card*T.card*((H.N-S.card)*(H.N-T.card)) := by
    have hm := Spectral.indicator_mixing_squared Xᶜ Yᶜ (H.N:ℝ) (H.d:ℝ) 16 (9*(H.d:ℝ)^2)
      (by exact_mod_cast hN) (by exact_mod_cast H.hA) (by exact_mod_cast H.hB)
      (incidence cap)
      (fun x hx => by
        simp only [incidence, sum_indicator_real]
        exact_mod_cast H.leftDegree x (mem_compl.mp hx))
      (fun y hy => by
        simp only [incidence, sum_indicator_real]
        exact_mod_cast H.rightDegree y (mem_compl.mp hy))
      H.spectral S hS T hT
    have he : (e:ℝ) = ∑ x ∈ S, ∑ y ∈ T, incidence cap x y := by
      simp [e,supportCapacity,incidence]
    rw [he]
    exact hm
  apply spectral_deficit_impossible_three_fourths (N:=(H.N:ℝ)) (d:=(H.d:ℝ))
    (h:=(h:ℝ)) (p:=(p:ℝ)) (s:=(S.card:ℝ)) (t:=(T.card:ℝ)) (e:=(e:ℝ))
  · exact_mod_cast hN
  · exact_mod_cast H.degree_pos
  · exact_mod_cast H.degree_le_order
  · positivity
  · positivity
  · exact_mod_cast H.cost
  · have hh : (H.d:ℝ) < (S.card:ℝ) + h + p := by exact_mod_cast hLargeS
    linarith only [hh]
  · have hh : (H.d:ℝ) < (T.card:ℝ) + h + p := by exact_mod_cast hLargeT
    linarith only [hh]
  · have hh : (H.N:ℝ) < (h:ℝ) + S.card + T.card := by exact_mod_cast hsum
    linarith only [hh]
  · exact_mod_cast hSpent
  · exact hMix

end WeightedPaper

#print axioms WeightedPaper.pair_degree_of_dense
#print axioms WeightedPaper.pair_degree_of_robust
#print axioms WeightedPaper.pair_degree_of_spectral
