import WeightedPaper.RobustCut

namespace WeightedPaper
open Finset
open scoped Classical

variable {I A B : Type*} [Fintype A] [Fintype B]

/-- A large ordinary rectangle contains a row or column with at least `k`
units of capacity. The condition works with copies or with simple support. -/
def PairDegreeCondition (cap : A → B → ℕ) (X : Finset A) (Y : Finset B) (m a k : ℕ) : Prop :=
  ∀ S ⊆ Xᶜ, ∀ T ⊆ Yᶜ, S.Nonempty → T.Nonempty →
    m < S.card + T.card + 2*a + X.card + Y.card →
    (∃ x ∈ S, k ≤ ∑ y ∈ T, cap x y) ∨ (∃ y ∈ T, k ≤ ∑ x ∈ S, cap x y)

def supportCapacity (cap : A → B → ℕ) (x : A) (y : B) : ℕ := if 0 < cap x y then 1 else 0

theorem PairDegreeCondition.mono {cap next : A → B → ℕ} {X : Finset A} {Y : Finset B} {m a k : ℕ}
    (H : PairDegreeCondition cap X Y m a k) (hle : ∀ x y, cap x y ≤ next x y) :
    PairDegreeCondition next X Y m a k := by
  intro S hS T hT hNS hNT hSize
  rcases H S hS T hT hNS hNT hSize with ⟨x,hx,hd⟩ | ⟨y,hy,hd⟩
  · exact Or.inl ⟨x,hx,hd.trans (sum_le_sum fun y _ => hle x y)⟩
  · exact Or.inr ⟨y,hy,hd.trans (sum_le_sum fun x _ => hle x y)⟩

theorem PairDegreeCondition.of_support {cap : A → B → ℕ} {X : Finset A} {Y : Finset B} {m a k : ℕ}
    (H : PairDegreeCondition (supportCapacity cap) X Y m a k) : PairDegreeCondition cap X Y m a k := by
  apply H.mono
  intro x y
  unfold supportCapacity
  split_ifs <;> omega

/-- The edge-count certificate implies the row-or-column certificate. -/
theorem pair_degree_of_edge_count {cap : A → B → ℕ} {X : Finset A} {Y : Finset B} {m a k : ℕ}
    (H : ∀ S ⊆ Xᶜ, ∀ T ⊆ Yᶜ, S.Nonempty → T.Nonempty →
      m < S.card + T.card + 2*a + X.card + Y.card →
      (k-1)*min S.card T.card < ∑ x ∈ S, ∑ y ∈ T, cap x y) :
    PairDegreeCondition cap X Y m a k := by
  intro S hS T hT hNS hNT hSize
  by_contra! hn
  have h := H S hS T hT hNS hNT hSize
  rcases le_total S.card T.card with hST | hTS
  · rw [min_eq_left hST] at h
    have hh : (∑ x ∈ S, ∑ y ∈ T, cap x y) ≤ ∑ _x ∈ S, (k-1) :=
      sum_le_sum fun x hx => Nat.le_sub_one_of_lt (hn.1 x hx)
    rw [sum_const, Nat.nsmul_eq_mul, Nat.mul_comm] at hh
    omega
  · rw [min_eq_right hTS, sum_comm] at h
    have hh : (∑ y ∈ T, ∑ x ∈ S, cap x y) ≤ ∑ _y ∈ T, (k-1) :=
      sum_le_sum fun y hy => Nat.le_sub_one_of_lt (hn.2 y hy)
    rw [sum_const, Nat.nsmul_eq_mul, Nat.mul_comm] at hh
    omega

/-- Exceptional Hall on both sides reduces each round to an ordinary rectangle. -/
theorem matching_of_pair_degree (U X : Finset A) (W Y : Finset B)
    (cap loss : A → B → ℕ) (m a k : ℕ) (hk : 0 < k)
    (hUW : U.card = W.card) (hsize : m ≤ U.card + 2*a)
    (hrow : ∀ x, (∑ y, loss x y) ≤ k-1) (hcol : ∀ y, (∑ x, loss x y) ≤ k-1)
    (hexA : ∀ S ⊆ U.filter (· ∈ X),
      S.card ≤ (W.filter fun y => ∃ x ∈ S, 0 < cap x y-loss x y).card)
    (hexB : ∀ T ⊆ W.filter (· ∈ Y),
      T.card ≤ (U.filter fun x => ∃ y ∈ T, 0 < cap x y-loss x y).card)
    (H : PairDegreeCondition cap X Y m a k) :
    ∃ f : U ≃ W, ∀ x : U, 0 < cap x (f x)-loss x (f x) := by
  classical
  let R := fun x y => 0 < cap x y-loss x y
  let _ : DecidableRel R := fun x y => Classical.propDecidable (R x y)
  apply exists_equiv_of_finset_hall U W R hUW
  intro S hS
  let Z := W.filter fun y => ∃ x ∈ S, R x y
  let T := W \ Z
  have htW : T ⊆ W := sdiff_subset
  have hzW : Z ⊆ W := filter_subset _ _
  change S.card ≤ Z.card
  by_contra! hBad
  have hTcard : T.card + Z.card = W.card := card_sdiff_add_card_eq_card hzW
  have hnone (x) (hx : x ∈ S) (y) (hy : y ∈ T) : cap x y ≤ loss x y := by
    have hh : ¬ R x y := fun h =>
      (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨htW hy,x,hx,h⟩)
    dsimp [R] at hh
    omega
  have hBadT : (U.filter fun x => ∃ y ∈ T, R x y).card < T.card := by
    have hsub : (U.filter fun x => ∃ y ∈ T, R x y) ⊆ U \ S := by
      intro x hx
      obtain ⟨hUx,y,hy,he⟩ := mem_filter.mp hx
      exact mem_sdiff.mpr ⟨hUx,fun h => Nat.not_lt_of_ge (hnone x h y hy) (Nat.sub_pos_iff_lt.mp he)⟩
    have hh := card_le_card hsub
    rw [card_sdiff_of_subset hS] at hh
    have hSU := card_le_card hS
    omega
  have hsX : (S \ X).Nonempty := by
    by_contra hn
    have hsub : S ⊆ X := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)
    have hHall := hexA S (fun _ hx => mem_filter.mpr ⟨hS hx,hsub hx⟩)
    apply (Nat.not_le_of_gt hBad)
    convert hHall using 2
    ext y
    simp [Z,R]
  have htY : (T \ Y).Nonempty := by
    by_contra hn
    have hsub : T ⊆ Y := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)
    have hHall := hexB T (fun _ hy => mem_filter.mpr ⟨htW hy,hsub hy⟩)
    apply (Nat.not_le_of_gt hBadT)
    convert hHall using 2
    ext x
    simp [R]
  have hLarge : m < (S \ X).card + (T \ Y).card + 2*a + X.card + Y.card := by
    have h₁ := card_sdiff_add_card_inter S X
    have h₂ := card_sdiff_add_card_inter T Y
    have h₃ := card_le_card (inter_subset_right (s₁:=S) (s₂:=X))
    have h₄ := card_le_card (inter_subset_right (s₁:=T) (s₂:=Y))
    omega
  rcases H (S \ X) (fun _ hx => mem_compl.mpr (mem_sdiff.mp hx).2)
    (T \ Y) (fun _ hx => mem_compl.mpr (mem_sdiff.mp hx).2) hsX htY hLarge with ⟨x,hx,h⟩ | ⟨y,hy,h⟩
  · have hcap := sum_le_sum (s:=T \ Y) fun y hy => hnone x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1
    have hbudget := (sum_le_univ_sum_of_nonneg (s:=T \ Y) (fun y => Nat.zero_le (loss x y))).trans (hrow x)
    omega
  · have hcap := sum_le_sum (s:=S \ X) fun x hx => hnone x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1
    have hbudget := (sum_le_univ_sum_of_nonneg (s:=S \ X) (fun x => Nat.zero_le (loss x y))).trans (hcol y)
    omega

theorem packing_of_pair_degree (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B)
    (m a : ℕ) (ai : I → ℕ)
    (hsize : ∀ i ∈ K, (U i).card + 2*ai i = m ∧ (W i).card + 2*ai i = m ∧ ai i ≤ a)
    (H : PairDegreeCondition cap X Y m a K.card)
    (rowsA : RowReserves U W cap K X Y)
    (rowsB : RowReserves W U (fun y x => cap x y) K Y X) :
    Nonempty (CrossingPacking U W cap K) := by
  classical
  apply exists_crossing_packing U W cap K
  intro i hi loss hLossA hLossB
  obtain ⟨hU,hW,ha⟩ := hsize i hi
  apply matching_of_pair_degree (U i) X (W i) Y cap loss m a K.card (card_pos.mpr ⟨i,hi⟩)
    (by omega) (by omega) hLossA hLossB _ _ H
  · intro S hS
    exact (rowsA.hall i hi loss hLossA S hS).trans (card_le_card fun y hy =>
      mem_filter.mpr ⟨(mem_filter.mp hy).1,(mem_filter.mp hy).2.2⟩)
  · intro T hT
    exact (rowsB.hall i hi (fun y x => loss x y) hLossB T hT).trans (card_le_card fun x hx =>
      mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.2⟩)

end WeightedPaper

#print axioms WeightedPaper.pair_degree_of_edge_count
#print axioms WeightedPaper.matching_of_pair_degree
#print axioms WeightedPaper.packing_of_pair_degree
