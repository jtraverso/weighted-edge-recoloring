import WeightedPaper.Cut.ReleaseAudit
import WeightedPaper.Cut.Mixing
import WeightedPaper.FullCriterion

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {I A B : Type*} [Fintype A] [Fintype B]

def incidence (cap : A → B → ℕ) (x : A) (y : B) : ℝ := if 0 < cap x y then 1 else 0

/-- Variational formulation of condition (S), with the ordinary
biadjacency acting on the two separate mean-zero subspaces. -/
structure SpectralCut (cap : A → B → ℕ) (X : Finset A) (Y : Finset B) (a k : ℕ) where
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
    4*(∑ x ∈ Xᶜ, u x*(∑ y ∈ Yᶜ,v y*incidence cap x y))^2 ≤
      (d:ℝ)^2*(∑ x ∈ Xᶜ,(u x)^2)*(∑ y ∈ Yᶜ,(v y)^2)

private theorem sum_indicator {C : Type*} (S : Finset C) (f : C → ℕ) :
    (∑ z ∈ S, if 0<f z then (1:ℝ) else 0) = ((S.filter fun z => 0<f z).card:ℝ) := by
  rw [← sum_filter]
  simp

theorem packing_of_spectral_cut (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B)
    (m a : ℕ) (ai : I → ℕ)
    (hmA : Fintype.card A = m) (hmB : Fintype.card B = m)
    (hsize : ∀ i ∈ K, (U i).card + 2*ai i = m ∧ (W i).card + 2*ai i = m ∧ ai i ≤ a)
    (H : SpectralCut cap X Y a K.card)
    (rowsA : RowReserves U W cap K X Y)
    (rowsB : RowReserves W U (fun y x => cap x y) K Y X) :
    Nonempty (CrossingPacking U W cap K) := by
  classical
  apply exists_crossing_packing U W cap K
  intro i hi loss hLossA hLossB
  obtain ⟨hU,hW,ha⟩ := hsize i hi
  have hm : m = H.N+X.card := by
    have hc := card_compl_add_card X
    rw [H.hA,hmA] at hc
    omega
  have hN := H.degree_le_order
  apply matching_of_mixing (U i) X (W i) Y cap loss H.N H.d (ai i) (K.card-1) X.card
    (hU.trans hm) (hW.trans hm) rfl H.same.symm H.degree_pos hN (by have := H.cost; omega)
    hLossA hLossB
  · intro x hx hn
    have hc : (Yᶜ \ W i).card ≤ 2*ai i := by
      have h := card_le_card (show Yᶜ \ W i ⊆ (W i)ᶜ from fun y hy => mem_compl.mpr (mem_sdiff.mp hy).2)
      rw [card_compl,hmB] at h
      omega
    exact (ordinary_degree_after_spending Yᶜ (W i) (cap x) (loss x) _ _ _ hc (hLossA x)
      (H.leftDegree x hn).ge).trans (card_le_card fun y hy =>
        mem_filter.mpr ⟨(mem_inter.mp (mem_filter.mp hy).1).2,(mem_filter.mp hy).2⟩)
  · intro y hy hn
    have hc : (Xᶜ \ U i).card ≤ 2*ai i := by
      have h := card_le_card (show Xᶜ \ U i ⊆ (U i)ᶜ from fun x hx => mem_compl.mpr (mem_sdiff.mp hx).2)
      rw [card_compl,hmA] at h
      omega
    exact (ordinary_degree_after_spending Xᶜ (U i) (fun x => cap x y) (fun x => loss x y) _ _ _ hc
      (hLossB y) (H.rightDegree y hn).ge).trans (card_le_card fun x hx =>
        mem_filter.mpr ⟨(mem_inter.mp (mem_filter.mp hx).1).2,(mem_filter.mp hx).2⟩)
  · intro S hS
    exact (rowsA.hall i hi loss hLossA S hS).trans (card_le_card fun y hy =>
      mem_filter.mpr ⟨(mem_filter.mp hy).1,(mem_filter.mp hy).2.2⟩)
  · intro T hT
    exact (rowsB.hall i hi (fun y x => loss x y) hLossB T hT).trans (card_le_card fun x hx =>
      mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.2⟩)
  · apply Spectral.indicator_mixing _ _ _ _ (by exact_mod_cast H.degree_pos.trans_le hN)
      (by exact_mod_cast H.hA) (by exact_mod_cast H.hB) (incidence cap)
    · intro x hx
      simp only [incidence, sum_indicator]
      exact_mod_cast H.leftDegree x (mem_compl.mp hx)
    · intro y hy
      simp only [incidence, sum_indicator]
      exact_mod_cast H.rightDegree y (mem_compl.mp hy)
    · exact H.spectral

end WeightedPaper
