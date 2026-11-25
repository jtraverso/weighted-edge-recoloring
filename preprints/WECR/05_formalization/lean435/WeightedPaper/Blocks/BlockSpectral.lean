import WeightedPaper.Blocks.BlockCutCriterion
import WeightedPaper.Cut.PairDegreeCuts

namespace WeightedPaper.Blocks

open Finset SimpleGraph
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

private def inclusion {T L : Finset A} (h : T ⊆ L) : T ↪ L :=
  ⟨fun x => ⟨x,h x.2⟩,fun _ _ he => Subtype.ext (congrArg (fun z : L => (z : A)) he)⟩

private theorem subset_compl_empty {V : Type*} [Fintype V] (s : Finset V) (de : DecidableEq V) :
    s ⊆ @compl _ (@BooleanAlgebra.toCompl _ (@Finset.booleanAlgebra _ _ de)) ∅ := by
  let _ : DecidableEq V := de
  show s ⊆ (∅ : Finset V)ᶜ
  rw [compl_empty]
  exact subset_univ _

omit [Fintype A] [Fintype B] in
/-- Apply the 0.4 spectral criterion to the induced ordinary block. -/
theorem rectangle_of_local_spectrum (cap : A → B → ℕ) (L : Finset A) (R : Finset B)
    (a k : ℕ) (hk : 0 < k)
    (hSpectrum : SpectralCutThreeFourths (fun (x : L) (y : R) => cap x y) ∅ ∅ a k) :
    Rectangle cap L R (L.card-2*a) k := by
  have hPair := (pair_degree_of_spectral (Fintype.card_coe L) hk hSpectrum).of_support
  intro S hS T hT hSn hTn hSize
  let s := S.attach.map (inclusion hS)
  let t := T.attach.map (inclusion hT)
  have hs : s.card = S.card := by simp [s]
  have ht : t.card = T.card := by simp [t]
  have h := hPair s (subset_compl_empty s _) t (subset_compl_empty t _)
    (card_pos.mp (by simpa only [hs] using card_pos.mpr hSn))
    (card_pos.mp (by simpa only [ht] using card_pos.mpr hTn)) (by simp only [hs,ht,card_empty]; omega)
  rcases h with ⟨x,hx,hdeg⟩ | ⟨y,hy,hdeg⟩
  · obtain ⟨v,_,rfl⟩ := mem_map.mp hx
    refine Or.inl ⟨v.val,v.2,?_⟩
    simp only [t,sum_map] at hdeg
    change k ≤ ∑ y ∈ T.attach, cap v.val y.val at hdeg
    rw [← sum_attach T (fun y => cap v.val y)]
    exact hdeg
  · obtain ⟨v,_,rfl⟩ := mem_map.mp hy
    refine Or.inr ⟨v.val,v.2,?_⟩
    simp only [s,sum_map] at hdeg
    change k ≤ ∑ x ∈ S.attach, cap x.val v.val at hdeg
    rw [← sum_attach S (fun x => cap x v.val)]
    exact hdeg

omit [Fintype A] [Fintype B] in
theorem rectangle_of_complete_support (cap : A → B → ℕ) (L : Finset A) (R : Finset B)
    (threshold k : ℕ) (hwidth : 2*(k-1) ≤ threshold)
    (hcomplete : ∀ x ∈ L, ∀ y ∈ R, 0 < cap x y) :
    Rectangle cap L R threshold k := by
  intro S hS T hT hSn hTn hsize
  by_cases ht : k ≤ T.card
  · obtain ⟨x,hx⟩ := hSn
    refine Or.inl ⟨x,hx,ht.trans ?_⟩
    simpa using sum_le_sum (s := T) (f := fun _ => (1:ℕ)) (g := cap x)
      (fun y hy => hcomplete x (hS hx) y (hT hy))
  · have hs : k ≤ S.card := by omega
    obtain ⟨y,hy⟩ := hTn
    refine Or.inr ⟨y,hy,hs.trans ?_⟩
    simpa using sum_le_sum (s := S) (f := fun _ => (1:ℕ)) (g := fun x => cap x y)
      (fun x hx => hcomplete x (hS hx) y (hT hy))

/-- An empty off-block rectangle witnesses failure of the global 0.4
criterion, including its version that counts parallel copies. -/
theorem not_pair_degree_of_empty_rectangle (cap : A → B → ℕ) (X : Finset A) (Y : Finset B)
    (S : Finset A) (T : Finset B) (hS : S ⊆ ordinary X) (hT : T ⊆ ordinary Y)
    (hSn : S.Nonempty) (hTn : T.Nonempty) (m a k : ℕ) (hk : 0 < k)
    (hSize : m < S.card + T.card + 2*a + X.card + Y.card)
    (hZero : ∀ x ∈ S, ∀ y ∈ T, cap x y = 0) :
    ¬ PairDegreeCondition cap X Y m a k := by
  classical
  intro h
  rcases h S (fun x hx => mem_compl.mpr ((mem_ordinary X x).mp (hS hx)))
      T (fun y hy => mem_compl.mpr ((mem_ordinary Y y).mp (hT hy))) hSn hTn hSize
    with ⟨x,hx,hxdeg⟩ | ⟨y,hy,hydeg⟩
  · rw [sum_eq_zero (hZero x hx)] at hxdeg
    omega
  · rw [sum_eq_zero (fun x hx => hZero x hx y hy)] at hydeg
    omega

/-- Local spectral data and the quotient cut conditions imply a
factorization. The full ordinary crossing support may be disconnected. -/
theorem exists_factorization_of_spectral_blocks {J V : Type*} [Fintype J] [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k ≤ D) (hkpos : 0 < k)
    (hreg : M.IsRegularOfDegree D) (C : (M.internalPart L).EdgeColoring k)
    (X : Finset L) (Y : Finset (Lᶜ : Finset V)) (left : L → J) (right : (Lᶜ : Finset V) → J)
    (a : J → ℕ)
    (eligibleA : Fin k → L → J → Prop) (eligibleB : Fin k → (Lᶜ : Finset V) → J → Prop)
    (hSpectrum : ∀ j, SpectralCutThreeFourths
      (fun (x : fiber (ordinary X) left j) (y : fiber (ordinary Y) right j) =>
        M.mult s(x.val.val,y.val.val)) ∅ ∅ (a j) k)
    (rowsA : BlockReserves (missingOn C L) (missingOn C Lᶜ) (fun x y => M.mult s(x.val,y.val))
      univ X Y right eligibleA)
    (rowsB : BlockReserves (missingOn C Lᶜ) (missingOn C L) (fun y x => M.mult s(x.val,y.val))
      univ Y X left eligibleB)
    (cuts : ∀ i, BlockCuts (missingOn C L i) (missingOn C Lᶜ i) X Y left right
      (fun j => (fiber (ordinary X) left j).card - 2*a j) (eligibleA i) (eligibleB i)) :
    ∃ F : M.EdgeColoring D, F.IsFactorization :=
  exists_factorization_of_block_cuts M L D k hk hreg C X Y left right
    (fun j => (fiber (ordinary X) left j).card-2*a j) eligibleA eligibleB
    (fun j => rectangle_of_local_spectrum _ _ _ _ k hkpos (hSpectrum j)) rowsA rowsB cuts

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.exists_factorization_of_spectral_blocks
#print axioms WeightedPaper.Blocks.rectangle_of_local_spectrum
#print axioms WeightedPaper.Blocks.not_pair_degree_of_empty_rectangle
