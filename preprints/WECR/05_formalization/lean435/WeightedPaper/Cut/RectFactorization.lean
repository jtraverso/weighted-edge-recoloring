import WeightedPaper.Cut.PairDegreeHost
import WeightedPaper.Cut.RectHost
import WeightedPaper.Cut.RectSpectrum

namespace WeightedPaper.Examples.RectGrid
open Finset SimpleGraph
variable {q : ℕ}

noncomputable def spectral (hq : 49 ≤ q) :
    SpectralCutThreeFourths ((host q).cap false true) (exSet (Row q) (Ord q) false)
      (exSet (Row q) (Ord q) true) (16*q) (32*q) := by
  have hd := (slack hq).2
  refine ⟨order q,degree q,by rw [ordinary_complement,card_ordSet,card_ord]; rfl,by rw [ordinary_complement,card_ordSet,card_ord]; rfl,
    by simp,by omega,by unfold degree; omega,by simp [degree]; omega,?_,?_,?_⟩
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    have h := ((host q).ordinaryNeighbours_compl Bool.false_ne_true x).trans (support_degree x)
    simpa only [ordinary_complement] using h
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    have h := ((host q).ordinaryNeighbours_compl' Bool.false_ne_true x).trans (support_degree x)
    simpa only [ordinary_complement] using h
  · intro u v hu hv
    simp only [ordinary_complement,ordSet,sum_map,incidence,Host.capOrd _ Bool.false_ne_true] at hv ⊢
    change 16*(∑ x,u (ordEmb false x)*(∑ y,v (ordEmb true y)*(if 0<ordinary x y then 1 else 0)))^2 ≤ _
    simp only [support_iff]
    have h := bilinear_bound (by omega : 2≤q) (fun x => u (ordEmb false x))
      (fun y => v (ordEmb true y)) hv
    simpa only [applySupport,degree,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (by omega : 1 ≤ 3*q),
      Nat.cast_one] using h

theorem factorization (hq : 49 ≤ q) :
    ∃ F : (host q).graph.EdgeColoring (order q), F.IsFactorization := by
  have he : order q = (32*q)*(16*q) := by unfold order; ring
  have hk : 1 ≤ 32*q := by omega
  have hcol (b : Bool) : Nonempty (((host q).graph.restrict (half (Row q) (Ord q) b)).EdgeColoring (32*q)) := by
    apply (host q).colourable_inside b _ (fun x => x.2.2.1)
    · intro x y h
      change internal x y = 0
      simp [internal,quadInternal_zero _ _ h]
    · intro x
      change (∑ y,internal x y) ≤ 32*q
      rw [inside_degree]
      omega
  apply (host q).finishPairDegree _ (32*q) (16*q) (by rw [he]; nlinarith)
    (regular hq) (by rw [internal_mass,he]) (hcol false) (hcol true)
  · rw [internal_mass,equitableGap,if_pos (show 32*q ∣ order q from ⟨16*q,he⟩)]
    exact row_budget hq
  · exact (pair_degree_of_spectral (by simp only [Fintype.card_coe,side_card]) (by omega) (spectral hq)).of_support

end WeightedPaper.Examples.RectGrid

#print axioms WeightedPaper.Examples.RectGrid.factorization
