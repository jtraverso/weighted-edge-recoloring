import WeightedPaper.VectorBalance
import WeightedRecolouring.Balance

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k n : ℕ}

/-- This is the square of the discrepancy factor in Theorem 1 of the
manuscript, so no square root or choice of sign is needed in the API. -/
noncomputable def discrepancyFactorSq (n : ℕ) (d : ℝ) : ℝ :=
  if n = 0 then 0 else
    if n = 1 then (if d = 0 then 4 else d^2) else d^2 + 4*n

/-- Weighted balancing for centred coordinate profiles, with the sharp
rank-one clause and the higher-rank Euclidean bound. -/
theorem exists_balanced_euclidean_prescribed_sizes (C : M.EdgeColoring k)
    (w : V → Fin n → ℝ) (center : Fin n → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hw : ∀ v, energy (fun j => w v j - center j) ≤ R^2) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ a b, energy (fun j =>
        (WeightedRecolouring.load D (fun v => w v j) a - 2 * center j * (C.colourMass a : ℝ)) -
        (WeightedRecolouring.load D (fun v => w v j) b - 2 * center j * (C.colourMass b : ℝ))) ≤
          (2*R)^2 * discrepancyFactorSq n ((C.colourMass a : ℝ)-C.colourMass b) := by
  let z (v : V) (j : Fin n) := w v j-center j
  suffices H : ∃ D : M.EdgeColoring k, (∀ i,D.colourMass i=C.colourMass i) ∧
      ∀ a b, energy (fun j => WeightedRecolouring.load D (fun v => z v j) a -
        WeightedRecolouring.load D (fun v => z v j) b) ≤
          (2*R)^2 * discrepancyFactorSq n ((C.colourMass a : ℝ)-C.colourMass b) by
    obtain ⟨D,hD,hBal⟩ := H
    refine ⟨D,hD,fun a b => ?_⟩
    have hh := hBal a b
    simp only [z,WeightedRecolouring.load_shift,hD] at hh
    exact hh
  by_cases hn : n = 0
  · subst n
    exact ⟨C,fun _ => rfl,fun a b => by simp [energy,discrepancyFactorSq]⟩
  by_cases hn₁ : n = 1
  · subst n
    let f (v : V) := z v 0
    have hwt (v : V) : (f v)^2 ≤ R^2 := by
      simpa only [energy,Fin.sum_univ_one] using hw v
    have hLow (v : V) : -R ≤ f v := by nlinarith [hwt v,sq_nonneg (f v+R)]
    have hHigh (v : V) : f v ≤ R := by nlinarith [hwt v,sq_nonneg (f v-R)]
    obtain ⟨D,hD,heq,hgt⟩ := WeightedRecolouring.exists_balanced_prescribed_sizes C f
      (-R) R (by linarith) hLow hHigh
    refine ⟨D,hD,fun a b => ?_⟩
    simp only [energy,Fin.sum_univ_one,discrepancyFactorSq,one_ne_zero,if_false,if_true]
    change (WeightedRecolouring.load D f a-WeightedRecolouring.load D f b)^2 ≤ _
    let d : ℝ := (C.colourMass a : ℝ)-C.colourMass b
    change _ ≤ (2*R)^2 * (if d = 0 then 4 else d^2)
    rcases lt_trichotomy (C.colourMass a) (C.colourMass b) with h|h|h
    · have hneg : d < 0 := sub_neg.mpr (by exact_mod_cast h)
      have hh := hgt b a h
      have hAbs : |WeightedRecolouring.load D f a-WeightedRecolouring.load D f b| ≤ 2*R*(-d) := by
        dsimp [d]
        apply abs_le.mpr
        constructor <;> linarith only [hh.1,hh.2]
      rw [if_neg hneg.ne]
      have hs := sq_le_sq.mpr (hAbs.trans_eq
        (abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ 2*R) (neg_nonneg.mpr hneg.le))).symm)
      nlinarith only [hs]
    · have hd : d = 0 := by simp [d,h]
      have hAbs : |WeightedRecolouring.load D f a-WeightedRecolouring.load D f b| ≤ 4*R := by
        have hh := heq a b h
        linarith
      rw [if_pos hd]
      have hs := sq_le_sq.mpr (hAbs.trans_eq (abs_of_nonneg (by linarith : 0 ≤ 4*R)).symm)
      nlinarith only [hs]
    · have hpos : 0 < d := sub_pos.mpr (by exact_mod_cast h)
      have hh := hgt a b h
      have hAbs : |WeightedRecolouring.load D f a-WeightedRecolouring.load D f b| ≤ 2*R*d := by
        dsimp [d]
        apply abs_le.mpr
        constructor <;> linarith only [hh.1,hh.2]
      rw [if_neg hpos.ne']
      have hs := sq_le_sq.mpr (hAbs.trans_eq
        (abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ 2*R) hpos.le)).symm)
      nlinarith only [hs]
  · obtain ⟨D,hD,hb⟩ := exists_balanced_vector_prescribed_sizes C z R hR hw
    exact ⟨D,hD,fun a b => by simpa only [discrepancyFactorSq,if_neg hn,if_neg hn₁] using hb a b⟩

end WeightedPaper
