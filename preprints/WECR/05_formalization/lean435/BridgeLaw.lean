import AdmissibleBridge
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace WeightedPaper.Repair
open Finset MeasureTheory

/-- Normalize a finite positive-mass restriction. Every possible sample is
inside the restriction and has strictly positive weight, including when a
later existence argument chooses a point without referring to its probability. -/
theorem restricted_law {Ω : Type*} [DecidableEq Ω] (allowed : Finset Ω)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (pos : 0 < ∑ x ∈ allowed, w x) :
    let good := allowed.filter (fun x => 0 < w x)
    ∃ p : PMF good, ∀ S : Finset good,
      (∑ x ∈ S, (p x).toReal) = (∑ x ∈ S, w x.val) / (∑ x ∈ allowed, w x) := by
  classical
  intro good
  let W := ∑ x ∈ allowed, w x
  have total : ∑ x : good, w x.val = W := by
    change (∑ x ∈ good.attach, w x.val) = W
    rw [sum_attach good w]
    apply sum_subset (filter_subset _ _)
    intro x hx hnot
    exact le_antisymm (le_of_not_gt (fun h => hnot (mem_filter.mpr ⟨hx,h⟩))) (hw x)
  let value (x : good) := ENNReal.ofReal (w x.val/W)
  have norm : ∑ x, value x = 1 := by
    dsimp only [value]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => div_nonneg (hw _) pos.le),
      ← sum_div, total, div_self pos.ne', ENNReal.ofReal_one]
  refine ⟨PMF.ofFintype value norm, fun S => ?_⟩
  rw [sum_div]
  exact sum_congr rfl fun x _ => ENNReal.toReal_ofReal (div_nonneg (hw x.val) pos.le)

/-- The probability law used for one actual request under both conditions of
Lemma 8, supported on admissible walks whose every transition has positive weight. -/
theorem admissible_walk_law {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y) (row : ∀ x, ∑ y, K x y = 1)
    (col : ∀ y, ∑ x, K x y = 1) {σ ρ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (hρ : 0 ≤ ρ)
    (op : ∀ f : V → ℝ, ∑ x, f x = 0 → ∑ y, (advance K f y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    (bad : Finset V) (forward : ∀ u, ∑ v ∈ bad, K u v ≤ ρ)
    (backward : ∀ v, ∑ u ∈ bad, K u v ≤ ρ)
    (h : ℕ) (hh : 0 < h) (mix : σ^h ≤ 1/(2*(Fintype.card V : ℝ)))
    (budget : 3*(2*h : ℕ)*ρ ≤ 1/2) (x y : V) :
    let A := (univ : Finset (Fin (2*h) → V)).filter (fun f => ∀ j, f j ∉ bad)
    let w (f : Fin (2*h) → V) := pathWeight K x (List.ofFn f) y
    let good := A.filter (fun f => 0 < w f)
    ∃ p : PMF good, (1/(2*(Fintype.card V : ℝ)))/2 ≤ ∑ f ∈ A, w f ∧
      ∀ S : Finset good, (∑ f ∈ S,(p f).toReal) = (∑ f ∈ S, w f.val)/(∑ f ∈ A, w f) := by
  intro A w good
  have low := (long_segment_bounds K row col hσ hσ' op (n := 2*h+1) (by omega) mix x y).1
  have keep := admissible_endpoint_mass K hn row col hσ hσ' hρ op bad forward backward h hh mix budget x y
  have H : (1/(2*(Fintype.card V : ℝ)))/2 ≤ ∑ f ∈ A, w f := (by linarith : _ ≤ (K^(2*h+1)) x y/2) |>.trans keep
  obtain ⟨p,P⟩ := restricted_law A w (fun f => pathWeight_nonneg K hn x y _) ((by positivity : 0 < (1/(2*(Fintype.card V : ℝ)))/2).trans_le H)
  exact ⟨p,H,P⟩
end WeightedPaper.Repair
