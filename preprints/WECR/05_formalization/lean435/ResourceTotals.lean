import EdgeMarginals

namespace WeightedPaper.Repair
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V] {Q : Type*} [Fintype Q]

/-- Summed occupancy of a reserve edge in one color at an interior
position. Either side of the specified step can supply the long segment. -/
theorem interior_edge_use (K : Matrix V V ℝ) (hn : ∀ u v, 0 ≤ K u v)
    (row : ∀ u, ∑ v, K u v = 1) (col : ∀ v, ∑ u, K u v = 1)
    (start stop : Q → V) (a b : ℕ) (u v : V) (c d ρ : ℝ) (hc : 0 < c) (hd : 0 < d)
    (edge : K u v ≤ 1/d) (first : ∀ v, ∑ q, K (start q) v ≤ ρ)
    (last : ∀ u, ∑ q, K u (stop q) ≤ ρ)
    (long : (∀ q, (K^(b+1)) v (stop q) ≤ 3*c) ∨ (∀ q, (K^(a+1)) (start q) u ≤ 3*c))
    (keep hit : Q → ℝ) (accepted : ∀ q, c/2 ≤ keep q)
    (submass : ∀ q, hit q ≤ stepMass K (a+1) (b+1) (start q) u v (stop q)) :
    ∑ q, hit q / keep q ≤ 6*ρ/d := by
  rcases long with fw | bw
  · exact summed_step_use K hn start stop _ _ u v c d ρ hc hd fw
      (requests_spread start K hn col ρ first a u) edge keep hit accepted submass
  · apply summed_step_use K.transpose (fun x y => hn y x) stop start (b+1) (a+1) v u c d ρ hc hd
    · simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using bw
    · exact requests_spread stop K.transpose (fun x y => hn y x) row ρ last b v
    · exact edge
    · exact accepted
    · simpa only [stepMass_reverse] using submass

theorem interior_matched_use (K : Matrix V V ℝ) (hn : ∀ u v, 0 ≤ K u v)
    (row : ∀ u, ∑ v, K u v = 1) (col : ∀ v, ∑ u, K u v = 1)
    (start stop : Q → V) (a b : ℕ) (z : V) (c ρ : ℝ) (hc : 0 < c)
    (first : ∀ v, ∑ q, K (start q) v ≤ ρ) (last : ∀ u, ∑ q, K u (stop q) ≤ ρ)
    (long : (∀ q, (K^(b+1)) z (stop q) ≤ 3*c) ∨ (∀ q, (K^(a+1)) (start q) z ≤ 3*c))
    (keep hit : Q → ℝ) (accepted : ∀ q, c/2 ≤ keep q)
    (submass : ∀ q, hit q ≤ (K^(a+1)) (start q) z * (K^(b+1)) z (stop q)) :
    ∑ q, hit q / keep q ≤ 6*ρ := by
  rcases long with fw | bw
  · exact summed_matched_slot K hn start stop _ _ z c ρ hc fw
      (requests_spread start K hn col ρ first a z) keep hit accepted submass
  · apply summed_matched_slot K.transpose (fun x y => hn y x) stop start (b+1) (a+1) z c ρ hc
    · simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using bw
    · exact requests_spread stop K.transpose (fun x y => hn y x) row ρ last b z
    · exact accepted
    · simpa only [← Matrix.transpose_pow, Matrix.transpose_apply, mul_comm] using submass

/-- Sum the two end positions and every interior position across all colors.
Here m=ℓ-2, so the original matching has m+1 intermediate slots. -/
theorem palette_resource_totals {I : Type*} [Fintype I] (m : ℕ) (t d ρ : ℝ) (hd : 0 < d)
    (first last : ℝ) (middle : Fin m → I → ℝ) (matched : Fin (m+1) → ℝ)
    (hf : first ≤ 6*t/d) (hl : last ≤ 6*t/d) (hm : ∀ j i, middle j i ≤ 6*ρ/d)
    (ho : ∀ j, matched j ≤ 6*ρ) :
    first+last+(∑ j, ∑ i, middle j i) ≤ 6*(2*t+m*(Fintype.card I : ℝ)*ρ)/d ∧
    (∑ j, matched j) ≤ 6*(m+1)*ρ := by
  have H := sum_le_sum (s := (univ : Finset (Fin m))) fun j _ =>
    sum_le_sum (s := (univ : Finset I)) fun i _ => hm j i
  have O := sum_le_sum (s := (univ : Finset (Fin (m+1)))) fun j _ => ho j
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at H O
  constructor
  · calc
      _ ≤ 6*t/d+6*t/d+m*((Fintype.card I : ℝ)*(6*ρ/d)) := by linarith
      _ = _ := by ring
  · linarith
end WeightedPaper.Repair
