import GridLayout
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace WeightedPaper.Repair.Grid
open Filter Asymptotics
open scoped Topology

theorem ordinary_count {q b : ℕ} (m : Marked q ↪ CellVertex q b) :
    Fintype.card (Ordinary (Fin (Nat.sqrt q)) (Intact m)) = b*q^2 := by
  rw [Fintype.card_congr (coordinates m)]
  simp [CellVertex, pow_two, Nat.mul_left_comm, Nat.mul_comm]

private theorem ordinary_sqrt (b q : ℕ) : √((b:ℝ)*q^2) = √(b:ℝ)*q := by
  rw [Real.sqrt_mul (Nat.cast_nonneg b), Real.sqrt_sq (Nat.cast_nonneg q)]

private theorem ordinary_quarter_power (b q : ℕ) :
    ((b:ℝ)*q^2) ^ (1/4:ℝ) = √(√(b:ℝ)) * √(q:ℝ) := by
  have hn : (0:ℝ) ≤ b*q^2 := by positivity
  have h : ((b:ℝ)*q^2) ^ (1/4:ℝ) = √(√((b:ℝ)*q^2)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn]
    norm_num
  rw [h, ordinary_sqrt, Real.sqrt_mul (Real.sqrt_nonneg _)]

/-- Both orders of growth in the sparse grid corollary, with b fixed.
Restricting the filter to even q gives the same estimates. -/
theorem sparse_grid_growth (b : ℕ) (hb : 0 < b) :
    ((fun q : ℕ => (b*(2*(q:ℝ)-1) : ℝ)) =Θ[atTop]
      (fun q : ℕ => √((b:ℝ)*q^2))) ∧
    ((fun q : ℕ => (Nat.sqrt q : ℝ)) =Θ[atTop]
      (fun q : ℕ => ((b:ℝ)*q^2) ^ (1/4:ℝ))) := by
  have B : (1:ℝ) ≤ b := by exact_mod_cast hb
  have rootB : 1 ≤ √(b:ℝ) := by simpa using Real.sqrt_le_sqrt B
  have rootB2 : 1 ≤ √(√(b:ℝ)) := by simpa using Real.sqrt_le_sqrt rootB
  refine ⟨⟨IsBigO.of_bound (2*(b:ℝ)) ?_, IsBigO.of_bound (√(b:ℝ)) ?_⟩,
    ⟨IsBigO.of_bound 1 ?_, IsBigO.of_bound (2*√(√(b:ℝ))) ?_⟩⟩
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
    have Q : (1:ℝ) ≤ q := by exact_mod_cast hq
    have d : (0:ℝ) ≤ b*(2*q-1) := mul_nonneg (by positivity) (by linarith)
    simp only [Real.norm_eq_abs, abs_of_nonneg d, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [ordinary_sqrt]
    calc
      (b:ℝ)*(2*q-1) ≤ (2*(b:ℝ))*q := by nlinarith
      _ ≤ (2*(b:ℝ))*(√(b:ℝ)*q) := by gcongr; exact le_mul_of_one_le_left (by positivity) rootB
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
    have Q : (1:ℝ) ≤ q := by exact_mod_cast hq
    have qd : (q:ℝ) ≤ b*(2*q-1) := by
      calc
        (q:ℝ) ≤ 2*q-1 := by linarith
        _ ≤ b*(2*q-1) := le_mul_of_one_le_left (by linarith) B
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg ((Nat.cast_nonneg q).trans qd)]
    rw [ordinary_sqrt]
    exact mul_le_mul_of_nonneg_left qd (Real.sqrt_nonneg _)
  · filter_upwards with q
    have hs : (Nat.sqrt q : ℝ) ≤ √(q:ℝ) := by
      apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).2
      exact_mod_cast Nat.sqrt_le' q
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Nat.sqrt q)),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ b*q^2) _), one_mul]
    rw [ordinary_quarter_power]
    exact hs.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) rootB2)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
    have S : (1:ℝ) ≤ Nat.sqrt q := by exact_mod_cast Nat.sqrt_pos.mpr (by omega : 0 < q)
    have hs : √(q:ℝ) ≤ 2*Nat.sqrt q := by
      have hlt : (q:ℝ) < ((Nat.sqrt q : ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' q
      apply (Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩)
      exact hlt.le.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Nat.sqrt q)),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ b*q^2) _)]
    rw [ordinary_quarter_power]
    calc
      √(√(b:ℝ))*√(q:ℝ) ≤ √(√(b:ℝ))*(2*Nat.sqrt q) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = _ := by ring

end WeightedPaper.Repair.Grid
