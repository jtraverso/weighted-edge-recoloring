module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section


/-! The right side of a block is indexed by its left side through the
color's matching permutation. A forward step has kernel K x z = P x (π z).
Reversing a step uses its transpose. -/
namespace WeightedPaper.Repair

open Finset Matrix
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathWeight (K : Matrix V V ℝ) (x : V) : List V → V → ℝ
  | [], y => K x y
  | z :: zs, y => K x z * pathWeight K z zs y

private theorem pathWeight_append (K : Matrix V V ℝ) (x : V) (zs : List V) (u y : V) :
    pathWeight K x (zs ++ [u]) y = pathWeight K x zs u * K u y := by
  induction zs generalizing x with
  | nil => rfl
  | cons z zs ih => simp [pathWeight, ih, mul_assoc]

theorem pathWeight_reverse (K : Matrix V V ℝ) (x y : V) (zs : List V) :
    pathWeight K.transpose y zs.reverse x = pathWeight K x zs y := by
  induction zs generalizing x with
  | nil => rfl
  | cons z zs ih =>
    rw [List.reverse_cons, pathWeight_append, ih, pathWeight, transpose_apply, mul_comm]

/-- Exact likelihood of a specified path, normalized by the mass of its
terminal vertex. The intermediate list has one fewer entry than the number of steps. -/
noncomputable def bridgeWeight (K : Matrix V V ℝ) (x : V) (zs : List V) (y : V) : ℝ :=
  pathWeight K x zs y / (K ^ (zs.length + 1)) x y

theorem bridgeWeight_reverse (K : Matrix V V ℝ) (x y : V) (zs : List V) :
    bridgeWeight K.transpose y zs.reverse x = bridgeWeight K x zs y := by
  simp [bridgeWeight, pathWeight_reverse, ← Matrix.transpose_pow]

/-- Summing over all intermediate vertices gives the normalizing kernel entry. -/
theorem pathWeight_total (K : Matrix V V ℝ) (x y : V) (n : ℕ) :
    (∑ f : Fin n → V, pathWeight K x (List.ofFn f) y) = (K ^ (n+1)) x y := by
  induction n generalizing x with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => V)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, pathWeight]
    simp_rw [← Finset.mul_sum, ih]
    rw [pow_succ' K (n+1), Matrix.mul_apply]

noncomputable def advance (K : Matrix V V ℝ) (f : V → ℝ) (y : V) := ∑ x, f x * K x y

theorem advance_sum (K : Matrix V V ℝ) (row : ∀ x, ∑ y, K x y = 1) (f : V → ℝ) :
    ∑ y, advance K f y = ∑ x, f x := by
  simp only [advance]
  rw [sum_comm]
  simp_rw [← mul_sum, row, mul_one]

theorem advance_bound (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (col : ∀ y, ∑ x, K x y = 1) {f : V → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) (y : V) :
    advance K f y ≤ c := by
  calc
    _ ≤ ∑ x, c * K x y := sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hf x) (hn x y)
    _ = c := by rw [← mul_sum, col, mul_one]

/-- Entrywise mixing for any doubly stochastic kernel with the given
mean-zero squared norm bound. This includes any permutation of the columns. -/
theorem power_entry_mixing [Nonempty V] (K : Matrix V V ℝ)
    (row : ∀ x, ∑ y, K x y = 1) (col : ∀ y, ∑ x, K x y = 1)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (contract : ∀ f : V → ℝ, ∑ x, f x = 0 →
      ∑ y, (advance K f y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    (n : ℕ) (x y : V) :
    |(K^n) x y - 1 / (Fintype.card V : ℝ)| ≤ σ^n := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by unfold N; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  let f (m : ℕ) (z : V) := (K^m) x z - 1/N
  have step (m : ℕ) : f (m+1) = advance K (f m) := by
    funext z
    simp only [f, pow_succ, Matrix.mul_apply, advance, sub_mul, sum_sub_distrib,
      ← mul_sum, col, mul_one]
  have mass (m : ℕ) : ∑ z, f m z = 0 := by
    induction m with
    | zero =>
      simp [f, Matrix.one_apply, sum_sub_distrib, N, Fintype.card_ne_zero]
    | succ m ih => rwa [step, advance_sum K row]
  have initial : (∑ z, (f 0 z)^2) ≤ 1 := by
    have expand (z : V) : (f 0 z)^2 =
        (if x = z then 1-2/N else 0) + (1/N)^2 := by
      by_cases hz : x = z <;> simp [f, Matrix.one_apply, hz] <;> ring
    simp_rw [expand, sum_add_distrib]
    simp only [sum_ite_eq, mem_univ, if_true, sum_const, card_univ, nsmul_eq_mul]
    change 1 - 2/N + N*(1/N)^2 ≤ 1
    field_simp
    nlinarith
  have energy (m : ℕ) : ∑ z, (f m z)^2 ≤ (σ^m)^2 := by
    induction m with
    | zero => simpa using initial
    | succ m ih =>
      rw [step]
      calc
        _ ≤ σ^2 * ∑ z, (f m z)^2 := contract _ (mass m)
        _ ≤ σ^2 * (σ^m)^2 := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
        _ = _ := by rw [pow_succ]; ring
  have one := single_le_sum (f := fun z => (f n z)^2) (fun z _ => sq_nonneg _) (mem_univ y)
  exact (sq_le_sq.mp (one.trans (energy n))).trans_eq (abs_of_nonneg (pow_nonneg hσ _))


/-- A color-specific completion of the matching to a bijection merely
reindexes the output vector. It preserves the squared contraction bound. -/
theorem permuted_contraction {B : Type*} [Fintype B] (π : V ≃ B)
    (P : Matrix V B ℝ) (σ : ℝ)
    (op : ∀ f : V → ℝ, ∑ x, f x = 0 →
      ∑ y, (∑ x, f x * P x y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    (f : V → ℝ) (hf : ∑ x, f x = 0) :
    ∑ y, (advance (fun x z => P x (π z)) f y)^2 ≤ σ^2 * ∑ x, (f x)^2 := by
  change (∑ y, (fun z => (∑ x, f x * P x z)^2) (π y)) ≤ _
  exact (π.sum_comp (fun z : B => (∑ x, f x * P x z)^2)).le.trans (op f hf)

theorem long_segment_bounds [Nonempty V] (K : Matrix V V ℝ)
    (row : ∀ x, ∑ y, K x y = 1) (col : ∀ y, ∑ x, K x y = 1)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (op : ∀ f : V → ℝ, ∑ x, f x = 0 →
      ∑ y, (advance K f y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    {h n : ℕ} (long : h ≤ n) (mix : σ^h ≤ 1 / (2 * (Fintype.card V : ℝ))) (x y : V) :
    1 / (2 * (Fintype.card V : ℝ)) ≤ (K^n) x y ∧
    (K^n) x y ≤ 3 / (2 * (Fintype.card V : ℝ)) := by
  have hm := (power_entry_mixing K row col σ hσ op n x y).trans
    ((pow_le_pow_of_le_one hσ hσ' long).trans mix)
  have hh := abs_le.mp hm
  rw [show 3 / (2 * (Fintype.card V : ℝ)) = 3 * (1 / (2 * (Fintype.card V : ℝ))) by ring]
  constructor <;> linarith [hh.1, hh.2, show 1 / (Fintype.card V : ℝ) =
    2 * (1 / (2 * (Fintype.card V : ℝ))) by ring]

end WeightedPaper.Repair
