import WeightedPaper.Examples.HostBudget

namespace WeightedPaper.Examples

open Finset
open scoped Classical

abbrev Quad (A : Type*) := Bool × Bool × A

def quadInternal {A : Type*} [DecidableEq A] (a b : Quad A) : ℕ :=
  if a.1 ≠ b.1 ∧ a.2.2 = b.2.2 then 1 else 0

theorem quadInternal_symm {A : Type*} [DecidableEq A] (a b : Quad A) :
    quadInternal a b = quadInternal b a := by
  unfold quadInternal
  exact if_congr (and_congr (not_congr eq_comm) eq_comm) rfl rfl

theorem quadInternal_zero {A : Type*} [DecidableEq A] (a b : Quad A) (h : a.1 = b.1) :
    quadInternal a b = 0 := by simp [quadInternal,h]

theorem quadInternal_degree {A : Type*} [Fintype A] [DecidableEq A] (a : Quad A) :
    (∑ b, quadInternal a b) = 2 := by
  rcases a with ⟨c,a,x⟩
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,quadInternal,Prod.fst,Prod.snd]
  cases c <;> simp

@[simp] theorem card_quad {A : Type*} [Fintype A] : Fintype.card (Quad A) = 4 * Fintype.card A := by
  simp [Fintype.card_prod,Nat.mul_assoc,← Nat.mul_assoc]

/-- Complete simple support with an independently specified extra
multiplicity on each diagonal pair across the cut. -/
def diagExtra {A : Type*} [DecidableEq A] (f : A → ℕ) (a b : A) : ℕ :=
  1 + if a = b then f a else 0

theorem diagExtra_symm {A : Type*} [DecidableEq A] (f : A → ℕ) (a b : A) :
    diagExtra f a b = diagExtra f b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp [diagExtra,h,Ne.symm h]

theorem diagExtra_degree {A : Type*} [Fintype A] [DecidableEq A] (f : A → ℕ) (a : A) :
    (∑ b, diagExtra f a b) = Fintype.card A + f a := by
  simp [diagExtra,sum_add_distrib]

theorem diagExtra_neighbours {A : Type*} [Fintype A] [DecidableEq A] (f : A → ℕ) (a : A) :
    (univ.filter fun b => 0 < diagExtra f a b).card = Fintype.card A := by
  simp [diagExtra]

def basis {n : ℕ} (i : Fin n) (j : Fin n) : ℝ := if j=i then 1 else 0

theorem energy_basis {n : ℕ} (i : Fin n) : energy (basis i) = 1 := by
  simp [basis,energy,ite_pow]

theorem dot_basis {n : ℕ} (i : Fin n) (w : Fin n → ℝ) : dot (basis i) w = w i := by
  simp [basis,dot,ite_mul]

end WeightedPaper.Examples
