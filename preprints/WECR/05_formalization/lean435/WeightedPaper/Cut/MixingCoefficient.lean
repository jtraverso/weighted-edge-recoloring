import WeightedPaper.IntrinsicBalance

namespace WeightedPaper.Spectral
open Finset
open scoped Classical

private noncomputable def mark {A : Type*} (S : Finset A) (x : A) : ℝ := if x ∈ S then 1 else 0

private theorem mark_sum {A : Type*} (O S : Finset A) (h : S ⊆ O) (f : A → ℝ) :
    ∑ x ∈ O, mark S x * f x = ∑ x ∈ S,f x := by
  classical
  simp only [mark,ite_mul,one_mul,zero_mul,← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [mem_filter]
  exact ⟨And.right,fun hx => ⟨h hx,hx⟩⟩

private theorem between {A : Type*} (O S : Finset A) (h : S ⊆ O) (N : ℝ) (f : A → ℝ) :
    ∑ x ∈ O, (N*mark S x-S.card)*f x =
      N*(∑ x ∈ S,f x)-S.card*(∑ x ∈ O,f x) := by
  simp only [sub_mul,mul_assoc,sum_sub_distrib,← mul_sum,mark_sum O S h]

private theorem centered_data {A : Type*} (O S : Finset A) (h : S ⊆ O) (N : ℝ)
    (hn : (O.card:ℝ) = N) :
    (∑ x ∈ O,(N*mark S x-S.card))=0 ∧
    (∑ x ∈ O,(N*mark S x-S.card)^2)=N*S.card*(N-S.card) := by
  have hf := between O S h N (fun _ => 1)
  simp only [mul_one,sum_const,nsmul_eq_mul,hn] at hf
  have hz : (∑ x ∈ O,(N*mark S x-S.card))=0 := by linarith only [hf]
  refine ⟨hz,?_⟩
  simp_rw [pow_two]
  rw [between O S h N, hz]
  have hs : (∑ x ∈ S,(N*mark S x-S.card)) = S.card*(N-S.card) := by
    calc
      _ = ∑ _x ∈ S,(N-S.card) := sum_congr rfl (fun x hx => by simp [mark,hx])
      _ = _ := by simp [mul_sub]
  rw [hs]
  ring

/-- Exact centered-indicator mixing from a two-sided mean-zero operator
bound with independent coefficients for the spectral inequality. -/
theorem indicator_mixing_squared {A B : Type*} (O : Finset A) (P : Finset B)
    (N d K L : ℝ) (pos : 0 < N) (hO : (O.card:ℝ)=N) (hP : (P.card:ℝ)=N)
    (w : A → B → ℝ)
    (row : ∀ x ∈ O, ∑ y ∈ P,w x y = d)
    (col : ∀ y ∈ P, ∑ x ∈ O,w x y = d)
    (op : ∀ (u : A → ℝ) (v : B → ℝ), (∑ x ∈ O,u x)=0 → (∑ y ∈ P,v y)=0 →
      K*(∑ x ∈ O, u x*(∑ y ∈ P,v y*w x y))^2 ≤
        L*(∑ x ∈ O,(u x)^2)*(∑ y ∈ P,(v y)^2))
    (S : Finset A) (hS : S ⊆ O) (T : Finset B) (hT : T ⊆ P) :
    K*(N*(∑ x ∈ S, ∑ y ∈ T,w x y)-d*S.card*T.card)^2 ≤
      L*S.card*T.card*((N-S.card)*(N-T.card)) := by
  obtain ⟨hu,hu2⟩ := centered_data O S hS N hO
  obtain ⟨hv,hv2⟩ := centered_data P T hT N hP
  have hh := op _ _ hu hv
  rw [hu2,hv2,between O S hS N] at hh
  simp_rw [between P T hT N] at hh
  have rc (I : Finset A) (hi : I ⊆ O) : (∑ x ∈ I,∑ y ∈ P,w x y) = I.card*d := by
    calc
      _ = ∑ _x ∈ I,d := sum_congr rfl (fun x hx => row x (hi hx))
      _ = _ := by simp
  have cc : (∑ x ∈ O, ∑ y ∈ T,w x y) = T.card*d := by
    rw [sum_comm]
    calc
      _ = ∑ _y ∈ T,d := sum_congr rfl (fun y hy => col y (hT hy))
      _ = _ := by simp
  simp only [sum_sub_distrib,← mul_sum,rc S hS,rc O Subset.rfl,cc,hO] at hh
  apply le_of_mul_le_mul_left (a := N^2) _ (sq_pos_of_pos pos)
  nlinarith only [hh]

end WeightedPaper.Spectral

#print axioms WeightedPaper.Spectral.indicator_mixing_squared
