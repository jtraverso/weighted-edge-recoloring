import GridSpending

namespace WeightedPaper.Repair
open Finset
open scoped Classical

theorem crossing_degree_left {A B : Type*} [Fintype A] [Fintype B]
    (cap : A → B → ℕ) (x : A) :
    ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.1 = x)).card = ∑ y, cap x y := by
  classical
  let S := (univ : Finset (CrossingCopy cap)).filter fun e => e.1.1 = x
  let e : (Σ y, Fin (cap x y)) ≃ ↥S := by
    apply Equiv.ofBijective (fun p => ⟨⟨(x,p.1),p.2⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)
    constructor
    · rintro ⟨y,i⟩ ⟨z,j⟩ he
      have h := congrArg (fun a : S => a.val) he
      have key : (x,y) = (x,z) := congrArg Sigma.fst h
      have yz : y = z := congrArg Prod.snd key
      subst z
      cases h
      rfl
    · rintro ⟨⟨⟨a,b⟩,i⟩,hi⟩
      have hx : a = x := (mem_filter.mp hi).2
      subst a
      exact ⟨⟨b,i⟩,rfl⟩
  have h := Fintype.card_congr e
  simpa only [Fintype.card_coe,Fintype.card_sigma,Fintype.card_fin] using h.symm

theorem crossing_degree_right {A B : Type*} [Fintype A] [Fintype B]
    (cap : A → B → ℕ) (y : B) :
    ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.2 = y)).card = ∑ x, cap x y := by
  classical
  let S := (univ : Finset (CrossingCopy cap)).filter fun e => e.1.2 = y
  let e : (Σ x, Fin (cap x y)) ≃ ↥S := by
    apply Equiv.ofBijective (fun p => ⟨⟨(p.1,y),p.2⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)
    constructor
    · rintro ⟨x,i⟩ ⟨z,j⟩ he
      have h := congrArg (fun a : S => a.val) he
      have key : (x,y) = (z,y) := congrArg Sigma.fst h
      have xz : x = z := congrArg Prod.fst key
      subst z
      cases h
      rfl
    · rintro ⟨⟨⟨a,b⟩,i⟩,hi⟩
      have hy : b = y := (mem_filter.mp hi).2
      subst b
      exact ⟨⟨a,i⟩,rfl⟩
  have h := Fintype.card_congr e
  simpa only [Fintype.card_coe,Fintype.card_sigma,Fintype.card_fin] using h.symm

namespace Grid
variable {H W : Type} [Fintype H] [Fintype W]

def endpoint (k : Fin 2) (e : Fin d × Bool) : Side H W ⊕ Side H W :=
  if e.2 then .inl (leftInternal k) else .inr (rightInternal k)

theorem internal_seed_count (d : ℕ) (i : Fin d) (x : Side H W) :
    (univ.filter (fun e : Fin d × Bool => e.1 = i ∧
      (endpoint 0 e = .inl x ∨ endpoint 1 e = .inl x))).card =
      if x ∈ Set.range (leftInternal : Fin 2 → Side H W) then 1 else 0 := by
  classical
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,endpoint,Bool.false_eq_true,ite_false,ite_true,reduceCtorEq,false_or]
  simp only [and_false,ite_false,add_zero]
  have eq : (Sum.inl (leftInternal 0) = (Sum.inl x : Side H W ⊕ Side H W) ∨
      Sum.inl (leftInternal 1) = (Sum.inl x : Side H W ⊕ Side H W)) ↔
      x ∈ Set.range (leftInternal : Fin 2 → Side H W) := by
    simp only [Sum.inl.injEq,Set.mem_range,Fin.exists_fin_two]
  simp only [eq]
  by_cases hx : x ∈ Set.range (leftInternal : Fin 2 → Side H W) <;> simp [hx]

theorem internal_seed_count' (d : ℕ) (i : Fin d) (y : Side H W) :
    (univ.filter (fun e : Fin d × Bool => e.1 = i ∧
      (endpoint 0 e = .inr y ∨ endpoint 1 e = .inr y))).card =
      if y ∈ Set.range (rightInternal : Fin 2 → Side H W) then 1 else 0 := by
  classical
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,endpoint,Bool.false_eq_true,ite_false,ite_true,reduceCtorEq,or_false]
  have eq : (Sum.inr (rightInternal 0) = (Sum.inr y : Side H W ⊕ Side H W) ∨
      Sum.inr (rightInternal 1) = (Sum.inr y : Side H W ⊕ Side H W)) ↔
      y ∈ Set.range (rightInternal : Fin 2 → Side H W) := by
    simp only [Sum.inr.injEq,Set.mem_range,Fin.exists_fin_two]
  simp only [eq,and_false,ite_false,add_zero]
  by_cases hy : y ∈ Set.range (rightInternal : Fin 2 → Side H W) <;> simp [hy]

private theorem internal_degree (d : ℕ) (P : Fin d × Bool → Prop) [DecidablePred P]
    (k : ℕ) (one : ∀ i : Fin d, (univ.filter (fun e : Fin d × Bool => e.1 = i ∧ P e)).card = k) :
    (univ.filter P).card = d*k := by
  have eq := sum_card_fiberwise_eq_card_filter (univ.filter P) (univ : Finset (Fin d)) Prod.fst
  simp only [mem_univ,filter_true,filter_filter,and_comm (a := P _)] at eq
  simpa [one] using eq.symm

theorem grid_degrees (R : Ordinary H W → Ordinary H W → Prop) (d : ℕ)
    (regA : ∀ x, (univ.filter (R x)).card = d)
    (regB : ∀ y, (univ.filter (fun x => R x y)).card = d) :
    (∀ x : Side H W, (univ.filter (fun e : Fin d × Bool => endpoint 0 e = .inl x ∨ endpoint 1 e = .inl x)).card +
      ((univ : Finset (CrossingCopy (capacity R d))).filter (fun e => e.1.1 = x)).card = 3*d) ∧
    (∀ y : Side H W, (univ.filter (fun e : Fin d × Bool => endpoint 0 e = .inr y ∨ endpoint 1 e = .inr y)).card +
      ((univ : Finset (CrossingCopy (capacity R d))).filter (fun e => e.1.2 = y)).card = 3*d) := by
  classical
  have left (x : Ordinary H W) : (∑ y : Side H W, if ordinary R (.inl x) y then 2 else 0) = 2*d := by
    rw [Fintype.sum_sum_type]
    have count : (∑ z : Ordinary H W, if R x z then 2 else 0) = 2*d := by
      rw [← sum_filter, sum_const, regA]
      simp [mul_comm]
    exact (congrArg₂ (· + ·) count (by simp [ordinary])).trans (Nat.add_zero _)
  have right (y : Ordinary H W) : (∑ x : Side H W, if ordinary R x (.inl y) then 2 else 0) = 2*d := by
    rw [Fintype.sum_sum_type]
    have count : (∑ z : Ordinary H W, if R z y then 2 else 0) = 2*d := by
      rw [← sum_filter, sum_const, regB]
      simp [mul_comm]
    exact (congrArg₂ (· + ·) count (by simp [ordinary])).trans (Nat.add_zero _)
  constructor
  · intro x
    have eq := crossing_degree_left (capacity R d) x
    rw [show (∑ y, capacity R d x y) = (∑ y, if static x y then d else 0) + ∑ y, if ordinary R x y then 2 else 0 from sum_add_distrib] at eq
    convert_to _ + ((∑ y, if static x y then d else 0) + ∑ y, if ordinary R x y then 2 else 0) = 3*d using 2
    · convert eq using 2 <;> congr 1 <;> ext <;> simp
    clear eq
    rw [internal_degree d _ _ (fun i => internal_seed_count d i x)]
    rcases x with (k | (k | (⟨h,t⟩ | w))) | h
    all_goals try rw [left]
    all_goals simp [Side,Ordinary,Fintype.sum_sum_type,Fintype.sum_prod_type,static,ordinary,leftInternal,eq_comm]
    all_goals (try simp only [sum_add_distrib])
    all_goals try rw [sum_ite_eq]
    all_goals try rw [sum_ite_eq']
    all_goals (try simp only [mem_univ,ite_true])
    all_goals try rw [sum_ite_eq]
    all_goals (try simp only [mem_univ,ite_true])
    all_goals (try fin_cases k) <;> (try simp)
    all_goals omega
  · intro y
    have eq := crossing_degree_right (capacity R d) y
    rw [show (∑ x, capacity R d x y) = (∑ x, if static x y then d else 0) + ∑ x, if ordinary R x y then 2 else 0 from sum_add_distrib] at eq
    convert_to _ + ((∑ x, if static x y then d else 0) + ∑ x, if ordinary R x y then 2 else 0) = 3*d using 2
    · convert eq using 2 <;> congr 1 <;> ext <;> simp
    clear eq
    rw [internal_degree d _ _ (fun i => internal_seed_count' d i y)]
    rcases y with (k | (k | (⟨h,t⟩ | w))) | h
    all_goals try rw [right]
    all_goals simp [Side,Ordinary,Fintype.sum_sum_type,Fintype.sum_prod_type,static,ordinary,rightInternal,eq_comm]
    all_goals (try simp only [sum_add_distrib])
    all_goals try rw [sum_ite_eq]
    all_goals try rw [sum_ite_eq']
    all_goals (try simp only [mem_univ,ite_true])
    all_goals try rw [sum_ite_eq]
    all_goals (try simp only [mem_univ,ite_true])
    all_goals (try fin_cases k) <;> (try simp)
    all_goals omega

end Grid
end WeightedPaper.Repair
