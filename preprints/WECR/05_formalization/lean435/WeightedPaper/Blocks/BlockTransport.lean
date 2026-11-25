import WeightedPaper.Cut.PairDegreeHall
import GaleHoffmanLib.Feasibility

namespace WeightedPaper.Blocks

open Finset
open scoped Classical

variable {X J Y : Type*} [Fintype X] [Fintype J] [Fintype Y]

private abbrev Node (X J Y : Type*) := X ⊕ (J ⊕ Y)
private abbrev exA (x : X) : Node X J Y := .inl x
private abbrev blk (j : J) : Node X J Y := .inr (.inl j)
private abbrev exB (y : Y) : Node X J Y := .inr (.inr y)

private noncomputable def arc (eA : X → J → Prop) (eB : Y → J → Prop) :
    Node X J Y → Node X J Y → ℤ
  | .inl x, .inr (.inl j) => if eA x j then 1 else 0
  | .inr (.inl j), .inr (.inr y) => if eB y j then 1 else 0
  | _, _ => 0

private def demand (delta : J → ℤ) : Node X J Y → ℤ
  | .inl _ => -1
  | .inr (.inl j) => -delta j
  | .inr (.inr _) => 1

omit [Fintype X] [Fintype J] [Fintype Y] in
private theorem arc_nonneg (eA : X → J → Prop) (eB : Y → J → Prop) (u v : Node X J Y) :
    0 ≤ arc eA eB u v := by
  classical
  rcases u with (x|j|y) <;> rcases v with (x'|j'|y') <;> simp [arc] <;> split <;> omega

/-- The cut inequalities for routing the free exceptional vertices. -/
def TransportCuts (eA : X → J → Prop) (eB : Y → J → Prop) (delta : J → ℤ) : Prop :=
  ∀ S : Finset J, (∑ j ∈ S, delta j) ≤
    ((univ.filter fun y => ∃ j ∈ S, eB y j).card : ℤ) -
    ((univ.filter fun x => ∀ j, eA x j → j ∈ S).card : ℤ)

private theorem sum_as_indicator {V : Type*} [Fintype V] (S : Finset V) (f : V → ℤ) :
    (∑ x ∈ S, f x) = ∑ x, if x ∈ S then f x else 0 := by
  classical
  rw [← sum_filter]
  congr 1
  ext x
  simp

private theorem card_as_indicator {V : Type*} [Fintype V] (p : V → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℤ) = ∑ x, if p x then 1 else 0 := by
  rw [card_filter,Nat.cast_sum]
  apply sum_congr rfl
  intro x _
  split <;> rfl

private theorem ite_sum_int {V : Type*} [Fintype V] (p : Prop) [Decidable p] (f : V → ℤ) :
    (if p then ∑ x, f x else 0) = ∑ x, if p then f x else 0 := by
  split <;> simp [*]

private theorem forall_cut_of_transport (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (hδ : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X)
    (cuts : TransportCuts eA eB delta) :
    ∀ S : Finset (Node X J Y), (∑ n ∈ Sᶜ, demand delta n) ≤
      ∑ u ∈ S, ∑ v ∈ Sᶜ, arc eA eB u v := by
  classical
  intro S
  let J₀ := univ.filter (fun j : J => blk j ∈ S)
  have memJ (j : J) : j ∈ J₀ ↔ blk j ∈ S := by simp [J₀]
  have hΔ : (∑ j ∈ J₀, delta j) + ∑ j ∈ J₀ᶜ, delta j = ∑ j, delta j :=
    sum_add_sum_compl J₀ delta
  have hCut := cuts J₀
  simp only [card_as_indicator] at hCut
  have hDemand :
      (∑ n ∈ Sᶜ, demand delta n) =
       -(∑ x : X, if exA x ∈ S then 0 else 1) - (∑ j ∈ J₀ᶜ, delta j) +
          ∑ y : Y, if exB y ∈ S then 0 else 1 := by
    rw [sum_as_indicator Sᶜ, Fintype.sum_sum_type, Fintype.sum_sum_type, sum_as_indicator J₀ᶜ]
    simp only [demand, mem_compl, ite_not, neg_ite, neg_zero, ← sum_neg_distrib]
    have hJ : (∑ j, if blk j ∈ S then 0 else -delta j) =
        -(∑ j, if j ∈ J₀ then 0 else delta j) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j _
      by_cases hj : blk j ∈ S <;> simp [memJ,hj]
    rw [hJ]
    ring
  have hCap :
      (∑ u ∈ S, ∑ v ∈ Sᶜ, arc eA eB u v) =
        (∑ x : X, if exA x ∈ S then ∑ j : J, if blk j ∈ S ∨ ¬ eA x j then 0 else 1 else 0) +
        ∑ y : Y, if exB y ∈ S then 0 else
          ∑ j : J, if blk j ∈ S ∧ eB y j then 1 else 0 := by
    rw [sum_as_indicator S, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [sum_as_indicator Sᶜ, Fintype.sum_sum_type, mem_compl, ite_not, arc, ite_self,
      sum_const_zero,add_zero,zero_add]
    congr 1
    · apply sum_congr rfl
      intro x _
      by_cases hx : exA x ∈ S <;> simp only [hx, if_true, if_false]
      apply sum_congr rfl
      intro j _
      by_cases hj : blk j ∈ S <;> by_cases he : eA x j <;> simp [hj,he]
    · simp only [ite_sum_int]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      by_cases hy : exB y ∈ S
      · simp [hy]
      · simp only [hy,if_false]
        apply sum_congr rfl
        intro j _
        by_cases hj : blk j ∈ S <;> by_cases he : eB y j <;> simp [hj,he]
  -- Each exceptional node contributes either its demand or a unit arc
  -- across the cut. A block touching an eligible neighbor gives such an arc.
  have hA (x : X) :
      (1 : ℤ) - (if ∀ j, eA x j → j ∈ J₀ then 1 else 0) ≤
      (if exA x ∈ S then 0 else 1) +
      (if exA x ∈ S then ∑ j : J, if blk j ∈ S ∨ ¬ eA x j then 0 else 1 else 0) := by
    by_cases h : ∀ j, eA x j → j ∈ J₀
    · rw [if_pos h, sub_self]
      apply add_nonneg
      · split <;> omega
      · split
        · exact sum_nonneg (fun _ _ => by split <;> omega)
        · omega
    · simp only [not_forall] at h
      obtain ⟨j,he,hj⟩ := h
      have hnot : ¬ ∀ j', eA x j' → j' ∈ J₀ := fun a => hj (a j he)
      by_cases hx : exA x ∈ S
      · simp only [hnot,if_false,hx,if_true, sub_zero,zero_add]
        have hterm := single_le_sum (f := fun j => if blk j ∈ S ∨ ¬ eA x j then (0:ℤ) else 1)
          (fun j _ => by split <;> omega) (mem_univ j)
        simpa [((memJ j).not.mp hj),he] using hterm
      · simp [hnot,hx]
  have hB (y : Y) :
      (if ∃ j ∈ J₀, eB y j then (1 : ℤ) else 0) + (if exB y ∈ S then 0 else 1) - 1 ≤
      if exB y ∈ S then 0 else ∑ j : J, if blk j ∈ S ∧ eB y j then 1 else 0 := by
    by_cases hy : exB y ∈ S
    · simp only [hy,if_true, add_zero, sub_nonpos]
      split <;> omega
    · by_cases h : ∃ j ∈ J₀, eB y j
      · obtain ⟨j,hj,he⟩ := h
        simp only [hy,if_false,if_pos (show ∃ j ∈ J₀, eB y j from ⟨j,hj,he⟩),add_sub_cancel_right]
        have hterm := single_le_sum (f := fun j => if blk j ∈ S ∧ eB y j then (1:ℤ) else 0)
          (fun j _ => by split <;> omega) (mem_univ j)
        simpa [(memJ j).mp hj,he] using hterm
      · rw [if_neg hy, if_neg h, if_neg hy, zero_add,sub_self]
        exact sum_nonneg (fun _ _ => by split <;> omega)
  have ha := sum_le_sum (s := (univ : Finset X)) (fun x _ => hA x)
  have hb := sum_le_sum (s := (univ : Finset Y)) (fun y _ => hB y)
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one] at ha hb
  rw [hDemand,hCap]
  omega

private theorem pick_one {V : Type*} [Fintype V] (f : V → ℤ)
    (h0 : ∀ v, 0 ≤ f v) (h1 : ∀ v, f v ≤ 1) (ht : ∑ v, f v = 1) :
    ∃ v, f v = 1 ∧ ∀ w, f w = if v = w then 1 else 0 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, f v = 1 := by
    by_contra! h
    have hz : ∀ v, f v = 0 := fun v => by have := h v; have := h0 v; have := h1 v; omega
    simp [hz] at ht
  refine ⟨v,hv,fun w => ?_⟩
  by_cases h : v = w
  · subst w
    simp [hv]
  · rw [if_neg h]
    have hs : f w + f v ≤ ∑ a, f a :=
      (show f w + f v = ∑ a ∈ ({w,v} : Finset V), f a by simp [Ne.symm h]) ▸
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => h0 a)
    have := h0 w
    omega

set_option maxHeartbeats 900000 in
/-- The integral quotient flow assigns each free exceptional vertex to
one eligible block with exactly the prescribed difference of counts. -/
theorem assign_of_transport_cuts (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (hδ : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X)
    (cuts : TransportCuts eA eB delta) :
    ∃ a : X → J, ∃ b : Y → J, (∀ x, eA x (a x)) ∧ (∀ y, eB y (b y)) ∧
      ∀ j, ((univ.filter fun y => b y = j).card : ℤ) -
        ((univ.filter fun x => a x = j).card : ℤ) = delta j := by
  classical
  obtain ⟨f,hskew,hcap,hd⟩ := (GaleFlows.feasibility_int (arc eA eB) (arc_nonneg eA eB)
    (demand delta)).mpr (forall_cut_of_transport eA eB delta hδ cuts)
  have hnet : ∑ u, ∑ v, f v u = 0 := by
    have hz : ∑ u, ∑ v, (f v u + f u v) = 0 := by simp [hskew]
    simp only [sum_add_distrib] at hz
    nth_rw 2 [sum_comm] at hz
    omega
  have hdtotal : ∑ u : Node X J Y, demand delta u = 0 := by
    simp only [Fintype.sum_sum_type,demand,sum_neg_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one]
    omega
  have hdegree (n) : (∑ v, f v n) = demand delta n := by
    by_contra! h
    have hlt : demand delta n < ∑ v, f v n := lt_of_le_of_ne (hd n) (Ne.symm h)
    have hsum := sum_lt_sum (fun u _ => hd u) ⟨n,mem_univ n,hlt⟩
    rw [hnet,hdtotal] at hsum
    omega
  have hzero (u v) (h₁ : arc eA eB u v = 0) (h₂ : arc eA eB v u = 0) : f u v = 0 := by
    have hu := hcap u v
    have hv := hcap v u
    rw [h₁] at hu
    rw [h₂] at hv
    have hs := hskew u v
    omega
  have hrev (u v) : f v u = -f u v := by have := hskew u v; omega
  let fa (x : X) (j : J) := f (exA x) (blk j)
  let fb (y : Y) (j : J) := f (blk j) (exB y)
  have ha0 (x j) : 0 ≤ fa x j := by
    have h := hcap (blk j) (exA x)
    change _ ≤ 0 at h
    rw [hrev] at h
    exact neg_nonpos.mp h
  have hb0 (y j) : 0 ≤ fb y j := by
    have h := hcap (exB y) (blk j)
    change _ ≤ 0 at h
    rw [hrev] at h
    exact neg_nonpos.mp h
  have ha1 (x j) : fa x j ≤ 1 := (hcap (exA x) (blk j)).trans (by change (if eA x j then 1 else 0) ≤ _; split <;> omega)
  have hb1 (y j) : fb y j ≤ 1 := (hcap (blk j) (exB y)).trans (by change (if eB y j then 1 else 0) ≤ _; split <;> omega)
  have hxa (x) : ∑ j, fa x j = 1 := by
    have h := hdegree (exA x)
    simp only [Fintype.sum_sum_type,demand] at h
    simp only [show ∀ x', f (exA x') (exA x) = 0 from fun _ => hzero _ _ rfl rfl,
      show ∀ y, f (exB y) (exA x) = 0 from fun _ => hzero _ _ rfl rfl, sum_const_zero,
      zero_add,add_zero,show ∀ j, f (blk j) (exA x) = -fa x j from fun _ => hrev _ _,
      sum_neg_distrib] at h
    omega
  have hyb (y) : ∑ j, fb y j = 1 := by
    have h := hdegree (exB y)
    simp only [Fintype.sum_sum_type,demand,
      show ∀ x, f (exA x) (exB y) = 0 from fun _ => hzero _ _ rfl rfl,
      show ∀ y', f (exB y') (exB y) = 0 from fun _ => hzero _ _ rfl rfl,
      sum_const_zero, zero_add,add_zero] at h
    exact h
  choose a ha haeq using fun x => pick_one (fa x) (ha0 x) (ha1 x) (hxa x)
  choose b hb hbeq using fun y => pick_one (fb y) (hb0 y) (hb1 y) (hyb y)
  refine ⟨a,b,?_,?_,?_⟩
  · intro x
    have hh := hcap (exA x) (blk (a x))
    change fa x (a x) ≤ if eA x (a x) then 1 else 0 at hh
    rw [ha] at hh
    by_contra hn
    simp [hn] at hh
  · intro y
    have hh := hcap (blk (b y)) (exB y)
    change fb y (b y) ≤ if eB y (b y) then 1 else 0 at hh
    rw [hb] at hh
    by_contra hn
    simp [hn] at hh
  · intro j
    have h := hdegree (blk j)
    simp only [Fintype.sum_sum_type,demand,
      show ∀ j', f (blk j') (blk j) = 0 from fun _ => hzero _ _ rfl rfl, sum_const_zero,zero_add,
      show ∀ y, f (exB y) (blk j) = -fb y j from fun _ => hrev _ _,sum_neg_distrib] at h
    rw [show (∑ x, f (exA x) (blk j)) = ∑ x, fa x j by rfl] at h
    simp only [haeq,hbeq] at h
    rw [card_as_indicator,card_as_indicator]
    omega

omit [Fintype J] in
private theorem count_in_blocks {V : Type*} [Fintype V] (a : V → J) (S : Finset J) :
    (∑ j ∈ S, ((univ.filter fun x => a x = j).card : ℤ)) =
      ((univ.filter fun x => a x ∈ S).card : ℤ) := by
  classical
  let U := univ.filter fun x => a x ∈ S
  have h := Finset.card_eq_sum_card_fiberwise (s := U) (t := S) (f := a)
    (fun x hx => (mem_filter.mp hx).2)
  rw [h,Nat.cast_sum]
  apply sum_congr rfl
  intro j hj
  have hEq : (univ.filter fun x => a x = j) = U.filter (fun x => a x = j) := by
    ext x
    simp only [U,mem_filter,mem_univ,true_and]
    exact ⟨fun hx => ⟨by simpa [hx] using hj,hx⟩,fun hx => hx.2⟩
  rw [hEq]

/-- Any eligible assignment with the prescribed differences satisfies the cuts. -/
theorem transport_cuts_of_assignment (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (a : X → J) (b : Y → J)
    (ha : ∀ x, eA x (a x)) (hb : ∀ y, eB y (b y))
    (hd : ∀ j, ((univ.filter fun y => b y = j).card : ℤ) -
      ((univ.filter fun x => a x = j).card : ℤ) = delta j) :
    TransportCuts eA eB delta := by
  classical
  intro S
  have hsum : (∑ j ∈ S, delta j) = ((univ.filter fun y => b y ∈ S).card : ℤ) -
      ((univ.filter fun x => a x ∈ S).card : ℤ) := by
    simp only [← hd,sum_sub_distrib,count_in_blocks]
  have hA : (univ.filter fun x => ∀ j, eA x j → j ∈ S).card ≤
      (univ.filter fun x => a x ∈ S).card :=
    card_le_card (fun x hx => mem_filter.mpr ⟨mem_univ x,(mem_filter.mp hx).2 _ (ha x)⟩)
  have hB : (univ.filter fun y => b y ∈ S).card ≤
      (univ.filter fun y => ∃ j ∈ S, eB y j).card :=
    card_le_card (fun y hy => mem_filter.mpr ⟨mem_univ y,b y,(mem_filter.mp hy).2,hb y⟩)
  rw [hsum]
  omega

theorem transport_cuts_iff_assignment (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (hδ : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X) :
    TransportCuts eA eB delta ↔
      ∃ a : X → J, ∃ b : Y → J, (∀ x, eA x (a x)) ∧ (∀ y, eB y (b y)) ∧
        ∀ j, ((univ.filter fun y => b y = j).card : ℤ) -
          ((univ.filter fun x => a x = j).card : ℤ) = delta j := by
  constructor
  · exact assign_of_transport_cuts eA eB delta hδ
  · rintro ⟨a,b,ha,hb,hd⟩
    exact transport_cuts_of_assignment eA eB delta a b ha hb hd

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.transport_cuts_iff_assignment
