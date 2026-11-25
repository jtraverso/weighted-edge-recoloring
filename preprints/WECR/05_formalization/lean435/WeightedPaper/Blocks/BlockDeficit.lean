import WeightedPaper.Blocks.BlockTransport

namespace WeightedPaper.Blocks

open Finset
open scoped Classical

variable {X Y J : Type*} [Fintype X] [Fintype Y] [Fintype J]

/-- Number of exceptional vertices assigned to a given block. -/
noncomputable def assignedCount {V : Type*} [Fintype V] (assign : V → J) (j : J) : ℕ :=
  (univ.filter fun x => assign x = j).card

theorem sum_assignedCount {V : Type*} [Fintype V] (assign : V → J) :
    ∑ j, assignedCount assign j = Fintype.card V := by
  classical
  unfold assignedCount
  simpa only [card_univ] using
    (card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset J))
      (f := assign) (fun _ _ => mem_univ _)).symm

/-- The signed number of unpaired left vertices in a block after assignment. -/
noncomputable def remainder (delta : J → ℤ) (a : X → J) (b : Y → J) (j : J) : ℤ :=
  delta j - ((assignedCount b j : ℤ) - assignedCount a j)

noncomputable def assignmentDeficit (delta : J → ℤ) (a : X → J) (b : Y → J) : ℕ :=
  ∑ j, (remainder delta a b j).toNat

/-- The failed inequality at a block cut, expressed as a signed integer. -/
noncomputable def cutGap (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (S : Finset J) : ℤ :=
  (∑ j ∈ S, delta j) -
    (((univ.filter fun y => ∃ j ∈ S, eB y j).card : ℤ) -
      ((univ.filter fun x => ∀ j, eA x j → j ∈ S).card : ℤ))

/-- The maximum positive violation of the quotient cut conditions. -/
noncomputable def transportDeficit (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) : ℕ :=
  (univ : Finset (Finset J)).sup fun S => (cutGap eA eB delta S).toNat

theorem cutGap_le_transportDeficit (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (S : Finset J) :
    cutGap eA eB delta S ≤ (transportDeficit eA eB delta : ℤ) := by
  have h : (cutGap eA eB delta S).toNat ≤ transportDeficit eA eB delta :=
    le_sup (f := fun S => (cutGap eA eB delta S).toNat) (mem_univ S)
  omega

theorem transportDeficit_eq_zero_iff (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) : transportDeficit eA eB delta = 0 ↔ TransportCuts eA eB delta := by
  constructor
  · intro h S
    have hg := cutGap_le_transportDeficit eA eB delta S
    rw [h] at hg
    unfold cutGap at hg
    omega
  · intro h
    apply Nat.le_zero.mp
    apply Finset.sup_le
    intro S _
    apply Int.toNat_le.mpr
    have hS := h S
    unfold cutGap
    omega

theorem transportDeficit_le_assignment (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (a : X → J) (b : Y → J)
    (ha : ∀ x, eA x (a x)) (hb : ∀ y, eB y (b y)) :
    transportDeficit eA eB delta ≤ assignmentDeficit delta a b := by
  classical
  apply Finset.sup_le
  intro S _
  let routed (j : J) : ℤ := (assignedCount b j : ℤ) - assignedCount a j
  have hc := transport_cuts_of_assignment eA eB routed a b ha hb (fun _ => rfl) S
  have sumR : (∑ j ∈ S, remainder delta a b j) = (∑ j ∈ S, delta j) - ∑ j ∈ S, routed j := by
    simp only [remainder, routed, sum_sub_distrib]
  have hSum : (∑ j ∈ S, remainder delta a b j) ≤ (assignmentDeficit delta a b : ℤ) := by
    calc
      _ ≤ ∑ j ∈ S, ((remainder delta a b j).toNat : ℤ) :=
        sum_le_sum (fun j _ => by omega)
      _ ≤ _ := by
        rw [assignmentDeficit,Nat.cast_sum]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => Int.natCast_nonneg _)
  have hGap : cutGap eA eB delta S ≤ (assignmentDeficit delta a b : ℤ) := by
    unfold cutGap
    omega
  exact Int.toNat_le.mpr hGap

theorem card_filter_congr {V : Type*} [Fintype V]
    (p q : V → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ x, p x ↔ q x) :
    (univ.filter p).card = (univ.filter q).card := by
  apply congrArg Finset.card
  ext x
  simp only [mem_filter,mem_univ,true_and]
  exact h x

theorem card_filter_sum {V W : Type*} [Fintype V] [Fintype W]
    (p : V → Prop) (q : W → Prop) [DecidablePred p] [DecidablePred q]
    [DecidablePred (Sum.elim p q)] :
    (univ.filter (Sum.elim p q)).card = (univ.filter p).card + (univ.filter q).card := by
  simp only [card_filter,Fintype.sum_sum_type]
  congr 1
  · apply sum_congr rfl
    intro v _
    by_cases h : p v <;> simp [h]
  · apply sum_congr rfl
    intro w _
    by_cases h : q w <;> simp [h]

private theorem cutGap_empty (eA : X → J → Prop) (eB : Y → J → Prop) (delta : J → ℤ)
    (ha : ∀ x, ∃ j, eA x j) : cutGap eA eB delta ∅ = 0 := by
  classical
  have hn : (univ.filter fun x => ∀ j, eA x j → j ∈ (∅ : Finset J)) = ∅ := by
    ext x
    obtain ⟨j,hj⟩ := ha x
    simp only [mem_filter,notMem_empty,mem_univ,true_and,iff_false]
    exact fun h => h j hj
  have hm : (univ.filter fun y => ∃ j ∈ (∅ : Finset J), eB y j) = ∅ := by simp
  unfold cutGap
  rw [hn,hm,sum_empty,card_empty]
  rfl

private theorem cutGap_univ (eA : X → J → Prop) (eB : Y → J → Prop) (delta : J → ℤ)
    (hb : ∀ y, ∃ j, eB y j)
    (ht : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X) :
    cutGap eA eB delta univ = 0 := by
  classical
  have hY : (univ.filter fun y => ∃ j ∈ (univ : Finset J), eB y j) = univ :=
    filter_true_of_mem (fun y _ => (hb y).imp (fun _ h => ⟨mem_univ _,h⟩))
  have hX : (univ.filter fun x => ∀ j, eA x j → j ∈ (univ : Finset J)) = univ :=
    filter_true_of_mem (fun _ _ _ _ => mem_univ _)
  unfold cutGap
  rw [hY,hX,card_univ,card_univ,ht,sub_self]

set_option maxHeartbeats 800000 in
/-- The largest violated cut equals the minimum total positive block
remainder over assignments to eligible blocks. -/
theorem exists_assignment_exact_deficit (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (ha : ∀ x, ∃ j, eA x j) (hb : ∀ y, ∃ j, eB y j)
    (ht : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X) :
    ∃ a : X → J, ∃ b : Y → J, (∀ x, eA x (a x)) ∧ (∀ y, eB y (b y)) ∧
      assignmentDeficit delta a b = transportDeficit eA eB delta := by
  classical
  let d := transportDeficit eA eB delta
  let A' (x : X ⊕ Fin d) (j : J) := x.elim (eA · j) (fun _ => True)
  let B' (y : Y ⊕ Fin d) (j : J) := y.elim (eB · j) (fun _ => True)
  have hcuts : TransportCuts A' B' delta := by
    intro S
    have hA : (univ.filter fun x => ∀ j, A' x j → j ∈ S).card =
        (univ.filter fun x => ∀ j, eA x j → j ∈ S).card +
          (univ.filter fun _ : Fin d => ∀ j : J, j ∈ S).card := by
      apply (card_filter_congr _ (Sum.elim (fun x => ∀ j, eA x j → j ∈ S)
        (fun _ : Fin d => ∀ j : J, j ∈ S)) (by
          intro x
          cases x <;> simp [A'])).trans
      exact card_filter_sum _ _
    have hB : (univ.filter fun y => ∃ j ∈ S, B' y j).card =
        (univ.filter fun y => ∃ j ∈ S, eB y j).card +
          (univ.filter fun _ : Fin d => S.Nonempty).card := by
      apply (card_filter_congr _ (Sum.elim (fun y => ∃ j ∈ S, eB y j)
        (fun _ : Fin d => S.Nonempty)) (by
          intro y
          cases y <;> simp [B',Finset.Nonempty])).trans
      exact card_filter_sum _ _
    rw [hA,hB]
    have hAc : (univ.filter fun _ : Fin d => ∀ j : J, j ∈ S).card =
        if ∀ j : J, j ∈ S then d else 0 := by
      by_cases h : ∀ j : J, j ∈ S <;> simp [h]
    have hBc : (univ.filter fun _ : Fin d => S.Nonempty).card = if S.Nonempty then d else 0 := by
      by_cases h : S.Nonempty <;> simp [h]
    by_cases hne : S.Nonempty
    · rw [if_pos hne] at hBc
      by_cases hfull : ∀ j, j ∈ S
      · rw [if_pos hfull] at hAc
        have he : S = univ := eq_univ_of_forall hfull
        have hz : cutGap eA eB delta S = 0 := by
          rw [he]
          exact cutGap_univ eA eB delta hb ht
        unfold cutGap at hz
        omega
      · rw [if_neg hfull] at hAc
        have hGap := cutGap_le_transportDeficit eA eB delta S
        change cutGap eA eB delta S ≤ (d : ℤ) at hGap
        unfold cutGap at hGap
        omega
    · rw [if_neg hne] at hBc
      have hzero : S = ∅ := not_nonempty_iff_eq_empty.mp hne
      have hz : cutGap eA eB delta S = 0 := by
        rw [hzero]
        exact cutGap_empty eA eB delta ha
      unfold cutGap at hz
      by_cases hfull : ∀ j, j ∈ S
      · rw [if_pos hfull] at hAc
        have hd : d = 0 := by
          unfold d transportDeficit
          apply le_antisymm _ (Nat.zero_le _)
          apply Finset.sup_le
          intro T _
          have he : T = ∅ := eq_empty_iff_forall_notMem.mpr
            (fun j _ => notMem_empty j (hzero ▸ hfull j))
          rw [he,cutGap_empty eA eB delta ha]
          rfl
        omega
      · rw [if_neg hfull] at hAc
        omega
  obtain ⟨a',b',haa,hbb,hbal⟩ := assign_of_transport_cuts A' B' delta
    (by simp [Fintype.card_sum, ht]) hcuts
  let a (x : X) := a' (.inl x)
  let b (y : Y) := b' (.inl y)
  let a₀ (x : Fin d) := a' (.inr x)
  let b₀ (y : Fin d) := b' (.inr y)
  have ha' (x : X) : eA x (a x) := haa (.inl x)
  have hb' (y : Y) : eB y (b y) := hbb (.inl y)
  have bound (j : J) : (remainder delta a b j).toNat ≤ assignedCount b₀ j := by
    have hA : assignedCount a' j = assignedCount a j + assignedCount a₀ j :=
      (card_filter_congr _ (Sum.elim (fun x => a x = j) (fun x => a₀ x = j))
        (by intro x; cases x <;> rfl)).trans (card_filter_sum _ _)
    have hB : assignedCount b' j = assignedCount b j + assignedCount b₀ j :=
      (card_filter_congr _ (Sum.elim (fun x => b x = j) (fun x => b₀ x = j))
        (by intro x; cases x <;> rfl)).trans (card_filter_sum _ _)
    have h : (assignedCount b' j : ℤ) - assignedCount a' j = delta j := hbal j
    rw [hA,hB] at h
    unfold remainder
    omega
  refine ⟨a,b,ha',hb',le_antisymm ?_ (transportDeficit_le_assignment eA eB delta a b ha' hb')⟩
  unfold assignmentDeficit
  exact (sum_le_sum (fun j _ => bound j)).trans_eq (by simpa [d] using sum_assignedCount b₀)

private theorem card_filter_le_changed {V : Type*} [Fintype V]
    (p q : V → Prop) [DecidablePred p] [DecidablePred q] (changed : Finset V)
    (h : ∀ x ∉ changed, p x → q x) :
    (univ.filter p).card ≤ (univ.filter q).card + changed.card := by
  classical
  have hsub : univ.filter p ⊆ univ.filter q ∪ changed := by
    intro x hx
    by_cases hxc : x ∈ changed
    · exact mem_union_right _ hxc
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h x hxc (mem_filter.mp hx).2⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

private theorem cutGap_le_of_changed (eA fA : X → J → Prop) (eB fB : Y → J → Prop)
    (delta : J → ℤ) (S : Finset J) (changedA : Finset X) (changedB : Finset Y)
    (ha : ∀ x ∉ changedA, ∀ j, eA x j ↔ fA x j)
    (hb : ∀ y ∉ changedB, ∀ j, eB y j ↔ fB y j) :
    cutGap fA fB delta S ≤ cutGap eA eB delta S + changedA.card + changedB.card := by
  classical
  have hA := card_filter_le_changed (fun x => ∀ j, fA x j → j ∈ S) (fun x => ∀ j, eA x j → j ∈ S)
    changedA (fun x hx h j hj => h j ((ha x hx j).mp hj))
  have hB := card_filter_le_changed (fun y => ∃ j ∈ S, eB y j) (fun y => ∃ j ∈ S, fB y j)
    changedB (fun y hy ⟨j,hj,h⟩ => ⟨j,hj,(hb y hy j).mp h⟩)
  unfold cutGap
  omega

/-- Changing eligibility for a set of exceptional vertices increases the
maximum cut deficit by at most the size of that set across both sides. -/
theorem transportDeficit_le_of_changed (eA fA : X → J → Prop) (eB fB : Y → J → Prop)
    (delta : J → ℤ) (changedA : Finset X) (changedB : Finset Y)
    (ha : ∀ x ∉ changedA, ∀ j, eA x j ↔ fA x j)
    (hb : ∀ y ∉ changedB, ∀ j, eB y j ↔ fB y j) :
    transportDeficit fA fB delta ≤ transportDeficit eA eB delta + changedA.card + changedB.card := by
  classical
  apply Finset.sup_le
  intro S _
  apply Int.toNat_le.mpr
  have h₁ := cutGap_le_of_changed eA fA eB fB delta S changedA changedB ha hb
  have h₂ := cutGap_le_transportDeficit eA eB delta S
  omega

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.transportDeficit_eq_zero_iff
#print axioms WeightedPaper.Blocks.exists_assignment_exact_deficit
#print axioms WeightedPaper.Blocks.transportDeficit_le_of_changed
