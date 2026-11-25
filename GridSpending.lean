module

public import GridHost

@[expose] public section


namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical
variable {H W : Type} [Fintype H] [Fintype W]

/-- Every round uses a filler/anchor pair or one of the two directions of a
hole-helper exchange. The tag of the round chooses its physical grid pool. -/
theorem round_pair_kind (p : Equiv.Perm (H ⊕ W)) (f : H → W)
    (swap : ∀ h, p (.inl h) = .inr (f h) ∧ p (.inr (f h)) = .inl h)
    (stay : ∀ w, w ∉ Set.range f → p (.inr w) = .inr w)
    {x y : Side H W} (used : (x,y) ∈ roundPairs p) :
    static x y ∨ ∃ h,
      (x = mark h false ∧ y = ordinaryHelper (f h)) ∨
      (x = ordinaryHelper (f h) ∧ y = mark h false) := by
  obtain ⟨u,_,e⟩ := mem_image.mp used
  rcases Prod.mk.inj e with ⟨hx,hy⟩
  subst x; subst y
  have active_step (u : H ⊕ W) : onFree p (.inr (.inr u)) = .inr (.inr (p u)) := rfl
  rcases u with i | (⟨h,k⟩ | (h|w))
  · exact Or.inl rfl
  · cases k <;> exact Or.inl rfl
  · rw [active_step,(swap h).1]
    exact Or.inr ⟨h,Or.inl ⟨rfl,rfl⟩⟩
  · by_cases hw : w ∈ Set.range f
    · obtain ⟨h,rfl⟩ := hw
      rw [active_step,(swap h).2]
      exact Or.inr ⟨h,Or.inr ⟨rfl,rfl⟩⟩
    · rw [active_step,stay w hw]
      exact Or.inl rfl

theorem grid_round_spending (R : Ordinary H W → Ordinary H W → Prop) (d : ℕ)
    (f : Fin d → H → W) (tag : Fin d → Bool) (p : Fin d → Equiv.Perm (H ⊕ W))
    (uses : ∀ j h, ordinary R (mark h false) (ordinaryHelper (f j h)) ∧
      ordinary R (ordinaryHelper (f j h)) (mark h false))
    (once : ∀ h, Function.Injective (fun j => (tag j,f j h)))
    (swap : ∀ j h, p j (.inl h) = .inr (f j h) ∧ p j (.inr (f j h)) = .inl h)
    (stay : ∀ j w, w ∉ Set.range (f j) → p j (.inr w) = .inr w) :
    ∀ x y, spending univ (fun j => roundPairs (p j)) x y ≤ capacity R d x y := by
  classical
  intro x y
  by_cases hxy : static x y
  · unfold capacity
    have c : spending univ (fun j => roundPairs (p j)) x y ≤ d :=
      (card_le_univ _).trans (by simp)
    simp only [hxy,ite_true]
    omega
  let S := univ.filter fun j => (x,y) ∈ roundPairs (p j)
  have hop (j : S) : ∃ h,
      (x = mark h false ∧ y = ordinaryHelper (f j h)) ∨
      (x = ordinaryHelper (f j h) ∧ y = mark h false) :=
    (round_pair_kind (p j) (f j) (swap j) (stay j) (mem_filter.mp j.property).2).resolve_left hxy
  by_cases hR : ordinary R x y
  · have inj : Function.Injective (fun j : S => tag j.val) := by
      intro j k e
      obtain ⟨hj,ej⟩ := hop j
      obtain ⟨hk,ek⟩ := hop k
      have markInj {h h' : H} (eq : (mark h false : Side H W) = mark h' false) : h = h' := by
        simpa [mark] using eq
      have helperInj {u v : W} (eq : (ordinaryHelper u : Side H W) = ordinaryHelper v) : u = v := by
        simpa [ordinaryHelper] using eq
      have apart (h : H) (w : W) : (mark h false : Side H W) ≠ ordinaryHelper w := by simp [mark,ordinaryHelper]
      rcases ej with ⟨hx,hy⟩|⟨hx,hy⟩ <;> rcases ek with ⟨hx',hy'⟩|⟨hx',hy'⟩
      · have hh := markInj (hx.symm.trans hx')
        subst hk
        exact Subtype.ext (once hj (Prod.ext e (helperInj (hy.symm.trans hy'))))
      · exact (apart _ _ (hx.symm.trans hx')).elim
      · exact (apart _ _ (hx'.symm.trans hx)).elim
      · have hh := markInj (hy.symm.trans hy')
        subst hk
        exact Subtype.ext (once hj (Prod.ext e (helperInj (hx.symm.trans hx'))))
    have bound := Fintype.card_le_of_injective _ inj
    rw [Fintype.card_coe,Fintype.card_bool] at bound
    simpa only [capacity,hxy,ite_false,hR,ite_true,zero_add,spending] using bound
  · have no : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨h,⟨hx,hy⟩|⟨hx,hy⟩⟩ := hop ⟨j,hj⟩
      · exact hR (hx.symm ▸ hy.symm ▸ (uses j h).1)
      · exact hR (hx.symm ▸ hy.symm ▸ (uses j h).2)
    simp [spending,show (univ.filter fun j => (x,y) ∈ roundPairs (p j)) = ∅ from no]
end WeightedPaper.Repair.Grid
