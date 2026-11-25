module

public import WeightedRecolouring.Statement
public import OverfullWork.WeightedComponentSwap

@[expose] public section


namespace WeightedRecolouring
open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

noncomputable def contrast (C : M.EdgeColoring k) (w : V → ℝ) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) : ℝ :=
  ∑ v∈C.componentSet a b z, w v*((C.colourGraph a).degree v-(C.colourGraph b).degree v : ℝ)

noncomputable def surplus (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) : ℝ :=
  ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)-
    ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ)

theorem abs_contrast_le (C : M.EdgeColoring k) (w : V → ℝ) (S : ℝ) (hS : 0≤S)
    (hw : ∀ v,|w v|≤S/2) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    |contrast C w a b z|≤S := by
  let T := (C.componentSet a b z).filter
    (fun v => (C.colourGraph a).degree v≠(C.colourGraph b).degree v)
  let f : V → ℝ := fun v => w v*((C.colourGraph a).degree v-(C.colourGraph b).degree v : ℝ)
  have hT : T.card≤2 := C.component_exclusive_card_le_two a b z
  have hlocal (v : V) : |f v|≤S/2 := by
    have ha : ((C.colourGraph a).degree v:ℝ)≤1 := by exact_mod_cast C.colourGraph_degree_le_one a v
    have hb : ((C.colourGraph b).degree v:ℝ)≤1 := by exact_mod_cast C.colourGraph_degree_le_one b v
    have hdeg : |((C.colourGraph a).degree v:ℝ)-(C.colourGraph b).degree v|≤1 := by
      have ha₀ : 0≤((C.colourGraph a).degree v:ℝ) := Nat.cast_nonneg _
      have hb₀ : 0≤((C.colourGraph b).degree v:ℝ) := Nat.cast_nonneg _
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    exact (abs_mul _ _).trans_le (by
      calc
        |w v| * |((C.colourGraph a).degree v:ℝ)-(C.colourGraph b).degree v| ≤ |w v| * 1 :=
          mul_le_mul_of_nonneg_left hdeg (abs_nonneg _)
        _ ≤ S/2 := by simpa using hw v)
  have hfilter : contrast C w a b z=∑ v∈T,f v := by
    unfold contrast
    rw [show T=(C.componentSet a b z).filter _ from rfl,sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases h : (C.colourGraph a).degree v=(C.colourGraph b).degree v <;> simp [f,h]
  rw [hfilter]
  calc
    _ ≤ ∑ v∈T,|f v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v∈T,S/2 := sum_le_sum (fun v _ => hlocal v)
    _ = (T.card:ℝ)*(S/2) := by simp
    _ ≤ S := by
      have hc : (T.card:ℝ)≤2 := by exact_mod_cast hT
      nlinarith

theorem sum_surplus (C : M.EdgeColoring k) (a b : Fin k) :
    (∑ z,surplus C a b z)=(C.colourMass a:ℝ)-C.colourMass b := by
  simp only [surplus,sum_sub_distrib,←Nat.cast_sum,
    C.sum_component_mass a b a (Or.inl rfl),C.sum_component_mass a b b (Or.inr rfl)]

private theorem selected_univ (C : M.EdgeColoring k) (a b : Fin k) :
    C.selectedComponentSet a b univ=univ := by
  simp [MultiGraph.EdgeColoring.selectedComponentSet]

theorem sum_contrast (C : M.EdgeColoring k) (w : V → ℝ) (a b : Fin k) :
    (∑ z,contrast C w a b z)=load C w a-load C w b := by
  unfold contrast
  rw [←C.sum_selected_components a b univ (fun v =>
    w v*((C.colourGraph a).degree v-(C.colourGraph b).degree v : ℝ)),selected_univ]
  simp only [load,mul_sub,sum_sub_distrib]

theorem swap_preserves_mass (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (h : ∑ z∈T,surplus C a b z=0) :
    ∀ i,(C.swapSelected a b T).colourMass i=C.colourMass i := by
  unfold surplus at h
  rw [sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,sub_eq_zero] at h
  exact C.swapSelected_mass_preserved a b T (by exact_mod_cast h)

theorem swap_load (C : M.EdgeColoring k) (w : V → ℝ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (i : Fin k) :
    load (C.swapSelected a b T) w i=load C w i+
      ∑ v∈C.selectedComponentSet a b T, w v*
      ((C.colourGraph (Equiv.swap a b i)).degree v-(C.colourGraph i).degree v : ℝ) := by
  unfold load
  have hset : (univ.filter (·∈C.selectedComponentSet a b T))=C.selectedComponentSet a b T := by
    ext
    simp
  rw [←hset,sum_filter,←sum_add_distrib]
  apply sum_congr rfl
  intro v _
  rw [MultiGraph.EdgeColoring.swapSelected,C.swapClosed_degree]
  by_cases h : v∈C.selectedComponentSet a b T <;> simp [h,mul_sub]

theorem swap_load_left (C : M.EdgeColoring k) (w : V → ℝ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) :
    load (C.swapSelected a b T) w a=load C w a-∑ z∈T,contrast C w a b z := by
  rw [swap_load,Equiv.swap_apply_left]
  unfold contrast
  rw [←C.sum_selected_components a b T (fun v =>
    w v*((C.colourGraph a).degree v-(C.colourGraph b).degree v : ℝ))]
  simp only [mul_sub,sum_sub_distrib]
  ring

theorem swap_load_right (C : M.EdgeColoring k) (w : V → ℝ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) :
    load (C.swapSelected a b T) w b=load C w b+∑ z∈T,contrast C w a b z := by
  rw [swap_load,Equiv.swap_apply_right]
  unfold contrast
  rw [←C.sum_selected_components a b T (fun v =>
    w v*((C.colourGraph a).degree v-(C.colourGraph b).degree v : ℝ))]

theorem swap_load_other (C : M.EdgeColoring k) (w : V → ℝ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (i : Fin k)
    (ha : i≠a) (hb : i≠b) :
    load (C.swapSelected a b T) w i=load C w i := by
  rw [swap_load,Equiv.swap_apply_of_ne_of_ne ha hb]
  simp

theorem load_shift (C : M.EdgeColoring k) (w : V → ℝ) (c : ℝ) (i : Fin k) :
    load C (fun v => w v-c) i=load C w i-2*c*(C.colourMass i:ℝ) := by
  simp only [load,sub_mul,sum_sub_distrib,←mul_sum,←Nat.cast_sum,
    (C.colourGraph i).sum_degrees_eq_twice_edgeCount,Nat.cast_mul,Nat.cast_ofNat,
    MultiGraph.EdgeColoring.colourMass]
  ring

end WeightedRecolouring
