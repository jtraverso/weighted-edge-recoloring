module

public import WeightedRecolouring.Components
public import WeightedRecolouring.Signing

@[expose] public section


namespace WeightedRecolouring
open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

private theorem finite_colourings : Finite (M.EdgeColoring k) := by
  let encode (C : M.EdgeColoring k) (e : Sym2 V) (i : Fin k) : Fin (M.mult e+1) :=
    ⟨C.col e i, by
      have h : C.col e i≤∑ j,C.col e j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
      rw [C.sum_col e] at h
      omega⟩
  apply Finite.of_injective encode
  intro C D h
  have hcol : C.col=D.col := by
    funext e i
    exact congrArg Fin.val (congrFun (congrFun h e) i)
  cases C
  cases D
  cases hcol
  rfl

private theorem exists_two_colour_balance (C : M.EdgeColoring k) (w : V → ℝ)
    (S : ℝ) (hS : 0≤S) (hw : ∀ v,|w v|≤S/2) (a b : Fin k)
    (hm : C.colourMass b≤C.colourMass a) :
    ∃ D : M.EdgeColoring k, (∀ i,D.colourMass i=C.colourMass i) ∧
      (∀ i,i≠a → i≠b → load D w i=load C w i) ∧
      load D w a+load D w b=load C w a+load C w b ∧
      |load D w a-load D w b| ≤
        if C.colourMass a=C.colourMass b then 2*S else
          ((C.colourMass a:ℝ)-C.colourMass b)*S := by
  let d := C.colourMass a-C.colourMass b
  have hd : (d:ℝ)=(C.colourMass a:ℝ)-C.colourMass b := Nat.cast_sub hm
  obtain ⟨T,_,hT,hbal⟩ := exists_component_swaps univ (surplus C a b)
    (contrast C w a b) S hS d (fun z _ => by
      rcases C.component_real_card_difference a b z with h|h|h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    (by rw [sum_surplus,hd]) (fun z _ => abs_contrast_le C w S hS hw a b z)
  refine ⟨C.swapSelected a b T,swap_preserves_mass C a b T hT,
    fun i hi hj => swap_load_other C w a b T i hi hj,?_ ,?_⟩
  · rw [swap_load_left,swap_load_right]
    ring
  · rw [swap_load_left,swap_load_right]
    rw [sum_contrast] at hbal
    have hzero : d=0 ↔ C.colourMass a=C.colourMass b := by dsimp [d]; omega
    rw [if_congr hzero rfl (congrArg (· * S) hd)] at hbal
    convert hbal using 2 <;> ring

private theorem sum_energy_pair (f : Fin k → ℝ) (a b : Fin k) (hab : a≠b) :
    (∑ i, (f i)^2)=(f a)^2+(f b)^2+∑ i∈(univ.erase a).erase b,(f i)^2 := by
  have hA := sum_erase_add univ (fun i => (f i)^2) (mem_univ a)
  have hB := sum_erase_add (univ.erase a) (fun i => (f i)^2) (mem_erase.mpr ⟨hab.symm,mem_univ b⟩)
  linarith only [hA,hB]

private theorem exists_centered_balance (C : M.EdgeColoring k) (w : V → ℝ)
    (S : ℝ) (hS : 0≤S) (hw : ∀ v,|w v|≤S/2) :
    ∃ D : M.EdgeColoring k, (∀ i,D.colourMass i=C.colourMass i) ∧
      ∀ a b,D.colourMass b≤D.colourMass a →
        |load D w a-load D w b| ≤
          if D.colourMass a=D.colourMass b then 2*S else
            ((D.colourMass a:ℝ)-D.colourMass b)*S := by
  letI : Finite (M.EdgeColoring k) := finite_colourings
  letI : Fintype (M.EdgeColoring k) := Fintype.ofFinite _
  let P : Finset (M.EdgeColoring k) := univ.filter fun D => ∀ i,D.colourMass i=C.colourMass i
  have hP : P.Nonempty := ⟨C, by simp [P]⟩
  let energy (D : M.EdgeColoring k) : ℝ := ∑ i,(load D w i)^2
  obtain ⟨D,hD,hmin⟩ := P.exists_min_image energy hP
  have hDmass : ∀ i,D.colourMass i=C.colourMass i := (mem_filter.mp hD).2
  refine ⟨D,hDmass, fun a b hm => ?_⟩
  by_contra! hbad
  have hab : a≠b := by
    intro h
    subst b
    simp at hbad
    linarith
  obtain ⟨R,hRmass,hRother,hRsum,hRgap⟩ := exists_two_colour_balance D w S hS hw a b hm
  have hR : R∈P := mem_filter.mpr ⟨mem_univ R, fun i => (hRmass i).trans (hDmass i)⟩
  have hsmall : |load R w a-load R w b| < |load D w a-load D w b| := hRgap.trans_lt hbad
  have hsquare : (load R w a-load R w b)^2 < (load D w a-load D w b)^2 :=
    sq_lt_sq.mpr hsmall
  have hsum : (load R w a+load R w b)^2=(load D w a+load D w b)^2 := by rw [hRsum]
  have hdrop : (load R w a)^2+(load R w b)^2 < (load D w a)^2+(load D w b)^2 := by
    nlinarith only [hsquare,hsum]
  have hrest : (∑ i∈(univ.erase a).erase b,(load R w i)^2)=
      ∑ i∈(univ.erase a).erase b,(load D w i)^2 := by
    apply sum_congr rfl
    intro i hi
    rw [hRother i (mem_erase.mp (mem_erase.mp hi).2).1 (mem_erase.mp hi).1]
  have hle := hmin R hR
  dsimp [energy] at hle
  rw [sum_energy_pair (fun i => load R w i) a b hab,
    sum_energy_pair (fun i => load D w i) a b hab,hrest] at hle
  linarith

/-- For any realizable labelled size vector, equal-size classes have
spread at most twice the vertex-weight oscillation. A larger class of
size difference d has extra load in [2 L d, 2 U d]. -/
theorem exists_balanced_prescribed_sizes (C : M.EdgeColoring k) (w : V → ℝ)
    (L U : ℝ) (hLU : L≤U) (hL : ∀ v,L≤w v) (hU : ∀ v,w v≤U) :
    ∃ D : M.EdgeColoring k, (∀ i,D.colourMass i=C.colourMass i) ∧
      (∀ a b,C.colourMass a=C.colourMass b → |load D w a-load D w b|≤2*(U-L)) ∧
      (∀ a b,C.colourMass b<C.colourMass a →
        2*L*((C.colourMass a:ℝ)-C.colourMass b) ≤ load D w a-load D w b ∧
        load D w a-load D w b ≤ 2*U*((C.colourMass a:ℝ)-C.colourMass b)) := by
  let c := (L+U)/2
  have hw : ∀ v,|w v-c|≤(U-L)/2 := fun v =>
    abs_le.mpr ⟨by dsimp [c]; linarith [hL v],by dsimp [c]; linarith [hU v]⟩
  obtain ⟨D,hD,h⟩ := exists_centered_balance C (fun v => w v-c) (U-L) (sub_nonneg.mpr hLU) hw
  refine ⟨D,hD,fun a b he => ?_,fun a b hlt => ?_⟩
  · have h' := h a b (by rw [hD a,hD b,he])
    rw [hD a,hD b,if_pos he,load_shift,load_shift,hD a,hD b,he,sub_sub_sub_cancel_right] at h'
    exact h'
  · have h' := h a b (by rw [hD a,hD b]; exact hlt.le)
    rw [hD a,hD b,if_neg hlt.ne.symm,load_shift,load_shift,hD a,hD b] at h'
    have ⟨hl,hu⟩ := abs_le.mp h'
    dsimp [c] at hl hu
    exact ⟨by linarith only [hl],by linarith only [hu]⟩

end WeightedRecolouring
