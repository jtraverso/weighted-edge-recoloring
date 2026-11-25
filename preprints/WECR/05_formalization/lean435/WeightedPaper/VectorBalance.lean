import WeightedPaper.VectorComponents
import WeightedRecolouring.Components

/-! Vector-valued balancing uses the same component swaps as the frozen
scalar proof. The discrepancy is written as a squared Euclidean norm. -/
namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : MultiGraph V} {k n : ℕ}

private theorem vector_contrast_bound (C : M.EdgeColoring k) (w : V → Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hw : ∀ v, energy (w v) ≤ R^2) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    energy (fun j => WeightedRecolouring.contrast C (fun v => w v j) a b z) ≤ (2*R)^2 := by
  let T := (C.componentSet a b z).filter
    (fun v => (C.colourGraph a).degree v ≠ (C.colourGraph b).degree v)
  let d (v : V) := ((C.colourGraph a).degree v : ℝ) - (C.colourGraph b).degree v
  let f (v : V) (j : Fin n) := w v j * d v
  have hT : T.card ≤ 2 := C.component_exclusive_card_le_two a b z
  have hf (v : V) : energy (f v) ≤ R^2 := by
    have ha : ((C.colourGraph a).degree v : ℝ) ≤ 1 := by exact_mod_cast C.colourGraph_degree_le_one a v
    have hb : ((C.colourGraph b).degree v : ℝ) ≤ 1 := by exact_mod_cast C.colourGraph_degree_le_one b v
    have ha' : 0 ≤ ((C.colourGraph a).degree v : ℝ) := Nat.cast_nonneg _
    have hb' : 0 ≤ ((C.colourGraph b).degree v : ℝ) := Nat.cast_nonneg _
    have hpos : -1 ≤ d v := by dsimp [d]; linarith
    have hneg : d v ≤ 1 := by dsimp [d]; linarith
    have hsq : (d v)^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hneg) (by linarith : 0 ≤ 1+d v)]
    calc
      energy (f v) = (d v)^2 * energy (w v) := by
        simp only [energy, f, mul_sum]
        exact sum_congr rfl (fun j _ => by ring)
      _ ≤ energy (w v) := by
        simpa using mul_le_mul_of_nonneg_right hsq (energy_nonneg (w v))
      _ ≤ _ := hw v
  have he (j : Fin n) :
      WeightedRecolouring.contrast C (fun v => w v j) a b z = ∑ v ∈ T, f v j := by
    unfold WeightedRecolouring.contrast
    rw [show T = (C.componentSet a b z).filter _ from rfl,sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases h : (C.colourGraph a).degree v = (C.colourGraph b).degree v <;> simp [f,d,h]
  have ht : (T.card : ℝ) ≤ 2 := by exact_mod_cast hT
  simp_rw [he]
  exact (energy_sum_le T f R hR (fun v _ => hf v)).trans
    (by gcongr <;> positivity)

private theorem vector_pair_repair (C : M.EdgeColoring k) (w : V → Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hw : ∀ v, energy (w v) ≤ R^2) (a b : Fin k)
    (hm : C.colourMass b ≤ C.colourMass a) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      (∀ i, i ≠ a → i ≠ b → ∀ j, WeightedRecolouring.load D (fun v => w v j) i =
        WeightedRecolouring.load C (fun v => w v j) i) ∧
      (∀ j, WeightedRecolouring.load D (fun v => w v j) a + WeightedRecolouring.load D (fun v => w v j) b =
        WeightedRecolouring.load C (fun v => w v j) a + WeightedRecolouring.load C (fun v => w v j) b) ∧
      energy (fun j => WeightedRecolouring.load D (fun v => w v j) a -
        WeightedRecolouring.load D (fun v => w v j) b) ≤
          (2*R)^2 * (((C.colourMass a : ℝ)-C.colourMass b)^2+4*n) := by
  let d := ((C.colourMass a : ℝ)-C.colourMass b)
  have hd : 0 ≤ d := sub_nonneg.mpr (by exact_mod_cast hm)
  obtain ⟨T,_,hT,hb⟩ := exists_vector_component_swaps univ (WeightedRecolouring.surplus C a b)
    (fun z j => WeightedRecolouring.contrast C (fun v => w v j) a b z) d (2*R) hd
    (by linarith) (fun z _ => by
      rcases C.component_real_card_difference a b z with h|h|h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    (WeightedRecolouring.sum_surplus C a b)
    (fun z _ => vector_contrast_bound C w R hR hw a b z)
  refine ⟨C.swapSelected a b T,WeightedRecolouring.swap_preserves_mass C a b T hT,
    fun i hi hj j => WeightedRecolouring.swap_load_other C (fun v => w v j) a b T i hi hj,?_,?_⟩
  · intro j
    rw [WeightedRecolouring.swap_load_left,WeightedRecolouring.swap_load_right]
    ring
  · have he (j : Fin n) :
        WeightedRecolouring.load (C.swapSelected a b T) (fun v => w v j) a -
          WeightedRecolouring.load (C.swapSelected a b T) (fun v => w v j) b =
        (∑ z,WeightedRecolouring.contrast C (fun v => w v j) a b z) -
          2*(∑ z ∈ T,WeightedRecolouring.contrast C (fun v => w v j) a b z) := by
      rw [WeightedRecolouring.swap_load_left,WeightedRecolouring.swap_load_right,
        WeightedRecolouring.sum_contrast]
      ring
    simp_rw [he]
    convert hb using 1 <;> dsimp [d] <;> ring

private theorem finite_colourings : Finite (M.EdgeColoring k) := by
  let encode (C : M.EdgeColoring k) (e : Sym2 V) (i : Fin k) : Fin (M.mult e+1) :=
    ⟨C.col e i, by
      have h : C.col e i ≤ ∑ j,C.col e j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
      rw [C.sum_col e] at h
      omega⟩
  apply Finite.of_injective encode
  intro C D h
  have he : C.col = D.col := by
    funext e i
    exact congrArg Fin.val (congrFun (congrFun h e) i)
  cases C
  cases D
  cases he
  rfl

private theorem sum_pair_split (f : Fin k → ℝ) (a b : Fin k) (hab : a ≠ b) :
    (∑ i,f i) = f a + f b + ∑ i ∈ (univ.erase a).erase b,f i := by
  have ha := sum_erase_add univ f (mem_univ a)
  have hb := sum_erase_add (univ.erase a) f (mem_erase.mpr ⟨hab.symm,mem_univ b⟩)
  linarith only [ha,hb]

private theorem energy_parallelogram (v w : Fin n → ℝ) :
    2*(energy v + energy w) =
      energy (fun j => v j+w j)+energy (fun j => v j-w j) := by
  simp only [energy, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

/-- A single proper colouring preserves all the labelled sizes and controls
the squared Euclidean discrepancy for every pair of colours. The coordinates
may be taken in any orthonormal representation of the centered profiles. -/
theorem exists_balanced_vector_prescribed_sizes (C : M.EdgeColoring k)
    (w : V → Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R) (hw : ∀ v, energy (w v) ≤ R^2) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ a b, energy (fun j => WeightedRecolouring.load D (fun v => w v j) a -
        WeightedRecolouring.load D (fun v => w v j) b) ≤
          (2*R)^2 * (((C.colourMass a : ℝ)-C.colourMass b)^2+4*n) := by
  classical
  letI : Finite (M.EdgeColoring k) := finite_colourings
  letI : Fintype (M.EdgeColoring k) := Fintype.ofFinite _
  let P : Finset (M.EdgeColoring k) := univ.filter fun D => ∀ i, D.colourMass i = C.colourMass i
  let L (D : M.EdgeColoring k) (i : Fin k) (j : Fin n) :=
    WeightedRecolouring.load D (fun v => w v j) i
  obtain ⟨D,hD,hmin⟩ := P.exists_min_image (fun D => ∑ i, energy (L D i)) ⟨C,by simp [P]⟩
  have hDM : ∀ i, D.colourMass i = C.colourMass i := (mem_filter.mp hD).2
  refine ⟨D,hDM,?_⟩
  suffices H : ∀ a b : Fin k, D.colourMass b ≤ D.colourMass a →
      energy (fun j => L D a j-L D b j) ≤
        (2*R)^2 * (((C.colourMass a : ℝ)-C.colourMass b)^2+4*n) by
    intro a b
    rcases le_total (D.colourMass b) (D.colourMass a) with h|h
    · exact H a b h
    · have he : energy (fun j => L D a j-L D b j) = energy (fun j => L D b j-L D a j) :=
        sum_congr rfl (fun j _ => by ring)
      change energy (fun j => L D a j-L D b j) ≤ _
      rw [he]
      convert H b a h using 1 <;> ring
  intro a b hm
  by_contra! hb
  have hab : a ≠ b := by
    intro h
    subst b
    simp [energy] at hb
    have hh : 0 ≤ (2*R)^2 * (4*(n:ℝ)) := by positivity
    linarith
  obtain ⟨E,hEM,hother,hsum,hgap⟩ := vector_pair_repair D w R hR hw a b hm
  have hE : E ∈ P := mem_filter.mpr ⟨mem_univ E,fun i => (hEM i).trans (hDM i)⟩
  rw [hDM,hDM] at hgap
  have hgap' : energy (fun j => L E a j-L E b j) < energy (fun j => L D a j-L D b j) :=
    hgap.trans_lt hb
  have hsum' : energy (fun j => L E a j+L E b j) = energy (fun j => L D a j+L D b j) :=
    congrArg energy (funext hsum)
  have hdrop : energy (L E a)+energy (L E b) < energy (L D a)+energy (L D b) := by
    linarith only [hgap',hsum',energy_parallelogram (L E a) (L E b),energy_parallelogram (L D a) (L D b)]
  have hrest : (∑ i ∈ (univ.erase a).erase b, energy (L E i)) =
      ∑ i ∈ (univ.erase a).erase b, energy (L D i) := by
    apply sum_congr rfl
    intro i hi
    exact congrArg energy (funext (hother i (mem_erase.mp (mem_erase.mp hi).2).1 (mem_erase.mp hi).1))
  have hle := hmin E hE
  rw [sum_pair_split _ a b hab,sum_pair_split _ a b hab,hrest] at hle
  linarith only [hdrop,hle]

end WeightedPaper
