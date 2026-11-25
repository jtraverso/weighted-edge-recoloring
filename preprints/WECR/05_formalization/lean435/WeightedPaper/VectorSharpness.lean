import WeightedPaper.EuclideanBalance
import OverfullWork.PaletteAlignment

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {J : Type*} [Fintype J] [DecidableEq J]

def coordinateEdge (j : J) : Sym2 (J × Bool) :=
  s((j,false),(j,true))

private theorem coordinateEdge_injective : Function.Injective (coordinateEdge : J → _) := by
  intro j l h
  rcases Sym2.eq_iff.mp h with h|h
  · exact congrArg Prod.fst h.1
  · exact Bool.noConfusion (congrArg Prod.snd h.1)

private theorem mem_coordinateEdge (j : J) (v : J × Bool) :
    v ∈ coordinateEdge j ↔ v.1 = j := by
  obtain ⟨v,b⟩ := v
  cases b <;> simp [coordinateEdge,Sym2.mem_iff]

noncomputable def coordinateMatching : MultiGraph (J × Bool) where
  mult e := if ∃ j : J, coordinateEdge j = e then 1 else 0
  loopless e he := by
    apply if_neg
    rintro ⟨j,rfl⟩
    simpa [coordinateEdge] using he

private theorem coordinate_mult (j : J) :
    (coordinateMatching (J := J)).mult (coordinateEdge j) = 1 := if_pos ⟨j,rfl⟩

private theorem colourGraph_degree_coordinate
    (C : (coordinateMatching (J := J)).EdgeColoring 2) (i : Fin 2) (v : J × Bool) :
    (C.colourGraph i).degree v = C.col (coordinateEdge v.1) i := by
  unfold MultiGraph.degree
  change (∑ e ∈ univ.filter (fun e : Sym2 (J × Bool) => v ∈ e), C.col e i) = _
  apply sum_eq_single _ _ _
  · intro e he hn
    have h0 : (coordinateMatching (J := J)).mult e = 0 := by
      apply if_neg
      rintro ⟨j,rfl⟩
      exact hn (congrArg coordinateEdge ((mem_coordinateEdge j v).mp (mem_filter.mp he).2).symm)
    have h : C.col e i ≤ (coordinateMatching (J := J)).mult e := by
      rw [← C.sum_col e]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  · intro hn
    exact (hn (mem_filter.mpr ⟨mem_univ _,(mem_coordinateEdge _ v).mpr rfl⟩)).elim

private theorem coordinateMatching_degree (v : J × Bool) :
    (coordinateMatching (J := J)).degree v = 1 := by
  rw [← coordinate_mult v.1]
  unfold MultiGraph.degree
  apply sum_eq_single _ _ _
  · intro e he hn
    apply if_neg
    rintro ⟨j,rfl⟩
    exact hn (congrArg coordinateEdge ((mem_coordinateEdge j v).mp (mem_filter.mp he).2).symm)
  · intro hn
    exact (hn (mem_filter.mpr ⟨mem_univ _,(mem_coordinateEdge _ v).mpr rfl⟩)).elim

private theorem coordinateMatching_edges :
    (coordinateMatching (J := J)).edgeCount = Fintype.card J := by
  classical
  let T := (univ : Finset J).image coordinateEdge
  have hmem (e : Sym2 (J × Bool)) : (∃ j : J, coordinateEdge j = e) ↔ e ∈ T := by simp [T]
  unfold MultiGraph.edgeCount
  change (∑ e : Sym2 (J × Bool), if ∃ j : J, coordinateEdge j = e then 1 else 0) = _
  simp_rw [hmem]
  rw [← sum_filter,← card_eq_sum_ones]
  have hEq : (univ.filter (· ∈ T)) = T := by ext x; simp
  rw [hEq]
  simp [T,card_image_of_injective _ coordinateEdge_injective]

/-- The lower-bound graph admits the prescribed equal cardinalities
whenever its number of edges is even. -/
theorem coordinateMatching_equal_palette (m : ℕ) (hJ : Fintype.card J = 2*m) :
    ∃ C : (coordinateMatching (J := J)).EdgeColoring 2, ∀ i, C.colourMass i = m := by
  let C : (coordinateMatching (J := J)).EdgeColoring 2 := {
    col e i := if i = 0 then coordinateMatching.mult e else 0
    sum_col e := by simp [Fin.sum_univ_two]
    proper v i := by
      by_cases h : i = 0
      · simp only [if_pos h]
        exact (coordinateMatching_degree v).le
      · simp [h] }
  obtain ⟨D,hD⟩ := C.exists_equitable
  have hs : ∑ i,D.colourMass i = ∑ _i : Fin 2,m := by
    rw [D.sum_colourMass,coordinateMatching_edges,hJ]
    simp
  obtain ⟨π,hπ⟩ := OverfullWork.PaletteAlignment.equitable_vectors_permutation D.colourMass
    (fun _ => m) hD (by simp) hs
  exact ⟨D,hπ⟩

noncomputable def coordinateWeight (R : ℝ) (v : J × Bool) (j : J) : ℝ :=
  if v.1 = j then R else 0

private theorem load_coordinate (R : ℝ) (C : (coordinateMatching (J := J)).EdgeColoring 2)
    (i : Fin 2) (j : J) :
    WeightedRecolouring.load C (fun v => coordinateWeight R v j) i =
      2*R*(C.col (coordinateEdge j) i : ℝ) := by
  unfold WeightedRecolouring.load
  have hPair (v : J × Bool) : (if v.1 = j then R else 0) *
        (C.col (coordinateEdge v.1) i : ℝ)
      = if v.1 = j then R * (C.col (coordinateEdge j) i : ℝ) else 0 := by
    split_ifs with h <;> simp [h]
  simp_rw [colourGraph_degree_coordinate, coordinateWeight,hPair]
  rw [Fintype.sum_prod_type]
  by_cases hF : j ∈ (univ : Finset J)
  · rw [sum_eq_single j]
    · simp [Fintype.sum_bool, two_mul, add_mul]
    · intro l _ hl
      simp [hl]
    · exact fun hn => (hn hF).elim
  · exact (hF (mem_univ j)).elim

theorem coordinateWeight_energy (R : ℝ) (v : J × Bool) :
    energy (coordinateWeight R v) = R^2 := by
  unfold energy
  rw [sum_eq_single v.1]
  · simp [coordinateWeight]
  · intro j _ hj
    simp [coordinateWeight,Ne.symm hj]
  · simp

/-- Every two-colouring of the coordinate matching has Euclidean
discrepancy squared `4 R² · |J|`. In particular this holds when the
classes have the same cardinality. -/
theorem coordinateMatching_discrepancy (R : ℝ)
    (C : (coordinateMatching (J := J)).EdgeColoring 2) :
    energy (fun j =>
      WeightedRecolouring.load C (fun v => coordinateWeight R v j) 0 -
      WeightedRecolouring.load C (fun v => coordinateWeight R v j) 1) =
      4*R^2*(Fintype.card J : ℝ) := by
  unfold energy
  calc
    _ = ∑ _j : J,4*R^2 := by
      apply sum_congr rfl
      intro j _
      change (WeightedRecolouring.load C (fun v => coordinateWeight R v j) 0 -
        WeightedRecolouring.load C (fun v => coordinateWeight R v j) 1)^2 = _
      rw [load_coordinate R C 0 j,load_coordinate R C 1 j]
      have h := C.sum_col (coordinateEdge j)
      rw [Fin.sum_univ_two,coordinate_mult] at h
      have hc : ((C.col (coordinateEdge j) 0 = 1) ∧ (C.col (coordinateEdge j) 1 = 0)) ∨
          ((C.col (coordinateEdge j) 0 = 0) ∧ (C.col (coordinateEdge j) 1 = 1)) := by omega
      rcases hc with ⟨h0,h1⟩|⟨h0,h1⟩ <;> simp [h0,h1] <;> ring
    _ = _ := by simp [mul_comm]

end WeightedPaper
