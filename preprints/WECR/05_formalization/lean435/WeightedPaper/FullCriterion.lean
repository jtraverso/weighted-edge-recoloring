import WeightedPaper.Incidence

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M N : MultiGraph V} {k : ℕ}

/-- The maximum gap of an equitable palette with the indicated total. -/
def equitableGap (k e : ℕ) : ℕ := if k ∣ e then 0 else 1

private theorem mass_gap_of_equitable (A : M.EdgeColoring k) (hA : A.IsEquitable) (i j : Fin k) :
    A.colourMass i ≤ A.colourMass j + equitableGap k M.edgeCount := by
  classical
  unfold equitableGap
  split_ifs with hd
  · obtain ⟨q,hq⟩ := hd
    have hsum : (∑ i : Fin k,A.colourMass i) = ∑ _i : Fin k,q := by
      simp only [A.sum_colourMass,hq,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
    obtain ⟨π,hπ⟩ := OverfullWork.PaletteAlignment.equitable_vectors_permutation
      A.colourMass (fun _ => q) hA (by simp) hsum
    simpa [hπ i,hπ j]
  · exact hA i j

private theorem mass_le_of_equitable (A : M.EdgeColoring k) (hA : A.IsEquitable)
    (a : ℕ) (ha : M.edgeCount ≤ k*a) (i : Fin k) : A.colourMass i ≤ a := by
  by_contra! h
  have hb (j : Fin k) : a ≤ A.colourMass j := by
    have hj := hA i j
    omega
  have total : (∑ _j : Fin k,a) < ∑ j,A.colourMass j :=
    sum_lt_sum (fun j _ => hb j) ⟨i,mem_univ i,h⟩
  rw [A.sum_colourMass] at total
  simp at total
  omega

private theorem colour_degree_zero_outside (T : Finset V)
    (C : (M.restrict T).EdgeColoring k) (i : Fin k) {v : V} (hv : v ∉ T) :
    (C.colourGraph i).degree v = 0 := by
  have h := C.incidence_le_degree v i
  rw [MultiGraph.degree_restrict,if_neg hv] at h
  omega

private theorem missingOn_card_and_mass (T : Finset V)
    (C : (M.restrict T).EdgeColoring k) (i : Fin k) :
    (missingOn C T i).card + 2*C.colourMass i = T.card := by
  classical
  have hcount : (missingOn C T i).card + (∑ v : T,(C.colourGraph i).degree v.val) = T.card := by
    unfold missingOn
    rw [card_eq_sum_ones,sum_filter,←sum_add_distrib]
    calc
      _ = ∑ _v : T,1 := by
        apply sum_congr rfl
        intro v _
        have hd := C.colourGraph_degree_le_one i v.val
        split_ifs <;> omega
      _ = _ := by simp
  have hd : (∑ v : T,(C.colourGraph i).degree v.val) = 2*C.colourMass i := by
    calc
      _ = ∑ v ∈ T,(C.colourGraph i).degree v := sum_attach T _
      _ = ∑ v,(C.colourGraph i).degree v := sum_subset (subset_univ _) (fun v _ hv =>
        colour_degree_zero_outside T C i hv)
      _ = _ := (C.colourGraph i).sum_degrees_eq_twice_edgeCount
  rwa [hd] at hcount

private theorem colourGraph_of_cast (h : M=N) (C : M.EdgeColoring k) (i : Fin k) :
    (h ▸ C : N.EdgeColoring k).colourGraph i = C.colourGraph i := by
  cases h
  rfl

/-- Start with arbitrarily coloured internal parts, balance and align the
palettes, recolour once on each side using the supplied incidence profiles,
and factor the ambient multigraph across a dense or robust ordinary cut. -/
theorem exists_factorization_of_weighted_cut (M : MultiGraph V) (L : Finset V)
    (D k m a : ℕ) (hk : k ≤ D) (hreg : M.IsRegularOfDegree D)
    (X : Finset L) (Y : Finset (Lᶜ : Finset V))
    (hmA : L.card = m) (hmB : (Lᶜ : Finset V).card = m)
    (hcap : (M.restrict L).edgeCount ≤ k*a)
    (hA : Nonempty ((M.restrict L).EdgeColoring k))
    (hB : Nonempty ((M.restrict Lᶜ).EdgeColoring k))
    (rowsA : IncidenceBudget M Lᶜ (fun (x : L) y => M.mult s(x.val,y.val)) X Y
      k (equitableGap k (M.restrict L).edgeCount))
    (rowsB : IncidenceBudget M L (fun (y : (Lᶜ : Finset V)) x => M.mult s(x.val,y.val)) Y X
      k (equitableGap k (M.restrict L).edgeCount))
    (hcut : DenseCut (fun x y => M.mult s(x.val,y.val)) X Y m a k ∨
      RobustCut (fun x y => M.mult s(x.val,y.val)) X Y a k) :
    ∃ F : M.EdgeColoring D, F.IsFactorization := by
  classical
  obtain ⟨A⟩ := hA
  obtain ⟨B⟩ := hB
  have he : (M.restrict L).edgeCount = (M.restrict Lᶜ).edgeCount :=
    M.internal_edge_counts_eq_of_regular L D hreg (hmA.trans hmB.symm)
  obtain ⟨A₀,B₀,hAeq,hBeq,hMatch⟩ := A.exists_aligned_equitable_pair B he
  obtain ⟨A₁,hA₁,hAReserve⟩ := rowsB.exists_recolour A₀ hAeq (mass_gap_of_equitable A₀ hAeq)
  obtain ⟨B₁,hB₁,hBReserve⟩ := rowsA.exists_recolour B₀ hBeq
    (fun i j => by simpa only [← he] using mass_gap_of_equitable B₀ hBeq i j)
  let F := A₁.addSamePalette B₁ (M.restrict_vertex_disjoint L)
  let C : (M.internalPart L).EdgeColoring k := M.restrict_add_restrict_compl L ▸ F
  have hdegree (v : V) (i : Fin k) :
      (C.colourGraph i).degree v = (A₁.colourGraph i).degree v + (B₁.colourGraph i).degree v := by
    rw [show C.colourGraph i = F.colourGraph i from colourGraph_of_cast _ F i]
    unfold MultiGraph.degree
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun _ _ => rfl)
  have hLeft (i : Fin k) : missingOn C L i = missingOn A₁ L i := by
    ext v
    have hv : v.val ∉ (Lᶜ : Finset V) := fun h => (mem_compl.mp h) v.2
    simp only [missingOn,mem_filter,mem_univ,true_and,hdegree,
      colour_degree_zero_outside Lᶜ B₁ i hv,Nat.add_zero]
  have hRight (i : Fin k) : missingOn C Lᶜ i = missingOn B₁ Lᶜ i := by
    ext v
    simp only [missingOn,mem_filter,mem_univ,true_and,hdegree,
      colour_degree_zero_outside L A₁ i (mem_compl.mp v.2),Nat.zero_add]
  let aᵢ := A₁.colourMass
  have hsize (i : Fin k) : (missingOn C L i).card+2*aᵢ i = m ∧
      (missingOn C Lᶜ i).card+2*aᵢ i = m ∧ aᵢ i ≤ a := by
    have hsame : aᵢ i = B₁.colourMass i := (hA₁ i).trans ((hMatch i).trans (hB₁ i).symm)
    have hAi : aᵢ i = A₀.colourMass i := hA₁ i
    refine ⟨?_,?_,hAi ▸ mass_le_of_equitable A₀ hAeq a hcap i⟩
    · rw [hLeft,← hmA]
      exact missingOn_card_and_mass L A₁ i
    · rw [hRight,hsame,← hmB]
      exact missingOn_card_and_mass Lᶜ B₁ i
  have hrowsA : RowReserves (missingOn C L) (missingOn C Lᶜ)
      (fun x y => M.mult s(x.val,y.val)) univ X Y := by
    refine ⟨rowsA.weight,rowsA.charge,rowsA.bound,rowsA.bound_pos,rowsA.charge_nonneg,
      rowsA.capacity,rowsA.column,?_⟩
    intro i _ x hx
    rw [hRight,card_univ,Fintype.card_fin]
    simp only [mem_filter] at hx
    have hh := hBReserve ⟨x,hx.2⟩ i
    convert hh using 1 <;> first | rfl | (refine sum_congr ?_ (fun _ _ => rfl); ext v <;> simp)
  have hrowsB : RowReserves (missingOn C Lᶜ) (missingOn C L)
      (fun y x => M.mult s(x.val,y.val)) univ Y X := by
    refine ⟨rowsB.weight,rowsB.charge,rowsB.bound,rowsB.bound_pos,rowsB.charge_nonneg,
      rowsB.capacity,rowsB.column,?_⟩
    intro i _ y hy
    rw [hLeft,card_univ,Fintype.card_fin]
    simp only [mem_filter] at hy
    have hh := hAReserve ⟨y,hy.2⟩ i
    convert hh using 1 <;> first | rfl | (refine sum_congr ?_ (fun _ _ => rfl); ext v <;> simp)
  exact exists_factorization_across_cut_of_reserves M L D k m a hk hreg C X Y aᵢ
    hmA hmB hsize hrowsA hrowsB hcut

end WeightedPaper
