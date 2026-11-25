import LocalLemmaLib.LocalLemma

namespace WeightedPaper.Repair
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Q : Type*} [Fintype Q] [DecidableEq Q] {Ω : Q → Type*}
  [∀ q, Fintype (Ω q)] [∀ q, MeasurableSpace (Ω q)] [∀ q, MeasurableSingletonClass (Ω q)]

private theorem coord_measurable (D : Finset Q) (A : Set (∀ q, Ω q))
    (dep : ∀ ω ω', (∀ q ∈ D, ω q = ω' q) → ω ∈ A → ω' ∈ A) :
    MeasurableSet[MeasurableSpace.comap (fun ω (q : D) => ω q.val) MeasurableSpace.pi] A := by
  refine ⟨(fun ω (q : D) => ω q.val) '' A, (Set.toFinite _).measurableSet, ?_⟩
  ext ω
  constructor
  · rintro ⟨ω', hω', he⟩
    exact dep ω' ω (fun q hq => congrFun he ⟨q,hq⟩) hω'
  · exact fun h => ⟨ω,h,rfl⟩

private theorem prod_complement {I : Type*} (s : Finset I) (p : I → ℝ)
    (hn : ∀ i, 0 ≤ p i) (hu : ∀ i, p i ≤ 1) :
    1 - ∑ i ∈ s, p i ≤ ∏ i ∈ s, (1-p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have h := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hu i))
    nlinarith [mul_nonneg (hn i) (sum_nonneg (s := s) fun j _ => hn j)]

/-- The best scalar bound obtained by multiplying the two elementary
product estimates is the maximum of y²(1-y), attained at y = 2/3. -/
theorem pair_conflict_budget_scaling (y : ℝ) (hy : 0 ≤ y) :
    y^2*(1-y) ≤ 4/27 := by
  have fact : 4/27-y^2*(1-y) = (y-2/3)^2*(y+1/3) := by ring
  exact sub_nonneg.mp (fact.symm ▸ mul_nonneg (sq_nonneg _) (by linarith : 0 ≤ y+1/3))

/-- Independent requests may have different finite path spaces and different
laws. Events may test any conflict of their two coordinates. The incident
probability bound alone supplies all parameters for the asymmetric local lemma. -/
theorem select_without_pair_conflicts (law : ∀ q, Measure (Ω q)) [∀ q, IsProbabilityMeasure (law q)]
    {n : ℕ} (left right : Fin n → Q)
    (conflict : (i : Fin n) → Ω (left i) → Ω (right i) → Prop)
    (budget : ∀ q, (∑ i ∈ univ.filter (fun i => q = left i ∨ q = right i),
      (Measure.pi law).real {ω | conflict i (ω (left i)) (ω (right i))}) ≤ 4/27) :
    ∃ ω : (∀ q, Ω q), ∀ i, ¬ conflict i (ω (left i)) (ω (right i)) := by
  classical
  let μ := Measure.pi law
  let A (i : Fin n) : Set (∀ q, Ω q) := {ω | conflict i (ω (left i)) (ω (right i))}
  let p (i : Fin n) := μ.real (A i)
  let D (i : Fin n) : Finset Q := {left i, right i}
  let incident (q : Q) := univ.filter fun i => q ∈ D i
  have hb (q : Q) : ∑ i ∈ incident q, p i ≤ 4/27 := by simpa [incident, D, p, A, μ] using budget q
  have hn (i) : 0 ≤ p i := measureReal_nonneg
  have hu (i) : p i ≤ 4/27 := (single_le_sum (f := p) (fun j _ => hn j)
    (show i ∈ incident (left i) by simp [incident,D])).trans (hb _)
  let Γ : SimpleGraph (Fin n) :=
    { Adj := fun i j => i ≠ j ∧ ¬ Disjoint (D i) (D j)
      symm := ⟨fun _ _ h => ⟨Ne.symm h.1, fun hd => h.2 hd.symm⟩⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
  have dep (i : Fin n) (ω ω' : ∀ q, Ω q) (h : ∀ q ∈ D i, ω q = ω' q) :
      ω ∈ A i → ω' ∈ A i := by
    change conflict i _ _ → conflict i _ _
    rw [h (left i) (by simp [D]), h (right i) (by simp [D])]
    exact id
  have graph : LocalLemma.IsDependencyGraph μ A Γ := by
    intro i
    have hind : iIndepFun (fun q (ω : ∀ q, Ω q) => ω q) μ :=
      iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
    have h := hind.indepFun_finset (D i) (D i)ᶜ disjoint_compl_right fun q => measurable_pi_apply q
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1 h) ?_) ?_
    · refine MeasurableSpace.generateFrom_le fun t ht => ?_
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact coord_measurable _ _ (dep i)
    · refine MeasurableSpace.generateFrom_le fun t ht => ?_
      obtain ⟨j, hji, hadj, rfl⟩ := ht
      have hd : Disjoint (D i) (D j) := by by_contra hn'; exact hadj ⟨Ne.symm hji, hn'⟩
      exact coord_measurable _ _ fun ω ω' he => dep j ω ω' fun q hq =>
        he q (mem_compl.mpr fun h => disjoint_left.mp hd h hq)
  have neighbors (i) : Γ.neighborFinset i ⊆ incident (left i) ∪ incident (right i) := by
    intro j hj
    obtain ⟨_, hd⟩ := (Γ.mem_neighborFinset i j).mp hj
    obtain ⟨q, hi, hj⟩ := not_disjoint_iff.mp hd
    rcases (show q = left i ∨ q = right i by simpa [D] using hi) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h ▸ hj⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h ▸ hj⟩)
  have product (T : Finset (Fin n)) (q : Q)
      (subset : T ⊆ incident q) : (2/3 : ℝ) ≤ ∏ j ∈ T, (1-(9/4)*p j) := by
    have mass := (sum_le_sum_of_subset_of_nonneg (f := p) subset (fun j _ _ => hn j)).trans (hb q)
    have h := prod_complement T (fun j => (9/4)*p j)
      (fun j => by linarith [hn j]) (fun j => by linarith [hu j])
    rw [← mul_sum] at h
    linarith
  have weight (i) : p i ≤ ((9/4)*p i) * ∏ j ∈ Γ.neighborFinset i, (1-(9/4)*p j) := by
    let U := Γ.neighborFinset i ∩ incident (left i)
    let V := Γ.neighborFinset i \ U
    have UL : U ⊆ incident (left i) := inter_subset_right
    have VR : V ⊆ incident (right i) := by
      intro j hj
      obtain ⟨hg,hu⟩ := mem_sdiff.mp hj
      rcases mem_union.mp (neighbors i hg) with left | right
      · exact (hu (mem_inter.mpr ⟨hg,left⟩)).elim
      · exact right
    have split : (∏ j ∈ V, (1-(9/4)*p j)) * (∏ j ∈ U, (1-(9/4)*p j)) =
        ∏ j ∈ Γ.neighborFinset i, (1-(9/4)*p j) :=
      prod_sdiff inter_subset_left
    have h := mul_le_mul (product V (right i) VR) (product U (left i) UL)
      (by norm_num) ((by norm_num : (0:ℝ) ≤ 2/3).trans (product V (right i) VR))
    rw [split] at h
    exact (show p i = ((9/4)*p i)*(2/3* (2/3)) by ring).le.trans
      (mul_le_mul_of_nonneg_left h (by linarith [hn i]))
  have H := LocalLemma.lll μ A (fun i => (Set.toFinite _).measurableSet) Γ graph
    (fun i => (9/4)*p i) (fun i => by linarith [hn i]) (fun i => by linarith [hu i]) weight
  have hp : 0 < ∏ i, (1-(9/4)*p i) := prod_pos fun i _ => by linarith [hu i]
  have ne : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra! h
    rw [h] at H
    simpa using hp.trans_le H
  obtain ⟨ω,hω⟩ := ne
  exact ⟨ω, Set.mem_iInter.mp hω⟩

end WeightedPaper.Repair
