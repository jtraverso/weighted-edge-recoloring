import WeightedPaper.IntrinsicBalance
import WeightedPaper.Examples.Matrices
import WeightedPaper.Cut.ExactReserves

namespace WeightedPaper.Examples
open Finset

variable {r : ℕ}

/-- Center the coordinate profiles at the barycenter of the simplex. -/
noncomputable def barycentricProfile (j : Fin r) (i : Fin r) : ℝ := basis j i - 1/(r:ℝ)

private theorem sum_basis (j : Fin r) : ∑ i, basis j i = 1 := by
  classical
  simp [basis]

private theorem sum_barycentric (hr : 0 < r) (j : Fin r) : ∑ i, barycentricProfile j i = 0 := by
  rw [show (∑ i, barycentricProfile j i) = (∑ i, basis j i)-∑ _ : Fin r, 1/(r:ℝ) by
    simp [barycentricProfile,sum_sub_distrib]]
  rw [sum_basis]
  simp [div_eq_mul_inv, hr.ne']

private noncomputable def coordinateSum (r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i

private theorem coordinateSum_apply (x : Fin r → ℝ) : coordinateSum r x = ∑ i, x i := by
  simp [coordinateSum,LinearMap.sum_apply]

theorem barycentric_span_finrank (hr : 0 < r) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (@barycentricProfile r))) = r-1 := by
  classical
  let S := Submodule.span ℝ (Set.range (@barycentricProfile r))
  have hspan : S = (coordinateSum r).ker := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨j,rfl⟩
      change barycentricProfile j ∈ (coordinateSum r).ker
      rw [LinearMap.mem_ker,coordinateSum_apply]
      exact sum_barycentric hr j
    · intro x hx
      have hz : ∑ i, x i = 0 := by simpa only [LinearMap.mem_ker,coordinateSum_apply] using hx
      have hdecomp : (∑ j, x j • barycentricProfile j) = x := by
        funext i
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply,smul_eq_mul,barycentricProfile,mul_sub,
          sum_sub_distrib,←sum_mul,hz,zero_mul,sub_zero]
        simp [basis,mul_ite]
      rw [←hdecomp]
      exact S.sum_mem fun j _ => S.smul_mem (x j) (Submodule.subset_span ⟨j,rfl⟩)
  have hTop : (coordinateSum r).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro t
    let j : Fin r := ⟨0,hr⟩
    refine ⟨fun i => t * basis j i,?_⟩
    rw [coordinateSum_apply,←mul_sum,sum_basis,mul_one]
  have hRank := (coordinateSum r).finrank_range_add_finrank_ker
  rw [hTop,Submodule.topEquiv.finrank_eq,Module.finrank_fin_fun,Module.finrank_self] at hRank
  change Module.finrank ℝ S = r-1
  rw [hspan]
  omega

/-- The same profile serves as the projection of the corresponding unit
coordinate onto the centered profile space. -/
theorem barycentric_dot (hr : 0 < r) (x j : Fin r) :
    dot (barycentricProfile x) (barycentricProfile j) = basis j x - 1/(r:ℝ) := by
  unfold dot
  simp only [barycentricProfile,mul_sub,sub_mul,sum_sub_distrib]
  rw [←sum_mul,←mul_sum, sum_basis,sum_basis]
  have hunit : (∑ i, basis x i * basis j i) = basis j x := dot_basis x (basis j)
  rw [hunit]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [(Nat.cast_ne_zero.mpr hr.ne' : (r:ℝ) ≠ 0)]
  <;> ring

theorem barycentric_energy (hr : 0 < r) (j : Fin r) :
    energy (barycentricProfile j) = 1-1/(r:ℝ) := by
  simpa [energy,dot,pow_two,basis] using barycentric_dot hr j j

theorem barycentric_row_allowance_sq (hr : 1 ≤ r) (j : Fin r) :
    energy (barycentricProfile j) * (2*Real.sqrt (1-1/(r:ℝ)))^2 * (4*((r-1:ℕ):ℝ)) =
      (4*(Real.sqrt (((r-1 : ℕ):ℝ)))*((r-1:ℕ):ℝ)/(r:ℝ))^2 := by
  have hpos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hroot : 0 ≤ 1-1/(r:ℝ) := by
    exact sub_nonneg.mpr ((div_le_iff₀ hpos).mpr (by simpa using h1))
  rw [barycentric_energy (by omega), show (2*Real.sqrt (1-1/(r:ℝ)))^2 = 4*(1-1/(r:ℝ)) by
    rw [mul_pow,Real.sq_sqrt hroot]; norm_num,div_pow]
  simp only [mul_pow,Nat.cast_sub hr,Nat.cast_one]
  rw [Real.sq_sqrt (show 0 ≤ (r:ℝ)-1 by linarith)]
  field_simp

set_option maxHeartbeats 1000000 in
theorem exists_barycentric_coordinates (hr : 0 < r) :
    ∃ z : Fin r → Fin (r-1) → ℝ,
      (∀ j, energy (z j) = 1-1/(r:ℝ)) ∧
      ∀ x j, dot (z x) (z j) = basis j x - 1/(r:ℝ) := by
  let S := Submodule.span ℝ (Set.range (@barycentricProfile r))
  let e := (WithLp.linearEquiv 2 ℝ (Fin r → ℝ)).symm
  let T : Submodule ℝ (EuclideanSpace ℝ (Fin r)) := S.map e.toLinearMap
  have hRank : Module.finrank ℝ T = r-1 := (e.finrank_map_eq S).trans (barycentric_span_finrank hr)
  let p (j : Fin r) : T := ⟨e (barycentricProfile j),⟨barycentricProfile j,Submodule.subset_span ⟨j,rfl⟩,rfl⟩⟩
  let b := (stdOrthonormalBasis ℝ T).reindex (finCongr hRank)
  let z (j : Fin r) (i : Fin (r-1)) : ℝ := b.repr (p j) i
  have hDot (x j : Fin r) : dot (z x) (z j) = dot (barycentricProfile x) (barycentricProfile j) := by
    have hh := b.repr.inner_map_map (p x) (p j)
    rw [Submodule.coe_inner] at hh
    simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real] at hh
    change (∑ i, z j i * z x i) =
      ∑ i, barycentricProfile j i * barycentricProfile x i at hh
    simpa only [dot,mul_comm] using hh
  refine ⟨z,?_,fun x j => (hDot x j).trans (barycentric_dot hr x j)⟩
  intro j
  simpa [energy,dot,pow_two,basis] using (hDot j j).trans (barycentric_dot hr j j)

noncomputable def barycentricAllowance (r : ℕ) : ℝ :=
  4*Real.sqrt (((r-1:ℕ):ℝ))*((r-1:ℕ):ℝ)/(r:ℝ)

/-- The centered rows of Section 4.2 can use the projected allowance
in a single recoloring. Isolated vertices do not constrain the profiles. -/
theorem exists_barycentric_recolour_with_reserves {V : Type*} [Fintype V] [DecidableEq V]
    {M : SimpleGraph.MultiGraph V} {k : ℕ} (C : M.EdgeColoring k) (hr : 1 ≤ r)
    (group : V → Fin r) (actual : Fin r → V → ℝ) (q bound : ℝ) (charge : Fin r → ℝ)
    (hrep : ∀ x v, M.degree v ≠ 0 → actual x v = q + basis (group v) x)
    (hequal : ∀ i j, C.colourMass i = C.colourMass j)
    (hbudget : ∀ x, (k:ℝ)*(bound+(k-1:ℕ)*charge x)+(k-1:ℕ)*barycentricAllowance r ≤
      (k:ℝ)*(∑ v,actual x v) - ∑ v,actual x v*(M.degree v:ℝ)) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ x i, bound+(k-1:ℕ)*charge x ≤ uncoveredWeight D (actual x) i := by
  obtain ⟨z,hEnergy,hDot⟩ := exists_barycentric_coordinates (by omega : 0 < r)
  have hpos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hOne : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hRoot : 0 ≤ 1-1/(r:ℝ) := sub_nonneg.mpr ((div_le_iff₀ hpos).mpr (by simpa using hOne))
  apply exists_vector_recolour_with_exact_reserves C (z ∘ group) z actual
    (fun _ => q+1/(r:ℝ)) charge (Real.sqrt (1-1/(r:ℝ))) bound
    (fun _ => barycentricAllowance r) 0
  · exact Real.sqrt_nonneg _
  · intro x; unfold barycentricAllowance; positivity
  · intro v
    rw [Function.comp_apply,hEnergy,Real.sq_sqrt hRoot]
  · intro x v hv
    rw [hrep x v hv,Function.comp_apply,hDot]
    ring
  · intro i j
    simp [hequal i j]
  · intro x
    have hh := barycentric_row_allowance_sq hr x
    rw [barycentric_energy (by omega)] at hh
    simpa [hEnergy,barycentricAllowance,mul_assoc] using hh.le
  · intro x
    simpa using hbudget x

end WeightedPaper.Examples

#print axioms WeightedPaper.Examples.barycentric_span_finrank
#print axioms WeightedPaper.Examples.barycentric_energy
#print axioms WeightedPaper.Examples.barycentric_row_allowance_sq
#print axioms WeightedPaper.Examples.exists_barycentric_coordinates
#print axioms WeightedPaper.Examples.exists_barycentric_recolour_with_reserves
