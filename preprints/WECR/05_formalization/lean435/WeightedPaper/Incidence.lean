import WeightedPaper.Criterion
import WeightedPaper.RecolourToReserves
import OverfullWork.AlignedInternal

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V A : Type*} [Fintype V] [DecidableEq V]

/-- A row weight is zero on the other side of the cut and on exceptions. -/
noncomputable def incidenceWeight (T : Finset V) (weight : A → T → ℝ) (Y : Finset T)
    (x : A) (v : V) : ℝ :=
  if h : v ∈ T then
    if (⟨v,h⟩ : T) ∈ Y then 0 else weight x ⟨v,h⟩
  else 0

theorem incidenceWeight_nonneg (T : Finset V) (weight : A → T → ℝ) (Y : Finset T)
    (x : A) (hs : ∀ y ∉ Y, 0 ≤ weight x y) (v : V) :
    0 ≤ incidenceWeight T weight Y x v := by
  unfold incidenceWeight
  split_ifs with hv hY
  · exact le_rfl
  · exact hs ⟨v,hv⟩ hY
  · exact le_rfl

theorem incidenceWeight_eq_zero_of_out (T : Finset V) (weight : A → T → ℝ) (Y : Finset T)
    (x : A) {v : V} (hv : v ∉ T) :
    incidenceWeight T weight Y x v = 0 := by simp [incidenceWeight,hv]

theorem uncoveredWeight_incidence {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k)
    (T : Finset V) (weight : A → T → ℝ) (Y : Finset T) (x : A) (i : Fin k) :
    uncoveredWeight C (incidenceWeight T weight Y x) i =
      ∑ y ∈ (missingOn C T i).filter (· ∉ Y), weight x y := by
  classical
  let f (v : V) := if (C.colourGraph i).degree v = 0 then
    incidenceWeight T weight Y x v
    else 0
  unfold uncoveredWeight
  rw [sum_filter]
  change (∑ v,f v) = _
  calc
    _ = ∑ v ∈ T,f v := by
      symm
      apply sum_subset (subset_univ _)
      intro v _ hv
      simp [f,incidenceWeight,hv]
    _ = ∑ v : T,f v.val := (sum_attach T f).symm
    _ = _ := by
      unfold missingOn
      rw [filter_filter,sum_filter]
      apply sum_congr rfl
      intro y _
      have hy : y.val ∈ T := y.2
      by_cases hyY : y ∈ Y <;> by_cases hd : (C.colourGraph i).degree y.val = 0 <;>
        simp [f,incidenceWeight,hy,hyY,hd]

/-- The linear and scalar representations in the reserve inequalities.
In the vector branch, the coordinate basis can be chosen in the span
of the profiles. Row projections have norm at most one. -/
structure IncidenceBudget (M : MultiGraph V) (T : Finset V) (cap : A → T → ℕ)
    (X : Finset A) (Y : Finset T) (k d : ℕ) where
  weight : A → T → ℝ
  charge : A → ℝ
  bound : ℝ
  σ : ℕ
  bound_pos : 0 < bound
  charge_nonneg : ∀ x ∈ X, 0 ≤ charge x
  capacity : ∀ x ∈ X, ∀ y ∉ Y, 0 ≤ weight x y ∧ weight x y ≤ charge x * cap x y
  column : ∀ y ∉ Y, (∑ x ∈ X, weight x y) ≤ bound
  internal_degree : ∀ y : T, y ∉ Y → (M.restrict T).degree y.val ≤ σ
  balance :
    (∃ R : ℝ, ∃ t : V → ℝ, ∃ u : X → ℝ,
      0 ≤ R ∧ (∀ v, 0 ≤ t v ∧ t v ≤ R) ∧ (∀ x, 0 ≤ u x) ∧
      (∀ x : X, ∀ v, t v*u x = incidenceWeight T weight Y x.val v) ∧
      ∀ x : X, (k : ℝ) * (bound+(k-1 : ℕ)*charge x.val)+(k-1 : ℕ)*(2*R*u x) ≤
        ((k : ℝ)-σ)*(∑ v,incidenceWeight T weight Y x.val v))
    ∨ (∃ n : ℕ, ∃ R H : ℝ, ∃ w : V → Fin n → ℝ, ∃ u : X → Fin n → ℝ, ∃ center : X → ℝ,
      0 ≤ R ∧ 0 ≤ H ∧ (∀ v, energy (w v) ≤ R^2) ∧
      (∀ x, energy (u x) ≤ 1) ∧ (2*R)^2*((d : ℝ)^2+4*n) ≤ H^2 ∧
      (∀ x : X, ∀ v, (M.restrict T).degree v ≠ 0 →
        incidenceWeight T weight Y x.val v = center x + dot (u x) (w v)) ∧
      ∀ x : X, (k : ℝ) * (bound+(k-1 : ℕ)*charge x.val)+(k-1 : ℕ)*(H+2*|center x| *d) ≤
        ((k : ℝ)-σ)*(∑ v,incidenceWeight T weight Y x.val v))

theorem IncidenceBudget.exists_recolour {M : MultiGraph V} {T : Finset V}
    {cap : A → T → ℕ} {X : Finset A} {Y : Finset T} {k d : ℕ}
    (P : IncidenceBudget M T cap X Y k d) (C : (M.restrict T).EdgeColoring k)
    (heq : ∀ i j, C.colourMass i ≤ C.colourMass j + 1)
    (hd : ∀ i j, C.colourMass i ≤ C.colourMass j + d) :
    ∃ D : (M.restrict T).EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
    ∀ (x : X) i, P.bound+(k-1 : ℕ)*P.charge x.val ≤
      ∑ y ∈ (missingOn D T i).filter (· ∉ Y), P.weight x.val y := by
  classical
  let W (x : X) := incidenceWeight T P.weight Y x.val
  have hσ (v : V) (x : X) (h : W x v ≠ 0) : (M.restrict T).degree v ≤ P.σ := by
    have hv : v ∈ T := by
      by_contra hn
      exact h (incidenceWeight_eq_zero_of_out T P.weight Y x.val hn)
    let y : T := ⟨v,hv⟩
    have hn : y ∉ Y := by
      intro he
      apply h
      simp [W,incidenceWeight,hv,show (⟨v,hv⟩ : T) ∈ Y from he]
    exact P.internal_degree y hn
  have hres (D : (M.restrict T).EdgeColoring k)
      (h : ∀ (x : X) i, P.bound+(k-1 : ℕ)*P.charge x.val ≤ uncoveredWeight D (W x) i) :
      ∀ (x : X) i, P.bound+(k-1 : ℕ)*P.charge x.val ≤
        ∑ y ∈ (missingOn D T i).filter (· ∉ Y), P.weight x.val y := by
    intro x i
    rw [← uncoveredWeight_incidence D]
    exact h x i
  rcases P.balance with hs|hv
  · obtain ⟨R,t,u,hR,ht,hu,hEq,hb⟩ := hs
    -- With all projected rows zero the inequality is impossible if there
    -- is an exceptional row, by positivity of its column bound.
    by_cases hExists : ∃ x : X, u x ≠ 0
    · obtain ⟨x₀,hx₀⟩ := hExists
      have hT : ∀ v,t v ≠ 0 → (M.restrict T).degree v ≤ P.σ := by
        intro v hv
        apply hσ v x₀
        rw [show W x₀ v = t v*u x₀ from (hEq x₀ v).symm]
        exact mul_ne_zero hv hx₀
      obtain ⟨D,hD,h⟩ := exists_rank_one_recolour_with_reserves C t u (fun x => P.charge x.val)
        R P.bound P.σ hR (fun v => (ht v).1) (fun v => (ht v).2) hu heq hT
        (fun x => by simp_rw [hEq x]; exact hb x)
      refine ⟨D,hD,hres D (fun x i => ?_)⟩
      simpa only [hEq x] using h x i
    · refine ⟨C,fun _ => rfl,hres C (fun x i => ?_)⟩
      have h0 : u x = 0 := by by_contra h; exact hExists ⟨x,h⟩
      have hW : ∀ v, W x v = 0 := fun v => by rw [show W x v = t v*u x from (hEq x v).symm,h0,mul_zero]
      have hb' := hb x
      change _ ≤ ((k : ℝ)-P.σ)*(∑ v,W x v) at hb'
      simp only [hW,h0,mul_zero,sum_const_zero,add_zero] at hb'
      have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
      have hn := P.charge_nonneg x.val x.2
      have hc : 0 < P.bound+(k-1 : ℕ)*P.charge x.val :=
        add_pos_of_pos_of_nonneg P.bound_pos (mul_nonneg (Nat.cast_nonneg _) hn)
      exact (not_lt_of_ge hb' (mul_pos hk hc)).elim
  · obtain ⟨n,R,H,w,u,center,hR,hH,hw,hu,hHsq,hEq,hb⟩ := hv
    have hnonneg (x : X) (v : V) : 0 ≤ W x v :=
      incidenceWeight_nonneg T P.weight Y x.val (fun y hy => (P.capacity x.val x.2 y hy).1) v
    obtain ⟨D,hD,h⟩ := exists_vector_recolour_with_reserves C w u W center
      (fun x => P.charge x.val) R H P.bound P.σ d hR hH hw hu hnonneg hEq hd hHsq
      (fun x v h => hσ v x h) hb
    exact ⟨D,hD,hres D h⟩

end WeightedPaper
