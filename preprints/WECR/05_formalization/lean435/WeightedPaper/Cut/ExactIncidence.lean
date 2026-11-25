import WeightedPaper.Incidence
import WeightedPaper.Cut.ExactReserves

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V A : Type*} [Fintype V] [DecidableEq V]

/-- The linear and scalar representations in the reserve inequalities.
The vector branch accepts a separate projection allowance for each row. -/
structure ExactIncidenceBudget (M : MultiGraph V) (T : Finset V) (cap : A → T → ℕ)
    (X : Finset A) (Y : Finset T) (k d : ℕ) where
  weight : A → T → ℝ
  charge : A → ℝ
  bound : ℝ
  bound_pos : 0 < bound
  charge_nonneg : ∀ x ∈ X, 0 ≤ charge x
  capacity : ∀ x ∈ X, ∀ y ∉ Y, 0 ≤ weight x y ∧ weight x y ≤ charge x * cap x y
  column : ∀ y ∉ Y, (∑ x ∈ X, weight x y) ≤ bound
  balance :
    (∃ R : ℝ, ∃ t : V → ℝ, ∃ u : X → ℝ,
      0 ≤ R ∧ (∀ v, 0 ≤ t v ∧ t v ≤ R) ∧ (∀ x, 0 ≤ u x) ∧
      (∀ x : X, ∀ v, t v*u x = incidenceWeight T weight Y x.val v) ∧
      ∀ x : X, (k : ℝ) * (bound+(k-1 : ℕ)*charge x.val)+(k-1 : ℕ)*(2*R*u x) ≤
        (k : ℝ)*(∑ v,incidenceWeight T weight Y x.val v) -
        ∑ v,incidenceWeight T weight Y x.val v * ((M.restrict T).degree v:ℝ))
    ∨ (∃ n : ℕ, ∃ R : ℝ, ∃ H : X → ℝ, ∃ w : V → Fin n → ℝ, ∃ u : X → Fin n → ℝ, ∃ center : X → ℝ,
      0 ≤ R ∧ (∀ x, 0 ≤ H x) ∧ (∀ v, energy (w v) ≤ R^2) ∧
      (∀ x, energy (u x)*((2*R)^2*((d : ℝ)^2+4*n)) ≤ (H x)^2) ∧
      (∀ x : X, ∀ v, (M.restrict T).degree v ≠ 0 →
        incidenceWeight T weight Y x.val v = center x + dot (u x) (w v)) ∧
      ∀ x : X, (k : ℝ) * (bound+(k-1 : ℕ)*charge x.val)+(k-1 : ℕ)*(H x+2*|center x| *d) ≤
        (k : ℝ)*(∑ v,incidenceWeight T weight Y x.val v) -
        ∑ v,incidenceWeight T weight Y x.val v * ((M.restrict T).degree v:ℝ))

theorem ExactIncidenceBudget.exists_recolour {M : MultiGraph V} {T : Finset V}
    {cap : A → T → ℕ} {X : Finset A} {Y : Finset T} {k d : ℕ}
    (P : ExactIncidenceBudget M T cap X Y k d) (C : (M.restrict T).EdgeColoring k)
    (heq : ∀ i j, C.colourMass i ≤ C.colourMass j + 1)
    (hd : ∀ i j, C.colourMass i ≤ C.colourMass j + d) :
    ∃ D : (M.restrict T).EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
    ∀ (x : X) i, P.bound+(k-1 : ℕ)*P.charge x.val ≤
      ∑ y ∈ (missingOn D T i).filter (· ∉ Y), P.weight x.val y := by
  classical
  let W (x : X) := incidenceWeight T P.weight Y x.val
  have hres (D : (M.restrict T).EdgeColoring k)
      (h : ∀ (x : X) i, P.bound+(k-1 : ℕ)*P.charge x.val ≤ uncoveredWeight D (W x) i) :
      ∀ (x : X) i, P.bound+(k-1 : ℕ)*P.charge x.val ≤
        ∑ y ∈ (missingOn D T i).filter (· ∉ Y), P.weight x.val y := by
    intro x i
    rw [← uncoveredWeight_incidence D]
    exact h x i
  rcases P.balance with hs|hv
  · obtain ⟨R,t,u,hR,ht,hu,hEq,hb⟩ := hs
    obtain ⟨D,hD,h⟩ := exists_rank_one_recolour_with_exact_reserves C t u (fun x => P.charge x.val)
      R P.bound hR (fun v => (ht v).1) (fun v => (ht v).2) hu heq
      (fun x => by simp_rw [hEq x]; exact hb x)
    refine ⟨D,hD,hres D (fun x i => ?_)⟩
    simpa only [hEq x] using h x i
  · obtain ⟨n,R,H,w,u,center,hR,hH,hw,hHsq,hEq,hb⟩ := hv
    obtain ⟨D,hD,h⟩ := exists_vector_recolour_with_exact_reserves C w u W center
      (fun x => P.charge x.val) R P.bound H d hR hH hw hEq hd hHsq hb
    exact ⟨D,hD,hres D h⟩

/-- The original uniform budget is an instance of the exact row budget. -/
noncomputable def IncidenceBudget.toExact {M : MultiGraph V} {T : Finset V}
    {cap : A → T → ℕ} {X : Finset A} {Y : Finset T} {k d : ℕ}
    (P : IncidenceBudget M T cap X Y k d) : ExactIncidenceBudget M T cap X Y k d := by
  refine ⟨P.weight,P.charge,P.bound,P.bound_pos,P.charge_nonneg,P.capacity,P.column,?_⟩
  have hDebit (x : X) :
      ((k:ℝ)-P.σ)*(∑ v,incidenceWeight T P.weight Y x.val v) ≤
        (k:ℝ)*(∑ v,incidenceWeight T P.weight Y x.val v) -
          ∑ v,incidenceWeight T P.weight Y x.val v * ((M.restrict T).degree v:ℝ) := by
    have h : (∑ v,incidenceWeight T P.weight Y x.val v * ((M.restrict T).degree v:ℝ)) ≤
        (∑ v,incidenceWeight T P.weight Y x.val v) * (P.σ:ℝ) := by
      rw [sum_mul]
      apply sum_le_sum
      intro v _
      unfold incidenceWeight
      split_ifs with hv hy
      · simp
      · exact mul_le_mul_of_nonneg_left (by exact_mod_cast P.internal_degree ⟨v,hv⟩ hy)
          ((P.capacity x.val x.2 ⟨v,hv⟩ hy).1)
      · simp
    linarith only [h]
  rcases P.balance with h|h
  · obtain ⟨R,t,u,hR,ht,hu,hEq,hBudget⟩ := h
    exact Or.inl ⟨R,t,u,hR,ht,hu,hEq,fun x => (hBudget x).trans (hDebit x)⟩
  · obtain ⟨n,R,H,w,u,center,hR,hH,hw,hu,hsq,hEq,hBudget⟩ := h
    refine Or.inr ⟨n,R,fun _ => H,w,u,center,hR,fun _ => hH,hw,?_,hEq,fun x => (hBudget x).trans (hDebit x)⟩
    intro x
    exact (mul_le_mul_of_nonneg_right (hu x) (by positivity)).trans (by simpa using hsq)

end WeightedPaper

#print axioms WeightedPaper.ExactIncidenceBudget.exists_recolour
#print axioms WeightedPaper.IncidenceBudget.toExact
