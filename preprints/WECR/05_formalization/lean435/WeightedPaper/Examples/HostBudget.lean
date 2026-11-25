import WeightedPaper.Examples.HostCut

namespace WeightedPaper.Examples

open Finset SimpleGraph
open scoped Classical

variable {X O : Type*} [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O]

@[simp] theorem exEmb_mem_exSet (b : Bool) (x : X) : exEmb (O:=O) b x ∈ exSet X O b :=
  mem_map.mpr ⟨x,mem_univ _,rfl⟩

@[simp] theorem ordEmb_not_mem_exSet (b : Bool) (y : O) : ordEmb (X:=X) b y ∉ exSet X O b := by
  apply mem_compl.mp
  rw [exSet_compl]
  exact mem_map.mpr ⟨y,mem_univ _,rfl⟩

noncomputable def exEquiv (b : Bool) : X ≃ exSet X O b :=
  Equiv.ofBijective (fun x => ⟨exEmb b x,exEmb_mem_exSet b x⟩)
    ⟨fun _ _ h => (exEmb b).injective (congrArg Subtype.val h),fun ⟨v,hv⟩ => by
      obtain ⟨x,_,rfl⟩ := mem_map.mp hv
      exact ⟨x,Subtype.ext rfl⟩⟩

/-- Extend an ordinary profile by zero outside its part. -/
def onOrd (X : Type*) (b : Bool) {Z : Type*} [Zero Z] (f : O → Z) (v : Vertex X O) : Z :=
  if v.1 = b then v.2.elim (fun _ => 0) f else 0

theorem sum_onOrd (b : Bool) (f : O → ℝ) : ∑ v, onOrd X b f v = ∑ y, f y := by
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  cases b <;> simp [onOrd,Fintype.sum_sum_type]

def liftCharge (b : Bool) (f : X → ℝ) (x : half X O b) : ℝ := x.val.2.elim f (fun _ => 0)

def liftWeight (b c : Bool) (w : X → O → ℝ) (x : half X O b) (y : half X O c) : ℝ :=
  x.val.2.elim (fun e => y.val.2.elim (fun _ => 0) (w e)) (fun _ => 0)

@[simp] theorem liftWeight_apply (b c : Bool) (w : X → O → ℝ) (x : X) (y : O) :
    liftWeight b c w (exEmb b x) (ordEmb c y) = w x y := rfl

theorem incidenceWeight_lift (b c : Bool) (w : X → O → ℝ) (x : X) (v : Vertex X O) :
    incidenceWeight (half X O c) (liftWeight b c w) (exSet X O c) (exEmb b x) v =
      onOrd X c (w x) v := by
  rcases v with ⟨b',x'|y⟩
  · by_cases hc : b' = c
    · subst b'
      simp [incidenceWeight,onOrd,show (⟨(c,.inl x'),(mem_half _ _).mpr rfl⟩ : half X O c) =
        exEmb c x' from rfl]
    · simp [incidenceWeight,onOrd,hc]
  · by_cases hc : b' = c
    · subst b'
      simp [incidenceWeight,onOrd,show (⟨(c,.inr y),(mem_half _ _).mpr rfl⟩ : half X O c) =
        ordEmb c y from rfl]
    · simp [incidenceWeight,onOrd,hc]

structure HostBudget (P : Host X O) (k d : ℕ) where
  weight : X → O → ℝ
  charge : X → ℝ
  bound : ℝ
  σ : ℕ
  bound_pos : 0 < bound
  charge_nonneg : ∀ x, 0 ≤ charge x
  capacity : ∀ x y, 0 ≤ weight x y ∧ weight x y ≤ charge x * P.incidence x y
  column : ∀ y, (∑ x, weight x y) ≤ bound
  internal_degree : ∀ y, (∑ z, P.internal y z) ≤ σ
  balance :
    (∃ R : ℝ, ∃ t : O → ℝ, ∃ u : X → ℝ,
      0 ≤ R ∧ (∀ y, 0 ≤ t y ∧ t y ≤ R) ∧ (∀ x, 0 ≤ u x) ∧
      (∀ x y, t y*u x = weight x y) ∧
      ∀ x, (k : ℝ)*(bound+(k-1 : ℕ)*charge x)+(k-1 : ℕ)*(2*R*u x) ≤
        ((k : ℝ)-σ)*(∑ y,weight x y))
    ∨ (∃ n : ℕ, ∃ R H : ℝ, ∃ w : O → Fin n → ℝ, ∃ u : X → Fin n → ℝ, ∃ center : X → ℝ,
      0 ≤ R ∧ 0 ≤ H ∧ (∀ y, energy (w y) ≤ R^2) ∧
      (∀ x, energy (u x) ≤ 1) ∧ (2*R)^2*((d : ℝ)^2+4*n) ≤ H^2 ∧
      (∀ x y, weight x y = center x + dot (u x) (w y)) ∧
      ∀ x, (k : ℝ)*(bound+(k-1 : ℕ)*charge x)+(k-1 : ℕ)*(H+2*|center x| *d) ≤
        ((k : ℝ)-σ)*(∑ y,weight x y))

noncomputable def HostBudget.lift {P : Host X O} {k d : ℕ} (B : HostBudget P k d)
    {b c : Bool} (hbc : b ≠ c) :
    IncidenceBudget P.graph (half X O c) (P.cap b c) (exSet X O b) (exSet X O c) k d := by
  classical
  refine ⟨liftWeight b c B.weight,liftCharge b B.charge,B.bound,B.σ,B.bound_pos,?_,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨e,_,rfl⟩ := mem_map.mp hx
    exact B.charge_nonneg e
  · intro x hx y hy
    obtain ⟨e,_,rfl⟩ := mem_map.mp hx
    obtain ⟨o,rfl⟩ := exists_ord_of_not_ex hy
    simp only [Host.capInc P hbc,liftWeight_apply]
    exact B.capacity e o
  · intro y hy
    obtain ⟨o,rfl⟩ := exists_ord_of_not_ex hy
    rw [exSet,sum_map]
    exact B.column o
  · intro y hy
    obtain ⟨o,rfl⟩ := exists_ord_of_not_ex hy
    simp only [ordEmb_val,Host.degree_restricted,if_pos rfl,Fintype.sum_sum_type,
      Host.inside,sum_const_zero,zero_add]
    exact B.internal_degree o
  · let e : X ≃ exSet X O b := exEquiv b
    have hsum (x : X) :
      (∑ v, incidenceWeight (half X O c) (liftWeight b c B.weight) (exSet X O c) (exEmb b x) v) =
        ∑ y, B.weight x y := by simp_rw [incidenceWeight_lift,sum_onOrd]
    rcases B.balance with h|h
    · obtain ⟨R,t,u,hR,ht,hu,he,hbud⟩ := h
      left
      refine ⟨R,onOrd X c t, u ∘ e.symm,hR,?_,fun x => hu (e.symm x),?_,?_⟩
      · rintro ⟨c',x|y⟩ <;> by_cases hh : c' = c <;> simp [onOrd,hh,hR,ht]
      · intro x v
        obtain ⟨a,rfl⟩ := e.surjective x
        have hv : (e a).val = exEmb (O:=O) b a := rfl
        rw [hv,incidenceWeight_lift]
        change onOrd X c t v * u (e.symm (e a)) = _
        rw [e.symm_apply_apply]
        rcases v with ⟨c',x|y⟩ <;> by_cases hh : c' = c <;> simp [onOrd,hh,he]
      · intro x
        obtain ⟨a,rfl⟩ := e.surjective x
        change (k : ℝ)*(B.bound+(k-1 : ℕ)*B.charge a)+(k-1 : ℕ)*(2*R*u (e.symm (e a))) ≤
          ((k : ℝ)-B.σ)*(∑ v, incidenceWeight (half X O c) (liftWeight b c B.weight) (exSet X O c)
            (exEmb b a) v)
        rw [e.symm_apply_apply,hsum]
        exact hbud a
    · obtain ⟨n,R,H,w,u,center,hR,hH,hw,hu,hHs,he,hbud⟩ := h
      right
      refine ⟨n,R,H,onOrd X c w,u ∘ e.symm,center ∘ e.symm,hR,hH,?_,
        fun x => hu (e.symm x),hHs,?_,?_⟩
      · rintro ⟨c',x|y⟩ <;> by_cases hh : c' = c <;>
          simp [onOrd,hh,hw,energy,sq_nonneg] <;> exact hw _
      · intro x v hv
        obtain ⟨a,rfl⟩ := e.surjective x
        have hx : (e a).val = exEmb (O:=O) b a := rfl
        rw [hx,incidenceWeight_lift]
        simp only [Function.comp_apply,e.symm_apply_apply]
        rcases v with ⟨c',x|y⟩
        · exfalso
          apply hv
          rw [P.degree_restricted]
          simp [Host.inside]
        · have hcc : c' = c := by
            by_contra h
            exact hv (by simp [P.degree_restricted,h])
          subst c'
          simpa [onOrd] using he a y
      · intro x
        obtain ⟨a,rfl⟩ := e.surjective x
        change (k : ℝ)*(B.bound+(k-1 : ℕ)*B.charge a)+(k-1 : ℕ)*(H+2*|center (e.symm (e a))| *d) ≤
          ((k : ℝ)-B.σ)*(∑ v, incidenceWeight (half X O c) (liftWeight b c B.weight) (exSet X O c)
            (exEmb b a) v)
        rw [e.symm_apply_apply,hsum]
        exact hbud a

theorem Host.finish (P : Host X O) (D k a : ℕ) (hk : k ≤ D)
    (hreg : P.graph.IsRegularOfDegree D)
    (hcap : (P.graph.restrict (half X O false)).edgeCount ≤ k*a)
    (hA : Nonempty ((P.graph.restrict (half X O false)).EdgeColoring k))
    (hB : Nonempty ((P.graph.restrict (half X O true)).EdgeColoring k))
    (budget : HostBudget P k (equitableGap k (P.graph.restrict (half X O false)).edgeCount))
    (hcut : DenseCut (P.cap false true) (exSet X O false) (exSet X O true)
          (Fintype.card X + Fintype.card O) a k ∨
      RobustCut (P.cap false true) (exSet X O false) (exSet X O true) a k) :
    ∃ F : P.graph.EdgeColoring D, F.IsFactorization := by
  let L := half X O false
  have hm : L.card = Fintype.card X + Fintype.card O := side_card false
  have hcompl : Lᶜ = half X O true := half_compl false
  have bw : (fun (y : half X O true) (x : L) => P.graph.mult s(x.val,y.val)) = P.cap true false := by
    funext y x
    rw [Host.cap,Sym2.eq_swap]
  have hgo (T : Finset (Vertex X O)) (hT : T = Lᶜ)
      (Y : Finset T) (hB : Nonempty ((P.graph.restrict T).EdgeColoring k))
      (hTsize : T.card = Fintype.card X + Fintype.card O)
      (A : IncidenceBudget P.graph T (fun (x : L) y => P.graph.mult s(x.val,y.val)) (exSet X O false) Y
        k (equitableGap k (P.graph.restrict L).edgeCount))
      (B : IncidenceBudget P.graph L (fun (y : T) x => P.graph.mult s(x.val,y.val)) Y (exSet X O false)
        k (equitableGap k (P.graph.restrict L).edgeCount))
      (cut : DenseCut (fun (x : L) (y : T) => P.graph.mult s(x.val,y.val)) (exSet X O false) Y
          (Fintype.card X + Fintype.card O) a k ∨
        RobustCut (fun (x : L) (y : T) => P.graph.mult s(x.val,y.val)) (exSet X O false) Y a k) :
      ∃ F : P.graph.EdgeColoring D, F.IsFactorization := by
    subst T
    exact exists_factorization_of_weighted_cut P.graph L D k _ a hk hreg (exSet X O false)
      Y hm hTsize hcap hA hB A B cut
  exact hgo _ hcompl.symm _ hB (side_card true) (budget.lift Bool.false_ne_true)
    (bw.symm ▸ budget.lift (by decide : true ≠ false)) hcut

end WeightedPaper.Examples
