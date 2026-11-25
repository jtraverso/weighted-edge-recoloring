import WeightedPaper.Cut.GridFactorization
import WeightedPaper.Cut.GridSeparation

namespace WeightedPaper.Examples.GridRange
open Finset SimpleGraph Grid
open scoped Classical
variable {q : ℕ}

theorem slack (hq : 46 ≤ q) : Grid.degree q+q+2 ≤ order q ∧ 2*Grid.degree q ≤ order q := by
  unfold Grid.degree order
  have : 2*q-1+1=2*q := by omega
  constructor <;> nlinarith [Nat.mul_le_mul_right q hq]

theorem regular (hq : 46 ≤ q) : (host q).graph.IsRegularOfDegree (order q) := by
  apply (host q).regular
  · intro x
    change (∑ _ : Fin q,0)+(∑ y : Ord q,if x=y.1 then q else 0)=_
    rw [sum_coords]
    simp only [sum_const_zero,zero_add]
    change (∑ i : Fin q,∑ _ : Fin q,∑ _ : Copy,if x=i then q else 0) = 256*q^2
    simp only [sum_const,card_univ,card_copy,Fintype.card_fin,nsmul_eq_mul,
      ← mul_sum,sum_ite_eq,mem_univ,if_true,Nat.cast_id]
    ring
  · intro x
    change (∑ y,internal x y)+(∑ i : Fin q,if i=x.1 then q else 0)+(∑ y,ordinary x y)=_
    rw [inside_degree]
    have hs : (∑ y : Ord q,if adjacent x y then 1 else 0) = Grid.degree q := by
      simpa only [card_filter,support_iff] using support_degree x
    simp only [ordinary,sum_add_distrib,hs,sum_ite_eq',sum_ite_eq,mem_univ,if_true]
    have := (slack hq).1
    omega

noncomputable def row_budget (hq : 46 ≤ q) : HostBudget (host q) (16*q) 0 := by
  let w (i : Fin q) (y : Ord q) : ℝ := if i=y.1 then 1 else 0
  have hq' : 46 ≤ (q:ℝ) := by exact_mod_cast hq
  have hrow (x : Fin q) : (∑ y,w x y) = 256*(q:ℝ) := by
    rw [sum_coords]
    change (∑ i : Fin q,∑ _ : Fin q,∑ _ : Copy,if x=i then (1:ℝ) else 0) = _
    simp only [sum_const,card_univ,card_copy,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
      ← mul_sum,sum_ite_eq,mem_univ,if_true,mul_one]
    ring
  refine ⟨w,fun _ => 1,1,2,by norm_num,fun _ => by norm_num,?_,?_,fun x => (inside_degree x).le,?_⟩
  · intro x y
    change 0 ≤ w x y ∧ w x y ≤ 1*( (if x=y.1 then q else 0 : ℕ) : ℝ)
    by_cases he : x=y.1 <;> simp [w,he] <;> linarith
  · intro y; simp [w]
  · right
    refine ⟨q,1,4*Real.sqrt q,fun y => basis y.1,basis,fun _ => 0,by norm_num,by positivity,
      fun y => by simp [energy_basis],fun x => (energy_basis x).le,?_,?_,?_⟩
    · have hs := Real.sq_sqrt (show 0 ≤ (q:ℝ) by positivity)
      push_cast
      nlinarith
    · intro x y; simp [w,dot_basis,basis]
    · intro x
      rw [hrow]
      have he : 1 ≤ 16*q := by omega
      simp [Nat.cast_sub he]
      have hs : Real.sqrt q ≤ (q:ℝ) := by
        nlinarith [Real.sq_sqrt (show 0≤(q:ℝ) by positivity),sq_nonneg (Real.sqrt q-1)]
      nlinarith [mul_nonneg (show 0≤16*(q:ℝ)-1 by linarith) (sub_nonneg.mpr hs),
        mul_nonneg (show 0≤(q:ℝ)-1 by linarith) (show 0≤(q:ℝ) by positivity)]

noncomputable def spectral (hq : 46 ≤ q) :
    SpectralCut ((host q).cap false true) (exSet (Fin q) (Ord q) false)
      (exSet (Fin q) (Ord q) true) (16*q) (16*q) := by
  have hd := (slack hq).2
  refine ⟨order q,Grid.degree q,by rw [ordinary_complement,card_ordSet,card_ord]; rfl,by rw [ordinary_complement,card_ordSet,card_ord]; rfl,
    by simp,by omega,by unfold Grid.degree; omega,by simp [Grid.degree]; omega,?_,?_,?_⟩
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    have h := ((host q).ordinaryNeighbours_compl Bool.false_ne_true x).trans (support_degree x)
    simpa only [ordinary_complement] using h
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    have h := ((host q).ordinaryNeighbours_compl' Bool.false_ne_true x).trans (support_degree x)
    simpa only [ordinary_complement] using h
  · intro u v hu hv
    simp only [ordinary_complement,ordSet,sum_map,incidence,Host.capOrd _ Bool.false_ne_true] at hv ⊢
    change 4*(∑ x,u (ordEmb false x)*(∑ y,v (ordEmb true y)*(if 0<ordinary x y then 1 else 0)))^2 ≤ _
    simp only [support_iff]
    have h := bilinear_bound (by omega : 2≤q) (fun x => u (ordEmb false x))
      (fun y => v (ordEmb true y)) hv
    simpa only [applySupport,Grid.degree,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (by omega : 1 ≤ 2*q),
      Nat.cast_one] using h

theorem factorization (hq : 46 ≤ q) :
    ∃ F : (host q).graph.EdgeColoring (order q), F.IsFactorization := by
  have he : order q = (16*q)*(16*q) := by unfold order; ring
  have hk : 1 ≤ 16*q := by omega
  have hcol (b : Bool) : Nonempty (((host q).graph.restrict (half (Fin q) (Ord q) b)).EdgeColoring (16*q)) := by
    apply (host q).colourable_inside b _ (fun x => x.2.2.1)
    · intro x y h
      change internal x y = 0
      simp [internal,quadInternal_zero _ _ h]
    · intro x
      change (∑ y,internal x y) ≤ 16*q
      rw [inside_degree]
      omega
  apply (host q).finishSpectral _ (16*q) (16*q) (by rw [he]; nlinarith)
    (regular hq) (by rw [internal_mass,he]) (hcol false) (hcol true)
  · rw [internal_mass,equitableGap,if_pos (show 16*q ∣ order q from ⟨16*q,he⟩)]
    exact row_budget hq
  · exact spectral hq

private theorem diagonal_neighbors (π : Equiv.Perm (Fin q)) (y : Ord q) :
    ((diagonal π).filter fun x => adjacent x y).card ≤ 512 := by
  rw [diagonal,filter_map,card_map,card_filter]
  let r := fun x : Fin q × Copy => if x.1=y.1 then 1 else 0
  let c := fun x : Fin q × Copy => if x.1=π.symm y.2.1 then 1 else 0
  have bound : (∑ x : Fin q × Copy, if adjacent (diagonalEmb π x) y then 1 else 0) ≤
      ∑ x,(r x+c x) := by
    apply sum_le_sum
    intro x _
    change (if x.1=y.1 ∨ π x.1=y.2.1 then 1 else 0) ≤ _
    by_cases hi : x.1=y.1 <;> by_cases hj : x.1=π.symm y.2.1 <;>
      simp [r,c,π.apply_eq_iff_eq_symm_apply,hi,hj]
  have hline (a : Fin q) : (∑ x : Fin q × Copy, if x.1=a then 1 else 0 : ℕ)=256 := by
    rw [Fintype.sum_prod_type]
    change (∑ i : Fin q,∑ _ : Copy, if i=a then (1:ℕ) else 0) = 256
    simp only [sum_const,card_univ,card_copy,nsmul_eq_mul,← mul_sum,sum_ite_eq',mem_univ,if_true,mul_one,Nat.cast_id]
  rw [sum_add_distrib,show (∑ x,r x)=256 from hline _,show (∑ x,c x)=256 from hline _] at bound
  exact bound

theorem diagonal_witness (hq : 46 ≤ q) :
    ∃ Z : Finset (Ord q), Grid.degree q ≤ Z.card ∧
      ∀ y, (Z.filter fun x => adjacent x y).card ≤ 1024 := by
  letI : NeZero q := ⟨by omega⟩
  letI : Fact (1 < q) := ⟨by omega⟩
  let π : Equiv.Perm (Fin q) := Equiv.addRight 1
  let ι := Equiv.refl (Fin q)
  have dis : Disjoint (diagonal ι) (diagonal π) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,_,rfl⟩ := mem_map.mp hx
    obtain ⟨v,_,hv⟩ := mem_map.mp hy
    have h₁ : v.1 = u.1 := congrArg (fun z : Ord q => z.1) hv
    have h₂ : v.1+1 = u.1 := congrArg (fun z : Ord q => z.2.1) hv
    have : (1 : Fin q)=0 := by simpa using (add_left_cancel (a:=v.1) (show v.1+1=v.1+0 by simpa [h₁] using h₂))
    have v := congrArg Fin.val this
    have h1 : (1 : Fin q).val = 1 := by change (1:ℕ) % q = 1; exact Nat.mod_eq_of_lt (by omega : (1:ℕ) < q)
    rw [h1] at v
    exact Nat.one_ne_zero v
  refine ⟨diagonal ι ∪ diagonal π,?_,?_⟩
  · rw [card_union_of_disjoint dis]
    simp only [Grid.degree,diagonal,card_map,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  · intro y
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add (diagonal_neighbors ι y) (diagonal_neighbors π y))

theorem separation (hq : 46 ≤ q) (a k : ℕ) (hpal : order q ≤ k*a) :
    ¬ DenseCut ((host q).cap false true) (exSet (Fin q) (Ord q) false)
      (exSet (Fin q) (Ord q) true) (q+order q) a k ∧
    ¬ RobustCut ((host q).cap false true) (exSet (Fin q) (Ord q) false)
      (exSet (Fin q) (Ord q) true) a k := by
  letI : NeZero q := ⟨by omega⟩
  let v : Ord q := (0,0,false,false,0)
  have hsl := (slack hq).2
  constructor
  · have h := (host q).not_dense_of_ordinary_upper Bool.false_ne_true a k (Grid.degree q) v
      (support_degree v).le (by simp only [card_ord,Fintype.card_fin]; unfold order at hsl; omega)
    simpa only [Fintype.card_fin,card_ord,order] using h
  · rintro ⟨ρ,τ,hr,hk,hd,_,hex⟩
    have ht := hd (ordEmb false v) (ordEmb_not_mem_exSet false v)
    have hcount := ((host q).ordinaryNeighbours_compl Bool.false_ne_true v).trans (support_degree v)
    simp only [ordinary_complement] at ht hcount hex
    have ht' : τ ≤ Grid.degree q := by
      have hh : τ ≤ ((ordSet (Fin q) (Ord q) true).filter
          fun y => 0 < (host q).cap false true (ordEmb false v) y).card :=
        (by omega : τ ≤ τ+(2*a+max (exSet (Fin q) (Ord q) false).card (exSet (Fin q) (Ord q) true).card)+(k-1)).trans ht
      exact hh.trans_eq hcount
    have hh : 1024 < ρ := by
      by_contra! hsmall
      have ha : 2*a ≤ ρ := by omega
      have hprod := Nat.mul_le_mul hk ha
      have hsq := Nat.mul_le_mul hsmall hsmall
      unfold order at hpal
      nlinarith [Nat.mul_le_mul hq hq]
    obtain ⟨Z,hZ,hNbr⟩ := diagonal_witness hq
    obtain ⟨T,hTZ,hT⟩ := exists_subset_card_eq (ht'.trans hZ)
    let S := T.map (ordEmb (X:=Fin q) false)
    have hS : S ⊆ (exSet (Fin q) (Ord q) false)ᶜ := by
      intro x hx
      obtain ⟨v,_,rfl⟩ := mem_map.mp hx
      exact mem_compl.mpr (ordEmb_not_mem_exSet _ _)
    have hsc : S.card=τ := (card_map _).trans hT
    have he := hex S (by simpa only [ordinary_complement] using hS) hsc.ge (by rw [hsc,card_ordSet,card_ord]; unfold order at hsl; omega)
    have hzero : (((exSet (Fin q) (Ord q) true)ᶜ).filter (fun y =>
      ρ ≤ (S.filter (fun x => 0 < (host q).cap false true x y)).card)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨y',rfl⟩ := exists_ord_of_not_ex (mem_compl.mp (mem_filter.mp hy).1)
      have hle := (mem_filter.mp hy).2
      have heq : (S.filter (fun x => 0 < (host q).cap false true x (ordEmb true y'))).card =
          (T.filter (fun x => adjacent x y')).card := by
        rw [show S=T.map _ from rfl,filter_map,card_map]
        simp [Function.comp_def,Host.capOrd _ Bool.false_ne_true,host,support_iff]
      rw [heq] at hle
      have := (card_le_card (filter_subset_filter (fun x => adjacent x y') hTZ)).trans (hNbr y')
      omega
    simp only [ordinary_complement] at hzero
    rw [hzero,card_empty] at he
    omega

end WeightedPaper.Examples.GridRange

#print axioms WeightedPaper.Examples.GridRange.factorization
#print axioms WeightedPaper.Examples.GridRange.separation
