import WeightedPaper.Cut.GridHost
namespace WeightedPaper.Examples.Grid
open Finset
variable {q : ℕ}

def diagonalEmb (π : Equiv.Perm (Fin q)) : (Fin q × Copy) ↪ Ord q where
  toFun z := (z.1,π z.1,z.2)
  inj' := fun x y h => Prod.ext (congrArg (fun z : Ord q => z.1) h) (congrArg (fun z : Ord q => z.2.2) h)
def diagonal (π : Equiv.Perm (Fin q)) := univ.map (diagonalEmb π)

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

theorem diagonal_witness (hq : 64 ≤ q) :
    ∃ Z : Finset (Ord q), degree q ≤ Z.card ∧
      ∀ y, (Z.filter fun x => adjacent x y).card ≤ 1024 := by
  letI : NeZero q := ⟨by omega⟩
  letI : Fact (1 < q) := ⟨by omega⟩
  let π : Equiv.Perm (Fin q) := Equiv.addRight 1
  let ι := Equiv.refl (Fin q)
  have dis : Disjoint (diagonal ι) (diagonal π) := by
    apply disjoint_left.mpr
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
    simp only [degree,diagonal,card_map,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  · intro y
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add (diagonal_neighbors ι y) (diagonal_neighbors π y))

theorem separation (hq : 64 ≤ q) (a k : ℕ) (hpal : order q ≤ k*a) :
    ¬ DenseCut ((host q).cap false true) (exSet (Fin q) (Ord q) false)
      (exSet (Fin q) (Ord q) true) (q+order q) a k ∧
    ¬ RobustCut ((host q).cap false true) (exSet (Fin q) (Ord q) false)
      (exSet (Fin q) (Ord q) true) a k := by
  letI : NeZero q := ⟨by omega⟩
  let v : Ord q := (0,0,false,false,0)
  have hsl := (slack hq).2
  constructor
  · have h := (host q).not_dense_of_ordinary_upper Bool.false_ne_true a k (degree q) v
      (support_degree v).le (by simp only [card_ord,Fintype.card_fin]; unfold order at hsl; omega)
    simpa only [Fintype.card_fin,card_ord,order] using h
  · rintro ⟨ρ,τ,hr,hk,hd,_,hex⟩
    have ht := hd (ordEmb false v) (ordEmb_not_mem_exSet false v)
    have hcount := ((host q).ordinaryNeighbours_compl Bool.false_ne_true v).trans (support_degree v)
    simp only [ordinary_complement] at ht hcount hex
    have ht' : τ ≤ degree q := by
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

end WeightedPaper.Examples.Grid
