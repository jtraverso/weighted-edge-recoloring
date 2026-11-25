import WeightedPaper.Examples.Centered
import WeightedPaper.RobustCut

namespace WeightedPaper.Examples
open Finset
open scoped Classical

/-- The alternate certificate for §4.2 works on the actual centered host
with every exceptional-to-ordinary certificate weight equal to one. -/
theorem centredHost_indicator_budget {r q gap : ℕ} (hr : 8 ≤ r) (hq : 2 ≤ q) :
    ∃ B : HostBudget (centredHost r q) 4 gap, ∀ x y, B.weight x y = 1 := by
  let weight : Fin r → Quad (Fin r) → ℝ := fun _ _ => 1
  have hbound : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine ⟨⟨weight,fun _ => 1,r,2,hbound,fun _ => zero_le_one,?_,?_,?_,?_⟩,fun _ _ => rfl⟩
  · intro x y
    have hc : 1 ≤ centredCopies q x y := by unfold centredCopies; omega
    refine ⟨zero_le_one, ?_⟩
    change (1:ℝ) ≤ 1*(centredCopies q x y : ℝ)
    rw [one_mul]
    exact_mod_cast hc
  · intro y
    simp [weight]
  · intro y
    exact (quadInternal_degree y).le
  · left
    refine ⟨1,fun _ => 1,fun _ => 1,zero_le_one,fun _ => ⟨zero_le_one,le_rfl⟩,
      fun _ => zero_le_one,fun _ _ => one_mul _,?_⟩
    intro x
    have hr' : (8:ℝ) ≤ r := by exact_mod_cast hr
    simp [weight]
    linarith

end WeightedPaper.Examples

namespace WeightedPaper
/-- The quantitative contradiction for a deficient pair. The mixing
hypothesis is in squared, denominator-free form. -/
theorem spectral_deficit_impossible {N d h p s t e : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hdN : d ≤ N)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (hcost : 8*(h+p) ≤ d)
    (hs : d-h-p < s) (ht : d-h-p < t) (hsum : N-h < s+t)
    (hspent : e ≤ p*min s t)
    (hmix : 4*(N*e-d*s*t)^2 ≤ d^2*s*t*((N-s)*(N-t))) : False := by
  have hs' : 7*d < 8*s := by linarith
  have ht' : 7*d < 8*t := by linarith
  have hmax : 7*N < 16*max s t := by
    have := le_max_left s t
    have := le_max_right s t
    linarith
  have hmin : 7*d < 8*min s t := by
    rcases le_total s t with h|h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hprod := mul_lt_mul_of_pos_right hmin (by linarith : 0 < 16*max s t)
  have hprod' := mul_lt_mul_of_pos_left hmax (by linarith : 0 < 7*d)
  have hsm : min s t * max s t = s*t := min_mul_max _ _
  have hst : 49*(d*N) < 128*(s*t) := by nlinarith only [hprod,hprod',hsm]
  have hsmall := mul_le_mul_of_nonneg_left (show 8*h ≤ d by linarith) hN.le
  have hcom := mul_lt_mul_of_pos_left hsum hN
  have hpos : 0 < s*t := mul_pos (by linarith) (by linarith)
  have hratio : 9*((N-s)*(N-t)) < 16*(s*t) := by nlinarith only [hst,hsmall,hcom,hpos]
  have hbound := mul_le_mul_of_nonneg_left hspent hN.le
  have hpN : 7*(N*p) ≤ 2*d*max s t := by
    nlinarith only [mul_le_mul_of_nonneg_left (show 8*p ≤ d by linarith) hN.le,
      mul_lt_mul_of_pos_left hmax hd]
  have hpst := mul_le_mul_of_nonneg_right hpN (show 0 ≤ min s t by apply le_min <;> linarith)
  have he : 3*(N*e) < d*(s*t) := by
    nlinarith only [hbound,hpst,hsm, mul_pos hd hpos,
      congrArg (fun z : ℝ => d*z) hsm]
  have he' : 4*(d*(s*t))^2 < (3*(d*s*t-N*e))^2 :=
    by nlinarith only [sq_lt_sq' (show -(3*(d*s*t-N*e)) < 2*(d*(s*t)) by
                                    nlinarith only [he,mul_pos hd hpos])
                                  (show 2*(d*(s*t)) < 3*(d*s*t-N*e) by linarith)]
  have hr := mul_lt_mul_of_pos_left hratio (mul_pos (sq_pos_of_pos hd) hpos)
  nlinarith only [hmix, he',hr]

end WeightedPaper

namespace WeightedPaper
open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

private theorem deficient_size {U : Finset A} {W : Finset B} {X : Finset A}
    (R : A → B → Prop) (S : Finset A) (hS : S ⊆ U) (d c p : ℕ)
    (hsmall : ∀ Q ⊆ U.filter (· ∈ X),
      Q.card ≤ (W.filter fun y => ∃ x ∈ Q, R x y).card)
    (hdeg : ∀ x ∈ U, x ∉ X → d-c-p ≤ (W.filter (R x)).card)
    (hbad : (W.filter fun y => ∃ x ∈ S, R x y).card < S.card) :
    d < (S\X).card + X.card+c+p := by
  classical
  by_cases h : S ⊆ X
  · exact False.elim (Nat.not_lt_of_ge (hsmall S (fun x hx => mem_filter.mpr ⟨hS hx,h hx⟩)) hbad)
  obtain ⟨x,hx,hX⟩ := not_subset.mp h
  have hs := hdeg x (hS hx) hX
  have hn : (W.filter (R x)).card ≤ (W.filter fun y => ∃ x ∈ S, R x y).card :=
    card_le_card (fun y hy => mem_filter.mpr ⟨(mem_filter.mp hy).1,x,hx,(mem_filter.mp hy).2⟩)
  have := card_sdiff_add_card_inter S X
  have := card_le_card (inter_subset_right (s₁:=S) (s₂:=X))
  omega

set_option maxHeartbeats 650000 in
/-- A squared mixing inequality for the original simple support, applied
only to ordinary subsets. The capacity and spending are integer copies. -/
theorem matching_of_mixing (U X : Finset A) (W Y : Finset B)
    (cap loss : A → B → ℕ) (N d a p r : ℕ)
    (hU : U.card + 2*a = N+r) (hW : W.card + 2*a = N+r)
    (hX : X.card = r) (hY : Y.card = r)
    (hd : 0 < d) (hdN : d ≤ N) (hcost : 8*(2*a+r+p) ≤ d)
    (hrow : ∀ x, (∑ y,loss x y) ≤ p) (hcol : ∀ y, (∑ x,loss x y) ≤ p)
    (hdegA : ∀ x ∈ U, x ∉ X → d-2*a-p ≤ (W.filter fun y => 0 < cap x y-loss x y).card)
    (hdegB : ∀ y ∈ W, y ∉ Y → d-2*a-p ≤ (U.filter fun x => 0 < cap x y-loss x y).card)
    (hexA : ∀ S ⊆ U.filter (· ∈ X),
      S.card ≤ (W.filter fun y => ∃ x ∈ S, 0 < cap x y-loss x y).card)
    (hexB : ∀ T ⊆ W.filter (· ∈ Y),
      T.card ≤ (U.filter fun x => ∃ y ∈ T, 0 < cap x y-loss x y).card)
    (hmix : ∀ S ⊆ Xᶜ, ∀ T ⊆ Yᶜ,
      let s : ℝ := S.card
      let t : ℝ := T.card
      let e : ℝ := ∑ x ∈ S, ∑ y ∈ T, if 0 < cap x y then (1:ℝ) else 0
      4*((N:ℝ)*e-d*s*t)^2 ≤ (d:ℝ)^2*s*t*((N-s)*(N-t))) :
    ∃ f : U ≃ W, ∀ x : U, 0 < cap x (f x)-loss x (f x) := by
  classical
  let R := fun x y => 0 < cap x y-loss x y
  letI : DecidableRel R := fun x y => Classical.propDecidable (R x y)
  apply exists_equiv_of_finset_hall U W R (by omega)
  intro S hS
  let Z := W.filter fun y => ∃ x ∈ S, R x y
  let T := W\Z
  have hZ : Z ⊆ W := filter_subset _ _
  have hT : T ⊆ W := sdiff_subset
  change S.card ≤ Z.card
  by_contra! hbad
  have hcT : T.card + Z.card = W.card := by
    rw [show T.card = W.card-Z.card from card_sdiff_of_subset hZ]
    have := card_le_card hZ
    omega
  have hnone (x) (hx : x ∈ S) (y) (hy : y ∈ T) : ¬ R x y := fun h =>
    (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨hT hy,x,hx,h⟩)
  have hback : (U.filter fun x => ∃ y ∈ T, R x y) ⊆ U\S := by
    intro x hx
    obtain ⟨hU',y,hy,hxy⟩ := mem_filter.mp hx
    exact mem_sdiff.mpr ⟨hU',fun h => hnone x h y hy hxy⟩
  have htbad := card_le_card hback
  rw [card_sdiff_of_subset hS] at htbad
  have hsc := deficient_size (X:=X) (W:=W) R S hS d (2*a) p (by
    intro Q hQ
    convert hexA Q hQ using 2 <;> ext z <;> simp [R]) (by
    intro x hx hn
    convert hdegA x hx hn using 2 <;> ext z <;> simp [R]) hbad
  have htc := deficient_size (X:=Y) (W:=U) (fun y x => R x y) T hT d (2*a) p (by
    intro Q hQ
    convert hexB Q hQ using 2 <;> ext z <;> simp [R]) (by
    intro y hy hn
    convert hdegB y hy hn using 2 <;> ext z <;> simp [R]) (by
    have hs' := card_le_card hS
    have he : (U.filter fun x => ∃ y ∈ T, R x y).card < T.card := by omega
    convert he using 2 <;> ext z <;> simp)
  let L := S\X
  let J := T\Y
  have hL : L ⊆ Xᶜ := fun _ hx => mem_compl.mpr (mem_sdiff.mp hx).2
  have hJ : J ⊆ Yᶜ := fun _ hy => mem_compl.mpr (mem_sdiff.mp hy).2
  have hsum : N < (2*a+r) + L.card+J.card := by
    have := card_sdiff_add_card_inter S X
    have := card_sdiff_add_card_inter T Y
    have := card_le_card (inter_subset_right (s₁:=S) (s₂:=X))
    have := card_le_card (inter_subset_right (s₁:=T) (s₂:=Y))
    dsimp [L,J]
    omega
  let edge := fun x y => if 0 < cap x y then (1:ℕ) else 0
  have hle (x) (hx : x ∈ L) (y) (hy : y ∈ J) : edge x y ≤ loss x y := by
    have hh := hnone x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1
    dsimp [R] at hh
    dsimp [edge]
    split_ifs <;> omega
  let E := ∑ x ∈ L, ∑ y ∈ J, edge x y
  have hspent : E ≤ p*min L.card J.card := by
    have ha : E ≤ ∑ _x ∈ L,p := sum_le_sum fun x hx =>
      (sum_le_sum (hle x hx)).trans ((sum_le_univ_sum_of_nonneg (fun y => Nat.zero_le (loss x y))).trans (hrow x))
    have hb : E ≤ ∑ _y ∈ J,p := by
      dsimp [E]
      rw [sum_comm]
      exact sum_le_sum fun y hy =>
        (sum_le_sum (fun x hx => hle x hx y hy)).trans
          ((sum_le_univ_sum_of_nonneg (fun x => Nat.zero_le (loss x y))).trans (hcol y))
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at ha hb
    rcases le_total L.card J.card with h|h
    · simpa only [min_eq_left h,Nat.mul_comm] using ha
    · simpa only [min_eq_right h,Nat.mul_comm] using hb
  have hm := hmix L hL J hJ
  have ee : (E:ℝ) = ∑ x ∈ L, ∑ y ∈ J, if 0 < cap x y then (1:ℝ) else 0 := by
    simp [E,edge,Nat.cast_ite]
  apply spectral_deficit_impossible (N:=(N:ℝ)) (d:=(d:ℝ)) (h:=((2*a+r:ℕ):ℝ))
    (p:=(p:ℝ)) (s:=(L.card:ℝ)) (t:=(J.card:ℝ)) (e:=(E:ℝ))
  · exact_mod_cast (show 0 < N by omega)
  · exact_mod_cast hd
  · exact_mod_cast hdN
  · positivity
  · positivity
  · exact_mod_cast hcost
  · have hh : d < L.card+(2*a+r)+p := by dsimp [L]; omega
    have : (d:ℝ) < L.card+((2*a+r:ℕ):ℝ)+p := by exact_mod_cast hh
    linarith only [this]
  · have hh : d < J.card+(2*a+r)+p := by dsimp [J]; omega
    have : (d:ℝ) < J.card+((2*a+r:ℕ):ℝ)+p := by exact_mod_cast hh
    linarith only [this]
  · have : (N:ℝ) < ((2*a+r:ℕ):ℝ)+L.card+J.card := by exact_mod_cast hsum
    linarith only [this]
  · exact_mod_cast hspent
  · rw [ee]
    exact hm

end WeightedPaper
