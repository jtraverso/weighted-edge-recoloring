import WeightedPaper.VectorSparsity

namespace WeightedPaper
open Finset
open scoped Classical

variable {J : Type*} [Fintype J]

theorem energy_nonneg (v : J → ℝ) : 0 ≤ energy v := sum_nonneg (fun j _ => sq_nonneg (v j))

private theorem energy_eq_zero_pointwise {v : J → ℝ} (hv : energy v ≤ 0) (j : J) : v j = 0 := by
  have h : (v j)^2 ≤ energy v := single_le_sum (fun i _ => sq_nonneg (v i)) (mem_univ j)
  nlinarith

theorem energy_add_le {v w : J → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : energy v ≤ a^2) (hw : energy w ≤ b^2) :
    energy (fun j => v j + w j) ≤ (a+b)^2 := by
  rcases ha.eq_or_lt with hza|hpa
  · subst a
    have hz : ∀ j, v j = 0 := energy_eq_zero_pointwise (by simpa using hv)
    simpa [hz] using hw
  rcases hb.eq_or_lt with hzb|hpb
  · subst b
    have hz : ∀ j, w j = 0 := energy_eq_zero_pointwise (by simpa using hw)
    simpa [hz] using hv
  let dot := ∑ j, v j * w j
  have hc : (2*a*b) * dot ≤ b^2 * energy v + a^2 * energy w := by
    simp only [energy,dot,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro j _
    nlinarith [sq_nonneg (b*v j-a*w j)]
  have hd : dot ≤ a*b := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hv (sq_nonneg b))
      (mul_le_mul_of_nonneg_left hw (sq_nonneg a))
    have hpos : 0 < 2*a*b := by positivity
    apply le_of_mul_le_mul_left _ hpos
    nlinarith only [hc,hh]
  have hh : energy (fun j => v j + w j) = energy v + 2*dot + energy w := by
    simp only [energy,dot,mul_sum,←sum_add_distrib]
    exact sum_congr rfl (fun j _ => by ring)
  rw [hh]
  nlinarith only [hd,hv,hw]

theorem energy_sum_le {I : Type*} (S : Finset I) (v : I → J → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hv : ∀ i ∈ S, energy (v i) ≤ R^2) :
    energy (fun j => ∑ i ∈ S, v i j) ≤ (S.card * R)^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [energy]
  | insert a S ha ih =>
    have hS := ih (fun i hi => hv i (mem_insert_of_mem hi))
    have hA := energy_add_le hR (mul_nonneg (Nat.cast_nonneg _) hR)
      (hv a (mem_insert_self _ _)) hS
    simp only [sum_insert ha,card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    convert hA using 1 <;> ring

variable {I : Type*} {n : ℕ}

/-- One free sign for each even component and for each pair with opposite
surplus. The fixed vector is the sum of the remaining positive components. -/
private structure Grouping (S : Finset I) (δ : I → ℝ) (w : I → Fin n → ℝ)
    (d R : ℝ) where
  free : Finset I
  subset : free ⊆ S
  vectors : I → Fin n → ℝ
  fixed : Fin n → ℝ
  fixed_bound : energy fixed ≤ (d*R)^2
  free_bound : ∀ i ∈ free, energy (vectors i) ≤ (2*R)^2
  orient : ∀ q : I → ℝ, (∀ i ∈ free, q i = 1 ∨ q i = -1) →
    ∃ T ⊆ S, (∑ i ∈ T,δ i) = 0 ∧
      ∀ j, (∑ i ∈ S,w i j)-2*(∑ i ∈ T,w i j) = fixed j + ∑ i ∈ free,q i * vectors i j

private theorem group_components (S : Finset I) (δ : I → ℝ) (w : I → Fin n → ℝ)
    (d R : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hδ : ∀ i ∈ S, δ i = 0 ∨ δ i = 1 ∨ δ i = -1)
    (hsum : (∑ i ∈ S,δ i) = d) (hw : ∀ i ∈ S, energy (w i) ≤ R^2) :
    Nonempty (Grouping S δ w d R) := by
  classical
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hm : ∃ b ∈ S, δ b = -1
  · obtain ⟨b,hb,hδb⟩ := hm
    have hp : ∃ a ∈ S, δ a = 1 := by
      by_contra! hnone
      have hnonpos : ∀ i ∈ S, δ i ≤ 0 := by
        intro i hi
        rcases hδ i hi with he|he|he
        · simp [he]
        · exact (hnone i hi he).elim
        · linarith
      have hneg : (∑ i ∈ S,δ i) < 0 := by
        rw [← sum_erase_add S δ hb,hδb]
        have he : (∑ i ∈ S.erase b,δ i) ≤ 0 := sum_nonpos (fun i hi => hnonpos i (mem_erase.mp hi).2)
        linarith
      linarith
    obtain ⟨a,ha,hδa⟩ := hp
    have hab : a ≠ b := by intro h; subst b; linarith
    let E := (S.erase a).erase b
    have hba : b ∈ S.erase a := mem_erase.mpr ⟨hab.symm,hb⟩
    have hES : E ⊆ S := (erase_subset _ _).trans (erase_subset _ _)
    have hnotA : a ∉ E := fun h => (mem_erase.mp (mem_erase.mp h).2).1 rfl
    have hnotB : b ∉ E := notMem_erase _ _
    have hES' : E ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hES,fun h => hnotA (h.symm ▸ ha)⟩
    have split (v : I → ℝ) : (∑ i ∈ S,v i) = (∑ i ∈ E,v i)+v a+v b := by
      have h1 := sum_erase_add S v ha
      have h2 := sum_erase_add (S.erase a) v hba
      change (∑ i ∈ E,v i)+v b = _ at h2
      linarith
    have hE : (∑ i ∈ E,δ i) = d := by rw [split δ,hδa,hδb] at hsum; linarith
    obtain ⟨G⟩ := ih E hES' (fun i hi => hδ i (hES hi)) hE (fun i hi => hw i (hES hi))
    let F := insert a G.free
    let vec := Function.update G.vectors a (fun j => w a j + w b j)
    have hn : a ∉ G.free := fun h => hnotA (G.subset h)
    have hvec (i : I) (hi : i ∈ G.free) : vec i = G.vectors i := by
      have h : i ≠ a := fun h => hn (h ▸ hi)
      simp [vec,Function.update_of_ne h]
    have hva : vec a = fun j => w a j + w b j := by simp [vec]
    refine ⟨⟨F,insert_subset ha (G.subset.trans hES),vec,G.fixed,G.fixed_bound,?_,?_⟩⟩
    · intro i hi
      rcases mem_insert.mp hi with he|hi
      · subst i
        rw [hva]
        simpa only [two_mul] using energy_add_le hR hR (hw a ha) (hw b hb)
      · rw [hvec i hi]
        exact G.free_bound i hi
    · intro q hq
      obtain ⟨T,hTE,ht,hT⟩ := G.orient q (fun i hi => hq i (mem_insert_of_mem hi))
      have hta : a ∉ T := fun h => hnotA (hTE h)
      have htb : b ∉ T := fun h => hnotB (hTE h)
      have pair_sum (v : I → ℝ) : (∑ i ∈ insert a (insert b T), v i) =
          v a + v b + ∑ i ∈ T,v i := by
        rw [sum_insert (by simp [hab,hta]),sum_insert htb]
        ring
      have free_sum (j : Fin n) : (∑ i ∈ F,q i * vec i j) =
          q a * (w a j + w b j) + ∑ i ∈ G.free,q i * G.vectors i j := by
        rw [sum_insert hn,hva]
        rw [sum_congr rfl (fun i hi => by rw [hvec i hi])]
      rcases hq a (mem_insert_self a G.free) with hq₁|hq₁
      · refine ⟨T,hTE.trans hES,ht,?_⟩
        intro j
        rw [split (fun i => w i j),free_sum j,hq₁]
        linarith only [hT j]
      · refine ⟨insert a (insert b T),insert_subset ha (insert_subset hb (hTE.trans hES)),?_,?_⟩
        · rw [pair_sum δ,hδa,hδb,ht]
          norm_num
        · intro j
          rw [split (fun i => w i j),pair_sum (fun i => w i j),free_sum j,hq₁]
          linarith only [hT j]
  · let E := S.filter fun i => δ i = 0
    let P := S.filter fun i => δ i ≠ 0
    have hp (i : I) (hi : i ∈ P) : δ i = 1 := by
      rcases hδ i (mem_filter.mp hi).1 with he|he|he
      · exact ((mem_filter.mp hi).2 he).elim
      · exact he
      · exact (hm ⟨i,(mem_filter.mp hi).1,he⟩).elim
    have hsplit (v : I → ℝ) : (∑ i ∈ E,v i)+(∑ i ∈ P,v i)=∑ i ∈ S,v i :=
      sum_filter_add_sum_filter_not S _ _
    have hP : (P.card : ℝ) = d := by
      rw [← hsplit δ,sum_eq_zero (fun i hi => (mem_filter.mp hi).2),zero_add,
        sum_congr rfl hp] at hsum
      simpa using hsum
    let f : Fin n → ℝ := fun j => ∑ i ∈ P,w i j
    have hf : energy f ≤ (d*R)^2 := by
      rw [← hP]
      exact energy_sum_le P w R hR (fun i hi => hw i (mem_filter.mp hi).1)
    refine ⟨⟨E,filter_subset _ _,w,f,hf,
      fun i hi => (hw i (mem_filter.mp hi).1).trans (by nlinarith),
      ?_⟩⟩
    intro q hq
    let T := E.filter fun i => q i = -1
    refine ⟨T,(filter_subset _ _).trans (filter_subset _ _),?_,?_⟩
    · exact sum_eq_zero (fun i hi => (mem_filter.mp (mem_filter.mp hi).1).2)
    · intro j
      rw [← hsplit (fun i => w i j)]
      have hsign : (∑ i ∈ E,q i * w i j) = (∑ i ∈ E,w i j) - 2 * ∑ i ∈ T,w i j := by
        have ht := sum_filter (s := E) (p := fun i => q i = -1) (f := fun i => w i j)
        rw [show T = E.filter _ from rfl,ht,mul_sum,← sum_sub_distrib]
        apply sum_congr rfl
        intro i hi
        rcases hq i hi with he|he <;> norm_num [he] <;> ring
      dsimp only [f]
      linarith only [hsign]

/-- The two-colour component signing with exact fixed size difference. -/
theorem exists_vector_component_swaps (S : Finset I) (δ : I → ℝ) (w : I → Fin n → ℝ)
    (d R : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hδ : ∀ i ∈ S, δ i = 0 ∨ δ i = 1 ∨ δ i = -1)
    (hsum : (∑ i ∈ S,δ i) = d) (hw : ∀ i ∈ S, energy (w i) ≤ R^2) :
    ∃ T ⊆ S, (∑ i ∈ T,δ i) = 0 ∧
      energy (fun j => (∑ i ∈ S,w i j)-2*(∑ i ∈ T,w i j)) ≤
        (d*R)^2 + n * (2*R)^2 := by
  obtain ⟨G⟩ := group_components S δ w d R hd hR hδ hsum hw
  obtain ⟨q,hq,hqB⟩ := exists_euclidean_sign_balance G.free n G.vectors G.fixed
    ((2*R)^2) (sq_nonneg _) G.free_bound
  obtain ⟨T,hT,hTδ,hTeq⟩ := G.orient q hq
  have he := congrArg energy (funext hTeq)
  exact ⟨T,hT,hTδ,he.trans_le (hqB.trans (add_le_add_left G.fixed_bound _))⟩

end WeightedPaper
