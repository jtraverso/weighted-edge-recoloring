import WeightedPaper.Blocks.BlockExample
import WeightedPaper.Blocks.BlockRelabel
import WeightedPaper.Examples.Host

namespace WeightedPaper.Blocks.Example

open Finset SimpleGraph
open scoped Classical

abbrev Vertex (n : ℕ) := Bool × Side n

variable {n : ℕ}

def chosen (b : Bool) : Index n := if b then first else second

def markedAt (j : Index n) : Ord n → Prop
  | (i,.inl _) => i = j
  | (_, .inr _) => False

instance (j : Index n) (o : Ord n) : Decidable (markedAt j o) := by
  rcases o with ⟨i,e|e⟩ <;> unfold markedAt <;> infer_instance

def inside (j : Index n) : Side n → Side n → ℕ
  | .inr (i,.inl e), .inr (i',.inl f) => if i = j ∧ i' = j ∧ e ≠ f then 1 else 0
  | _, _ => 0

theorem inside_symm (j : Index n) (x y : Side n) : inside j x y = inside j y x := by
  rcases x with e|⟨i,e|e⟩ <;> rcases y with f|⟨i',f|f⟩ <;> simp [inside,and_comm,and_left_comm,and_assoc,ne_comm]

theorem inside_diag (j : Index n) (x : Side n) : inside j x x = 0 := by
  rcases x with e|⟨i,e|e⟩ <;> simp [inside]

def degree (n : ℕ) : ℕ := 2*((n+2)*(2*n+6))+(n+1)+1
def slack (n : ℕ) : ℕ := degree n - (2*n+6) - 4 - (n+1)

private theorem arithmetic (n : ℕ) : (2*n+6)+4+slack n+(n+1)=degree n := by
  have h : (2*n+6)+4+(n+1) ≤ degree n := by unfold degree; nlinarith
  unfold slack
  omega

/-- Capacities at the cut, with a diagonal adjustment that pays for the
internal edge or the extra incidence to an exceptional vertex. -/
def capacity : Side n → Side n → ℕ
  | .inl e, .inl f => if e = f then 1 else 0
  | .inl e, .inr o => 2 + if o = (first,.inl e) then n+1 else 0
  | .inr o, .inl f => 2 + if o = (second,.inl f) then n+1 else 0
  | .inr o, .inr p =>
    (if o.1 = p.1 then 1 else 0) +
      if o = p then slack n + (if markedAt first o ∨ markedAt second o then 0 else n+1) else 0

theorem ordinary_capacity (x y : Ord n) :
    0 < capacity (.inr x) (.inr y) ↔ x.1 = y.1 := by
  by_cases h : x.1 = y.1
  · simp [capacity,h]
  · have hn : x ≠ y := fun he => h (congrArg Prod.fst he)
    simp [capacity,h,hn]

theorem capA (e : Bool) (o : Ord n) : 0 < capacity (.inl e) (.inr o) := by
  simp [capacity]
theorem capB (e : Bool) (o : Ord n) : 0 < capacity (.inr o) (.inl e) := by
  simp [capacity]

private theorem card_copy : Fintype.card (Copy n) = 2*n+6 := by simp [Fintype.card_sum]; omega
private theorem card_ord : Fintype.card (Ord n) = (n+2)*(2*n+6) := by
  rw [Fintype.card_prod,card_copy,Fintype.card_fin]

private theorem inside_sum (j : Index n) (o : Ord n) :
    (∑ y : Side n, inside j (.inr o) y) = if markedAt j o then 1 else 0 := by
  rcases o with ⟨i,e|e⟩
  · by_cases hi : i = j
    · subst i
      have he (y : Side n) : inside j (.inr (j,.inl e)) y =
          if y = .inr (j,.inl (!e)) then 1 else 0 := by
        rcases y with f|⟨l,f|f⟩ <;> try cases f <;> cases e <;> simp [inside,Prod.mk.injEq]
      simp only [he,markedAt,if_true,sum_ite_eq',mem_univ]
    · have he (y : Side n) : inside j (.inr (i,.inl e)) y = 0 := by
        rcases y with f|⟨l,f|f⟩ <;> simp [inside,hi]
      simp [he,markedAt,hi]
  · simp [inside,markedAt]

private theorem inc_sum (j : Index n) (o : Ord n) :
    (∑ e : Bool, (2 + if o = (j,.inl e) then n+1 else 0)) =
      4 + if markedAt j o then n+1 else 0 := by
  rcases o with ⟨i,e|e⟩
  · cases e <;> by_cases hi : i = j <;> simp [markedAt,hi,Prod.mk.injEq] <;> omega
  · simp [markedAt]

private theorem ex_inc_sum (j : Index n) (e : Bool) :
    (∑ o : Ord n, (2 + if o = (j,.inl e) then n+1 else 0)) = 2*((n+2)*(2*n+6))+(n+1) := by
  rw [sum_add_distrib,sum_const,card_univ,card_ord,nsmul_eq_mul,sum_ite_eq']
  simp only [mem_univ,if_true,Nat.cast_id]
  omega

private theorem ordinary_sum (o : Ord n) :
    (∑ p : Ord n, capacity (.inr o) (.inr p)) =
      (2*n+6)+slack n+(if markedAt first o ∨ markedAt second o then 0 else n+1) := by
  have hb : (∑ p : Ord n, if o.1 = p.1 then (1:ℕ) else 0) = 2*n+6 := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ j : Index n, if o.1 = j then 2*n+6 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases h : o.1 = j
        · rw [if_pos h]
          simp only [h,if_true,sum_const,card_univ,card_copy,nsmul_eq_mul,mul_one,Nat.cast_id]
        · simp [h]
      _ = _ := by simp
  simp only [capacity,sum_add_distrib,hb,sum_ite_eq,mem_univ,if_true]
  omega

private theorem ordinary_sum_rev (o : Ord n) :
    (∑ p : Ord n, capacity (.inr p) (.inr o)) =
      (2*n+6)+slack n+(if markedAt first o ∨ markedAt second o then 0 else n+1) := by
  rw [← ordinary_sum o]
  apply sum_congr rfl
  intro p _
  by_cases h : p = o
  · subst p
    rfl
  · simp [capacity,h,Ne.symm h,eq_comm]

def unitAdj (v w : Vertex n) : ℕ :=
  if v.1 = w.1 then inside (chosen v.1) v.2 w.2 else 0

def adj (v w : Vertex n) : ℕ :=
  if v.1 = w.1 then (n+1)*inside (chosen v.1) v.2 w.2 else
    if v.1 then capacity v.2 w.2 else capacity w.2 v.2

private theorem unitAdj_symm (v w : Vertex n) : unitAdj v w = unitAdj w v := by
  by_cases h : v.1 = w.1
  · simp only [unitAdj,h,if_true,inside_symm (chosen w.1) v.2 w.2]
  · simp [unitAdj,h,Ne.symm h]

private theorem adj_symm (v w : Vertex n) : adj v w = adj w v := by
  rcases v with ⟨b,v⟩
  rcases w with ⟨c,w⟩
  cases b <;> cases c <;> simp [adj,inside_symm]

def graph (n : ℕ) : MultiGraph (Vertex n) where
  mult := Sym2.lift ⟨adj,adj_symm⟩
  loopless e he := by
    induction e using Sym2.inductionOn with
    | hf v w =>
      obtain rfl := Sym2.mk_isDiag_iff.mp he
      change adj v v = 0
      simp [adj,inside_diag]

private def unitGraph (n : ℕ) : MultiGraph (Vertex n) where
  mult := Sym2.lift ⟨unitAdj,unitAdj_symm⟩
  loopless e he := by
    induction e using Sym2.inductionOn with
    | hf v w =>
      obtain rfl := Sym2.mk_isDiag_iff.mp he
      change unitAdj v v = 0
      simp [unitAdj,inside_diag]

private theorem ordinary_total (b : Bool) (o : Ord n) :
    (n+1)*(if markedAt (chosen b) o then 1 else 0) +
      (4 + if markedAt (chosen (!b)) o then n+1 else 0) +
      ((2*n+6)+slack n+(if markedAt first o ∨ markedAt second o then 0 else n+1)) = degree n := by
  have hd := arithmetic n
  have noneBoth : ¬ (markedAt (first : Index n) o ∧ markedAt second o) := by
    rcases o with ⟨i,e|e⟩
    · intro h
      exact different (h.1.symm.trans h.2)
    · simp [markedAt]
  by_cases h₀ : markedAt (first : Index n) o <;> by_cases h₁ : markedAt (second : Index n) o <;>
    cases b <;> simp only [chosen,Bool.not_false,Bool.not_true, Bool.false_eq_true,if_true,if_false,
      h₀,h₁,false_or,true_or,or_false,Nat.mul_zero,Nat.mul_one] <;> first | omega | exact (noneBoth ⟨h₀,h₁⟩).elim

private theorem cross_from_sum (v : Side n) :
    (∑ w : Side n, capacity v w) = v.elim (fun _ => degree n)
      (fun o => (4 + if markedAt second o then n+1 else 0) +
        ((2*n+6)+slack n+(if markedAt first o ∨ markedAt second o then 0 else n+1))) := by
  rw [Fintype.sum_sum_type]
  cases v with
  | inl e =>
    change (∑ f : Bool, if e = f then 1 else 0) +
      (∑ o : Ord n, (2 + if o = (first,.inl e) then n+1 else 0)) = degree n
    rw [sum_ite_eq,ex_inc_sum]
    simp only [mem_univ,if_true]
    unfold degree
    omega
  | inr o =>
    change (∑ f : Bool, (2 + if o = (second,.inl f) then n+1 else 0)) +
      (∑ w : Ord n, capacity (.inr o) (.inr w)) = _
    rw [inc_sum,ordinary_sum]
    rfl

private theorem cross_to_sum (v : Side n) :
    (∑ w : Side n, capacity w v) = v.elim (fun _ => degree n)
      (fun o => (4 + if markedAt first o then n+1 else 0) +
        ((2*n+6)+slack n+(if markedAt first o ∨ markedAt second o then 0 else n+1))) := by
  rw [Fintype.sum_sum_type]
  cases v with
  | inl e =>
    change (∑ f : Bool, if f = e then 1 else 0) +
      (∑ o : Ord n, (2 + if o = (second,.inl e) then n+1 else 0)) = degree n
    rw [sum_ite_eq',ex_inc_sum]
    simp only [mem_univ,if_true]
    unfold degree
    omega
  | inr o =>
    change (∑ f : Bool, (2 + if o = (first,.inl f) then n+1 else 0)) +
      (∑ w : Ord n, capacity (.inr w) (.inr o)) = _
    rw [inc_sum,ordinary_sum_rev]
    rfl

theorem regular (n : ℕ) : (graph n).IsRegularOfDegree (degree n) := by
  rintro ⟨b,v⟩
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_prod_type,Fintype.sum_bool,add_comm]
  change (∑ w : Side n, adj (b,v) (false,w)) + ∑ w : Side n, adj (b,v) (true,w) = _
  cases b
  · change (∑ w : Side n, (n+1)*inside second v w) + ∑ w : Side n, capacity w v = _
    rw [← mul_sum,cross_to_sum]
    cases v with
    | inl e => simp [inside]
    | inr o =>
      rw [inside_sum]
      simpa [chosen,add_assoc] using ordinary_total false o
  · change (∑ w : Side n, capacity v w) + ∑ w : Side n, (n+1)*inside first v w = _
    rw [← mul_sum,cross_from_sum,add_comm]
    cases v with
    | inl e => simp [inside]
    | inr o =>
      rw [inside_sum]
      simpa [chosen,add_assoc] using ordinary_total true o

private theorem unit_degree (b : Bool) (v : Side n) :
    (unitGraph n).degree (b,v) = v.elim (fun _ => 0) (fun o => if markedAt (chosen b) o then 1 else 0) := by
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_prod_type,Fintype.sum_bool,add_comm]
  change (∑ w : Side n, unitAdj (b,v) (false,w)) + ∑ w : Side n, unitAdj (b,v) (true,w) = _
  cases b
  · change (∑ w : Side n, inside second v w) + (∑ _ : Side n, (0:ℕ)) = _
    rw [sum_const_zero,add_zero]
    cases v with
    | inl e => simp [inside]
    | inr o => exact inside_sum second o
  · change (∑ _ : Side n, (0:ℕ)) + (∑ w : Side n, inside first v w) = _
    rw [sum_const_zero,zero_add]
    cases v with
    | inl e => simp [inside]
    | inr o => exact inside_sum first o

def left (n : ℕ) : Finset (Vertex n) := Examples.half Bool (Ord n) true

noncomputable def seed (n : ℕ) : ((graph n).internalPart (left n)).EdgeColoring (n+1) where
  col e _ := (unitGraph n).mult e
  sum_col e := by
    induction e using Sym2.inductionOn with
    | hf v w =>
      rw [MultiGraph.internalPart_mult]
      change (∑ _ : Fin (n+1),unitAdj v w) =
        if (v ∈ left n ↔ w ∈ left n) then adj v w else 0
      have he : (v ∈ left n ↔ w ∈ left n) ↔ v.1 = w.1 := by
        simp only [left,Examples.mem_half]
        cases v.1 <;> cases w.1 <;> simp
      by_cases h : v.1 = w.1 <;> simp [he,unitAdj,adj,h]
  proper v _ := by
    rw [show (∑ e ∈ univ.filter (fun e : Sym2 (Vertex n) => v ∈ e), (unitGraph n).mult e) =
      (unitGraph n).degree v from rfl]
    obtain ⟨b,v⟩ := v
    rw [unit_degree]
    rcases v with e|o
    · simp
    · change (if markedAt (chosen b) o then 1 else 0) ≤ _
      split <;> omega

private theorem seed_missing (b : Bool) (v : Side n) (i : Fin (n+1)) :
    ((seed n).colourGraph i).degree (b,v) = 0 ↔ uncovered (chosen b) v := by
  change (unitGraph n).degree (b,v) = 0 ↔ _
  rw [unit_degree]
  rcases v with e|⟨j,e|e⟩
  · simp [uncovered]
  · by_cases h : j = chosen b <;> simp [uncovered,markedAt,h]
  · simp [uncovered,markedAt]

private def coordA (n : ℕ) : Side n ≃ (left n) := Examples.sideEquiv true
private def coordB (n : ℕ) : Side n ≃ (↥((left n)ᶜ : Finset (Vertex n))) :=
  (Examples.sideEquiv false).trans (Finset.equivOfEq (Examples.half_compl (X := Bool) (O := Ord n) true).symm)

private theorem map_freeA (i : Fin (n+1)) :
    (free first : Finset (Side n)).map (coordA n).toEmbedding = missingOn (seed n) (left n) i := by
  ext x
  obtain ⟨v,rfl⟩ := (coordA n).surjective x
  simp only [Equiv.toEmbedding_apply,mem_map,Equiv.apply_eq_iff_eq,exists_eq_right,mem_free,
    missingOn,mem_filter,mem_univ,true_and]
  exact (seed_missing true v i).symm

private theorem map_freeB (i : Fin (n+1)) :
    (free second : Finset (Side n)).map (coordB n).toEmbedding = missingOn (seed n) (left n)ᶜ i := by
  ext x
  obtain ⟨v,rfl⟩ := (coordB n).surjective x
  simp only [Equiv.toEmbedding_apply,mem_map,Equiv.apply_eq_iff_eq,exists_eq_right,mem_free,
    missingOn,mem_filter,mem_univ,true_and]
  exact (seed_missing false v i).symm

/-- Simple support of the multigraph, with multiplicities ignored. -/
def support (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := 0 < adj x y
  symm := ⟨fun x y h => by simpa only [adj_symm y x] using h⟩
  loopless := ⟨fun x h => by simp [adj,inside_diag] at h⟩

theorem connected (n : ℕ) : (support n).Connected := by
  let a : Vertex n := (true,.inl false)
  let b : Vertex n := (false,.inl false)
  let o : Ord n := (first,.inl false)
  have crossing (x y : Side n) (h : 0 < capacity x y) :
      (support n).Reachable (true,x) (false,y) :=
    (show (support n).Adj (true,x) (false,y) from h).reachable
  have hab : (support n).Reachable a b := crossing _ _ (by simp [capacity])
  have reach (v : Vertex n) : (support n).Reachable a v := by
    rcases v with ⟨side,e|v⟩
    · cases side
      · exact hab.trans ((crossing _ _ (capB false o)).symm.trans (crossing _ _ (capB e o)))
      · exact (crossing _ _ (capA false o)).trans (crossing _ _ (capA e o)).symm
    · cases side
      · exact crossing _ _ (capA false v)
      · exact hab.trans (crossing _ _ (capB false v)).symm
  exact (connected_iff _).mpr ⟨fun u v => (reach u).symm.trans (reach v),⟨a⟩⟩

/-- Each ordinary vertex has exactly the local block width as its
number of distinct ordinary crossing neighbors. -/
theorem ordinary_neighbors (x : Ord n) :
    (univ.filter fun y : Ord n => 0 < capacity (.inr x) (.inr y)).card = 2*n+6 := by
  classical
  let emb : Copy n ↪ Ord n :=
    ⟨fun c => (x.1,c),fun _ _ h => congrArg Prod.snd h⟩
  have he : (univ.filter fun y : Ord n => 0 < capacity (.inr x) (.inr y)) = univ.map emb := by
    ext y
    simp only [mem_filter,mem_univ,true_and,ordinary_capacity,mem_map]
    constructor
    · intro h
      exact ⟨y.2,Prod.ext h rfl⟩
    · rintro ⟨c,h⟩
      change (x.1,c) = y at h
      have he := congrArg (fun p : Ord n => p.1) h
      exact he
  rw [he,card_map,card_univ,card_copy]

/-- A growing family of connected regular multigraphs with sparse block-diagonal
ordinary crossing support, for which every internal color needs compensation. -/
theorem factorization (n : ℕ) : ∃ F : (graph n).EdgeColoring (degree n), F.IsFactorization := by
  classical
  obtain ⟨P⟩ := packing (n:=n) capacity (fun x y => (ordinary_capacity x y).mpr) capA capB
  have relabeled := P.relabel (coordA n) (coordB n)
  have hA : (fun _ : Fin (n+1) => (free first : Finset (Side n)).map (coordA n).toEmbedding)
      = missingOn (seed n) (left n) := funext map_freeA
  have hB : (fun _ : Fin (n+1) => (free second : Finset (Side n)).map (coordB n).toEmbedding)
      = missingOn (seed n) (left n)ᶜ := funext map_freeB
  have hcap : (fun x y => capacity ((coordA n).symm x) ((coordB n).symm y)) =
      fun x y => (graph n).mult s(x.val,y.val) := by
    funext x y
    obtain ⟨x,rfl⟩ := (coordA n).surjective x
    obtain ⟨y,rfl⟩ := (coordB n).surjective y
    simp only [Equiv.symm_apply_apply]
    rfl
  rw [hA,hB,hcap] at relabeled
  exact exists_factorization_of_crossing_packing (graph n) (left n) (degree n) (n+1)
    (by unfold degree; omega) (regular n) (seed n) relabeled

/-- The new criterion applies to a connected regular graph whose
fixed cut fails the original pair-degree condition at every palette size. -/
theorem separating_family (n : ℕ) :
    (graph n).IsRegularOfDegree (degree n) ∧ (support n).Connected ∧
    (∃ F : (graph n).EdgeColoring (degree n), F.IsFactorization) ∧
    ∀ a k, 0 < k → ¬ PairDegreeCondition
      (fun x y : Side n => (graph n).mult s((true,x),(false,y)))
      exceptional exceptional (Fintype.card (Side n)) a k := by
  refine ⟨regular n,connected n,factorization n,?_⟩
  intro a k hk
  apply original_pair_fails capacity _ a k hk
  intro x y h
  exact Nat.eq_zero_of_not_pos (fun hp => h ((ordinary_capacity x y).mp hp))

end WeightedPaper.Blocks.Example

#print axioms WeightedPaper.Blocks.Example.ordinary_neighbors
#print axioms WeightedPaper.Blocks.Example.separating_family
#print axioms WeightedPaper.Blocks.Example.factorization
