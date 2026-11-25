import WeightedPaper.FullCriterion

/-! A symmetric two-part construction. Internal edges are restricted to
ordinary vertices. Cross edges use independent matrices for ordinary pairs,
exceptional incidences and pairs of exceptional vertices. -/
namespace WeightedPaper.Examples

open Finset SimpleGraph
open scoped Classical

variable {X O : Type*} [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O]

structure Host (X O : Type*) where
  internal : O → O → ℕ
  internal_symm : ∀ a b, internal a b = internal b a
  internal_diag : ∀ a, internal a a = 0
  ordinary : O → O → ℕ
  ordinary_symm : ∀ a b, ordinary a b = ordinary b a
  incidence : X → O → ℕ
  exceptional : X → X → ℕ
  exceptional_symm : ∀ x y, exceptional x y = exceptional y x

abbrev Vertex (X O : Type*) := Bool × (X ⊕ O)

def Host.cross (P : Host X O) : (X ⊕ O) → (X ⊕ O) → ℕ
  | .inl x, .inl y => P.exceptional x y
  | .inl x, .inr b => P.incidence x b
  | .inr a, .inl y => P.incidence y a
  | .inr a, .inr b => P.ordinary a b

theorem Host.cross_symm (P : Host X O) (a b : X ⊕ O) : P.cross a b = P.cross b a := by
  cases a <;> cases b <;> simp [Host.cross,P.ordinary_symm,P.exceptional_symm]

def Host.inside (P : Host X O) : (X ⊕ O) → (X ⊕ O) → ℕ
  | .inr a, .inr b => P.internal a b
  | _, _ => 0

theorem Host.inside_symm (P : Host X O) (a b : X ⊕ O) : P.inside a b = P.inside b a := by
  cases a <;> cases b <;> simp [Host.inside,P.internal_symm]

def Host.adj (P : Host X O) (v w : Vertex X O) : ℕ :=
  if v.1 = w.1 then P.inside v.2 w.2 else P.cross v.2 w.2

def Host.graph (P : Host X O) : MultiGraph (Vertex X O) where
  mult := Sym2.lift ⟨P.adj, fun u v => by
    by_cases h : u.1 = v.1
    · simp only [Host.adj,if_pos h,if_pos h.symm]
      exact P.inside_symm _ _
    · simp only [Host.adj,if_neg h,if_neg (Ne.symm h)]
      exact P.cross_symm _ _⟩
  loopless e he := by
    induction e using Sym2.inductionOn with
    | hf v w =>
      obtain rfl := Sym2.mk_isDiag_iff.mp he
      change P.adj v v = 0
      rcases v with ⟨b,v⟩
      cases v <;> simp [Host.adj,Host.inside,P.internal_diag]

@[simp] theorem Host.graph_pair (P : Host X O) (v w : Vertex X O) :
    P.graph.mult s(v,w) = P.adj v w := rfl

def half (X O : Type*) [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O] (b : Bool) :
    Finset (Vertex X O) := univ.filter (fun v => v.1 = b)

@[simp] theorem mem_half (v : Vertex X O) (b : Bool) :
    v ∈ half X O b ↔ v.1 = b := by simp [half]

theorem half_compl (b : Bool) : (half X O b)ᶜ = half X O (!b) := by
  ext v
  cases b <;> cases v.1 <;> simp

def sideEquiv (b : Bool) : (X ⊕ O) ≃ (half X O b) where
  toFun v := ⟨(b,v), (mem_half _ _).mpr rfl⟩
  invFun v := v.val.2
  left_inv _ := rfl
  right_inv v := Subtype.ext (Prod.ext ((mem_half _ _).mp v.2).symm rfl)

@[simp] theorem sideEquiv_val (b : Bool) (v : X ⊕ O) :
    ((sideEquiv b v : half X O b) : Vertex X O) = (b,v) := rfl

theorem side_card (b : Bool) : (half X O b).card = Fintype.card X + Fintype.card O := by
  have h := Fintype.card_congr (sideEquiv (X:=X) (O:=O) b)
  rwa [Fintype.card_sum,Fintype.card_coe,eq_comm] at h

@[simp] theorem Host.restrict_pair (P : Host X O) (b : Bool) (v w : Vertex X O) :
    (P.graph.restrict (half X O b)).mult s(v,w) =
      if v.1 = b ∧ w.1 = b then P.inside v.2 w.2 else 0 := by
  change (if s(v,w).toFinset ⊆ half X O b then P.graph.mult s(v,w) else 0) = _
  by_cases hv : v.1 = b <;> by_cases hw : w.1 = b <;>
    simp [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,hv,hw,Host.adj]

theorem Host.degree_restricted (P : Host X O) (b c : Bool) (v : X ⊕ O) :
    (P.graph.restrict (half X O b)).degree (c,v) =
      if c = b then ∑ w, P.inside v w else 0 := by
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_prod_type]
  cases b <;> cases c <;> simp [Fintype.sum_bool]

theorem Host.degree (P : Host X O) (b : Bool) (v : X ⊕ O) :
    P.graph.degree (b,v) = (∑ w, P.inside v w) + ∑ w, P.cross v w := by
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_prod_type,Fintype.sum_bool]
  cases b <;> simp [Host.adj,add_comm]

theorem Host.regular (P : Host X O) (D : ℕ)
    (hx : ∀ x, (∑ y, P.exceptional x y) + ∑ a, P.incidence x a = D)
    (ho : ∀ a, (∑ b, P.internal a b) + (∑ x, P.incidence x a) + (∑ b, P.ordinary a b) = D) :
    P.graph.IsRegularOfDegree D := by
  intro v
  rcases v with ⟨b,x|a⟩
  · rw [degree,Fintype.sum_sum_type,Fintype.sum_sum_type]
    simpa [Host.inside,Host.cross] using hx x
  · rw [degree,Fintype.sum_sum_type,Fintype.sum_sum_type]
    simpa [Host.inside,Host.cross,add_assoc] using ho a

def ordinaryBipartition (f : O → Bool) : Finset (Vertex X O) :=
  univ.filter (fun v => v.2.elim (fun _ => false) f = true)

theorem Host.colourable_inside (P : Host X O) (b : Bool) (k : ℕ) (f : O → Bool)
    (hB : ∀ a c, f a = f c → P.internal a c = 0)
    (hdeg : ∀ a, (∑ c, P.internal a c) ≤ k) :
    Nonempty ((P.graph.restrict (half X O b)).EdgeColoring k) := by
  classical
  apply MultiGraph.exists_edgeColoring_of_bipartite _ (ordinaryBipartition (X:=X) f) k
  · intro v w h
    rw [P.restrict_pair]
    split_ifs
    · rcases v with ⟨_,a|a⟩ <;> rcases w with ⟨_,c|c⟩ <;> simp [Host.inside]
      apply hB
      apply Bool.eq_iff_iff.mpr
      simpa [ordinaryBipartition] using h
    · rfl
  · rintro ⟨c,a|a⟩ <;> rw [degree_restricted] <;> split_ifs <;>
      simp [Fintype.sum_sum_type,Host.inside,hdeg]

theorem Host.edgeCount_inside (P : Host X O) (b : Bool) (s : ℕ)
    (hdeg : ∀ a, (∑ c, P.internal a c) = s) :
    2*(P.graph.restrict (half X O b)).edgeCount = Fintype.card O*s := by
  rw [← MultiGraph.sum_degrees_eq_twice_edgeCount,Fintype.sum_prod_type,Fintype.sum_bool]
  have hsum (v : O) : (∑ w : X ⊕ O, P.inside (.inr v) w) = s := by
    simp [Fintype.sum_sum_type,Host.inside,hdeg v]
  cases b <;> simp [P.degree_restricted,Fintype.sum_sum_type,Host.inside,hdeg]

end WeightedPaper.Examples
