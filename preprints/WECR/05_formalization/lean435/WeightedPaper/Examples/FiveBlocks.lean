import WeightedPaper.Examples.Matrices

namespace WeightedPaper.Examples

open Finset
open scoped Classical

/-- The two neighbors of a block form the reflected cyclic interval
of length two. The resulting bipartite block graph is a 10-cycle. -/
def blockAdj (i j : Fin 5) : Prop := (i+j).val < 2

instance (i j : Fin 5) : Decidable (blockAdj i j) := inferInstanceAs (Decidable ((i+j).val < 2))

theorem blockAdj_symm (i j : Fin 5) : blockAdj i j ↔ blockAdj j i := by
  unfold blockAdj
  rw [add_comm]

theorem block_degree (i : Fin 5) : (univ.filter (blockAdj i)).card = 2 := by
  have h : ∀ j : Fin 5, (univ.filter (blockAdj j)).card = 2 := by decide
  exact h i

def blockNeighbours (J : Finset (Fin 5)) : Finset (Fin 5) :=
  univ.filter fun j => ∃ i ∈ J, blockAdj i j

theorem block_growth (J : Finset (Fin 5)) (hJ : 0 < J.card) (hJ' : J.card < 5) :
    J.card + 1 ≤ (blockNeighbours J).card := by
  have h : ∀ K : Finset (Fin 5), 0 < K.card → K.card < 5 → K.card+1 ≤ (blockNeighbours K).card := by
    decide
  exact h J hJ hJ'

theorem block_neighbours_of_full (J : Finset (Fin 5)) (hJ : J.card = 5) :
    blockNeighbours J = univ := by
  have h : ∀ K : Finset (Fin 5), K.card = 5 → blockNeighbours K = univ := by decide
  exact h J hJ

variable {O : Type*} [Fintype O] [DecidableEq O]

def blockCopies (π : O → Fin 5) (x y : O) : ℕ :=
  if blockAdj (π x) (π y) then 1 else 0

theorem blockCopies_symm (π : O → Fin 5) (x y : O) : blockCopies π x y = blockCopies π y x := by
  unfold blockCopies
  rw [if_congr (blockAdj_symm _ _) rfl rfl]

def fiberCount (π : O → Fin 5) (S : Finset O) (j : Fin 5) : ℕ :=
  (S.filter (fun x => π x = j)).card

theorem sum_fiberCount (π : O → Fin 5) (S : Finset O) (J : Finset (Fin 5)) :
    ∑ j ∈ J,fiberCount π S j = (S.filter fun x => π x ∈ J).card := by
  simp only [fiberCount,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]

theorem blockCopies_degree (π : O → Fin 5) (B : ℕ)
    (hπ : ∀ j, fiberCount π univ j = B) (x : O) :
    (∑ y, blockCopies π x y) = 2*B := by
  unfold blockCopies
  rw [← sum_filter, ← card_eq_sum_ones]
  let J := univ.filter (blockAdj (π x))
  have he : (univ.filter fun y => blockAdj (π x) (π y)) = univ.filter (fun y => π y ∈ J) := by
    ext y
    simp [J]
  rw [he,← sum_fiberCount π,show (∑ j ∈ J, fiberCount π univ j) = ∑ _j ∈ J, B from
    sum_congr rfl (fun j _ => hπ j),sum_const,nsmul_eq_mul,show J.card=2 from block_degree _]
  rfl

theorem blockCopies_neighbours (π : O → Fin 5) (B : ℕ)
    (hπ : ∀ j, fiberCount π univ j = B) (x : O) :
    (univ.filter fun y => 0 < blockCopies π x y).card = 2*B := by
  have h := blockCopies_degree π B hπ x
  rw [← h,card_eq_sum_ones,sum_filter]
  apply sum_congr rfl
  intro y _
  by_cases hh : blockAdj (π x) (π y) <;> simp [blockCopies,hh]

theorem block_robust (π : O → Fin 5) (B ρ τ : ℕ)
    (hπ : ∀ j, fiberCount π univ j = B) (hO : Fintype.card O = 5*B)
    (hBT : 6*ρ ≤ B) (hτ : 5*ρ ≤ τ)
    (S : Finset O) (hsmall : τ ≤ S.card) (hlarge : S.card+τ ≤ Fintype.card O) :
    S.card+ρ ≤ (univ.filter fun y => ρ ≤ (S.filter fun x => 0 < blockCopies π x y).card).card := by
  classical
  let J : Finset (Fin 5) := univ.filter (fun j => ρ ≤ fiberCount π S j)
  have hsum := sum_fiberCount π S (univ : Finset (Fin 5))
  have hsum' : (∑ j : Fin 5, fiberCount π S j) = S.card := by simpa using hsum
  have hbound (j : Fin 5) : fiberCount π S j ≤ B := by
    rw [← hπ j]
    exact card_le_card (fun x hx => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩)
  have hbelow (j : Fin 5) (hj : j ∈ Jᶜ) : fiberCount π S j < ρ :=
    lt_of_not_ge (fun hh => (mem_compl.mp hj) (mem_filter.mpr ⟨mem_univ _,hh⟩))
  have hjpos : 0 < J.card := by
    by_contra! hn
    have hz : J = ∅ := card_eq_zero.mp (by omega)
    have hb : (∑ j : Fin 5, fiberCount π S j) < ∑ _j : Fin 5, ρ := by
      apply sum_lt_sum_of_nonempty univ_nonempty
      intro j _
      exact hbelow j (by simp [hz])
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
    omega
  let Y := univ.filter fun y => π y ∈ blockNeighbours J
  have hY : Y.card = (blockNeighbours J).card * B := by
    dsimp only [Y]
    rw [← sum_fiberCount π]
    rw [show (∑ j ∈ blockNeighbours J, fiberCount π univ j) = ∑ _j ∈ blockNeighbours J, B from
      sum_congr rfl (fun j _ => hπ j),sum_const,nsmul_eq_mul]
    rfl
  have hsub : Y ⊆ univ.filter (fun y => ρ ≤ (S.filter fun x => 0 < blockCopies π x y).card) := by
    intro y hy
    obtain ⟨j,hj,hAdj⟩ := (mem_filter.mp (mem_filter.mp hy).2).2
    have hIncl : S.filter (fun x => π x = j) ⊆ S.filter (fun x => 0 < blockCopies π x y) := by
      intro x hx
      obtain ⟨hx,he⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hx,by simp [blockCopies,he,hAdj]⟩
    exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hj).2).trans (card_le_card hIncl)⟩
  apply le_trans _ (card_le_card hsub)
  rw [hY]
  by_cases hj : J.card = 5
  · rw [block_neighbours_of_full J hj,card_univ,Fintype.card_fin]
    omega
  · have hcard : J.card ≤ 5 := by simpa using card_le_univ J
    have hstep := block_growth J hjpos (by omega)
    have hA : (∑ j ∈ J,fiberCount π S j) ≤ J.card*B := by
      calc
        _ ≤ ∑ _j ∈ J,B := sum_le_sum (fun j _ => hbound j)
        _ = _ := by simp
    have hB : (∑ j ∈ Jᶜ,fiberCount π S j) ≤ 5*ρ := by
      have hh : (∑ j ∈ Jᶜ,fiberCount π S j) ≤ (Jᶜ).card*ρ := by
        calc
          _ ≤ ∑ _j ∈ Jᶜ,ρ := sum_le_sum (fun j hj => (hbelow j hj).le)
          _ = _ := by simp
      exact hh.trans (Nat.mul_le_mul_right ρ (by simpa using card_le_univ Jᶜ))
    have hsplit := sum_add_sum_compl J (fiberCount π S)
    rw [hsum'] at hsplit
    have hmul := Nat.mul_le_mul_right B hstep
    rw [Nat.add_mul,one_mul] at hmul
    omega

end WeightedPaper.Examples
