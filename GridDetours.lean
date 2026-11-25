module

public import DetourSchedule
public import WECRGridModel

@[expose] public section


namespace WeightedPaper.Repair
open Finset

theorem gridNeighbors_card {q b : ℕ} (x : CellVertex q b) :
    (gridNeighbors x).card = b*(2*q-1) := by
  let row : Finset (CellVertex q b) := {x.1} ×ˢ (univ ×ˢ univ)
  let col : Finset (CellVertex q b) := univ ×ˢ ({x.2.1} ×ˢ univ)
  have inter : row ∩ col = {x.1} ×ˢ ({x.2.1} ×ˢ univ) := by
    ext ⟨i,j,k⟩; simp only [row,col,mem_inter,mem_product,mem_singleton,mem_univ,and_true,true_and]
  have count := card_union_add_card_inter row col
  rw [inter] at count
  simp only [card_product, card_singleton, card_univ, Fintype.card_fin, one_mul] at count
  have rsize : row.card = q*b := by simp [row]
  have csize : col.card = q*b := by simp [col]
  change (row ∪ col).card = _
  have qpos := x.1.isLt
  obtain ⟨k,hk⟩ : ∃ k, q = k+1 := ⟨q-1,by omega⟩
  rw [show 2*q-1 = 2*k+1 by omega]
  rw [rsize,csize] at count
  nlinarith [show q*b = (k+1)*b by rw [hk]]

theorem gridNeighbors_symmetric {q b : ℕ} (x y : CellVertex q b) :
    y ∈ gridNeighbors x ↔ x ∈ gridNeighbors y := by
  rcases x with ⟨i,j,k⟩; rcases y with ⟨i',j',k'⟩
  simp only [gridNeighbors,mem_union,mem_product,mem_singleton,mem_univ,and_true,true_and,eq_comm]

/-- Actual row/column support of §6.3, with arbitrary hole positions.
The forbidden positions include all switched fillers and all exceptional or
internal reservations at ordinary coordinates. Every selected round is a
permutation on the holes plus the intact admissible filler positions. -/
theorem grid_detour_matchings (b q : ℕ) (hb : 1 ≤ b) (hq : 12 ≤ q)
    (position : Fin (Nat.sqrt q) ↪ CellVertex q b) (forbidden : Finset (CellVertex q b))
    (blocked : forbidden.card ≤ 2*Nat.sqrt q+4) (removed : ∀ h, position h ∈ forbidden) :
    let H := Fin (Nat.sqrt q)
    let W := {w : CellVertex q b // w ∉ forbidden}
    let d := b*(2*q-1)
    ∃ (f : Fin d → H → W) (tag : Fin d → Bool) (π : Fin d → Equiv.Perm (H ⊕ W)),
      (∀ j h, (f j h).val ∈ gridNeighbors (position h) ∧
        position h ∈ gridNeighbors (f j h).val ∧ (f j h).val ≠ position h) ∧
      (∀ h, Function.Injective (fun j => (tag j, f j h))) ∧
      (∀ j h, π j (.inl h) = .inr (f j h) ∧ π j (.inr (f j h)) = .inl h) ∧
      ∀ j w, w ∉ Set.range (f j) → π j (.inr w) = .inr w := by
  intro H W d
  let helpers (h : H) : Finset W := (gridNeighbors (position h)).subtype (fun w => w ∉ forbidden)
  have room h : (d+1)/2 ≤ (helpers h).card := by
    have e : (helpers h).card = (gridNeighbors (position h) \ forbidden).card := by
      dsimp only [helpers]; rw [card_subtype]; congr 1; ext w; simp
    have n := le_card_sdiff forbidden (gridNeighbors (position h))
    rw [gridNeighbors_card] at n
    have hroom := (grid_detour_room b q hb hq).2
    change (d+1)/2 ≤ d-(2*Nat.sqrt q+4) at hroom
    rw [e]
    change d-forbidden.card ≤ _ at n
    omega
  have holes : Fintype.card H ≤ (d+1)/2 := by
    change Fintype.card (Fin (Nat.sqrt q)) ≤ (d+1)/2
    simpa only [Fintype.card_fin] using (grid_detour_room b q hb hq).1
  obtain ⟨f,tag,π,valid,inj,swap,stay⟩ := detour_matchings helpers d holes room
  refine ⟨f,tag,π,fun j h => ?_,inj,swap,stay⟩
  have hv : (f j h).val ∈ gridNeighbors (position h) := Finset.mem_subtype.mp (valid j h)
  exact ⟨hv,(gridNeighbors_symmetric _ _).mp hv,fun eq => (f j h).property (eq ▸ removed h)⟩


/-- Copy identity includes its pool and both physical coordinates. It
distinguishes the two directions of each exchange as well as all rounds.
The physical holes lie in the forbidden set and the helpers lie outside. -/
theorem detour_copies_injective {H W V J : Type*}
    (hole : H ↪ V) (helper : W ↪ V) (apart : ∀ h w, hole h ≠ helper w)
    (tag : J → Bool) (f : J → H → W)
    (once : ∀ h, Function.Injective fun j => (tag j,f j h)) :
    Function.Injective (fun p : (J × H) × Bool =>
      if p.2 then (tag p.1.1,hole p.1.2,helper (f p.1.1 p.1.2))
      else (tag p.1.1,helper (f p.1.1 p.1.2),hole p.1.2)) := by
  rintro ⟨⟨j,h⟩,s⟩ ⟨⟨k,t⟩,u⟩ eq
  cases s <;> cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    Prod.mk.injEq] at eq ⊢
  · have e := hole.injective eq.2.2
    subst t
    exact ⟨⟨once h (Prod.ext eq.1 (helper.injective eq.2.1)), rfl⟩,by trivial⟩
  · exact (apart t _ eq.2.1.symm).elim
  · exact (apart h _ eq.2.1).elim
  · have e := hole.injective eq.2.1
    subst t
    exact ⟨⟨once h (Prod.ext eq.1 (helper.injective eq.2.2)), rfl⟩,by trivial⟩
end WeightedPaper.Repair
