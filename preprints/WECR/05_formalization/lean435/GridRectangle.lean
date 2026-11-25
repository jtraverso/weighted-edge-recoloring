import GridCompletion

namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

abbrev HalfIndex (q b : ℕ) := Fin (q/2) × Fin q × Fin b

def halfCells (q b : ℕ) (upper : Bool) : HalfIndex q b ↪ CellVertex q b :=
  ⟨fun v => (⟨(if upper then q/2 else 0)+v.1.val,by
      have h := v.1.isLt
      cases upper <;> simp_all <;> omega⟩,v.2),by
    intro u v eq
    obtain ⟨first,second⟩ := Prod.mk.inj eq
    have h := congrArg Fin.val first
    have he : u.1.val = v.1.val := Nat.add_left_cancel h
    exact Prod.ext (Fin.ext he) second⟩

noncomputable def cutEmbedding {q b : ℕ} (m : Marked q ↪ CellVertex q b) (upper : Bool) :
    HalfIndex q b ↪ Side (Fin (Nat.sqrt q)) (Intact m) :=
  (halfCells q b upper).trans ((coordinates m).symm.toEmbedding.trans Function.Embedding.inl)

noncomputable def cutSet {q b : ℕ} (m : Marked q ↪ CellVertex q b) (upper : Bool) :=
  univ.map (cutEmbedding m upper)

theorem cutSet_card {q b : ℕ} (m : Marked q ↪ CellVertex q b) (upper : Bool) :
    (cutSet m upper).card = q/2*q*b := by
  simp [cutSet,HalfIndex,Fintype.card_prod,mul_assoc]

theorem gridNeighbor_iff {q b : ℕ} (x y : CellVertex q b) :
    y ∈ gridNeighbors x ↔ y.1 = x.1 ∨ y.2.1 = x.2.1 := by
  simp only [gridNeighbors,mem_union,mem_product,mem_univ,mem_singleton,and_true,true_and]

/-- The ordinary filler edges of this placement lie inside the support
of the two grid pools, so the full host has that same ordinary support. -/
theorem grid_host_ordinary_support {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b) :
    let m := markedEmbedding q b hq hb
    let V := Ordinary (Fin (Nat.sqrt q)) (Intact m)
    ∀ (x y : V), 0 < capacity (support m) (b*(2*q-1)) (.inl x) (.inl y) ↔ support m x y := by
  intro m V x y
  have filler : static (Sum.inl x : Side _ _) (Sum.inl y) → support m x y := by
    rcases x with i | (i | (i | i)) <;> rcases y with j | (j | (j | j)) <;>
      simp only [static] <;> try tauto
    · intro eq
      subst j
      apply (gridNeighbor_iff (coordinates m _) (coordinates m _)).mpr
      right
      rfl
    · intro eq
      subst j
      apply (gridNeighbor_iff (coordinates m _) (coordinates m _)).mpr
      left
      rfl
  unfold capacity
  change 0 < (if static (Sum.inl x : Side _ _) (Sum.inl y) then b*(2*q-1) else 0) +
      (if support m x y then 2 else 0) ↔ support m x y
  by_cases h : support m x y
  · simp [h]
  · simp [h, mt filler h]

theorem grid_host_ordinary_degrees {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b) :
    let m := markedEmbedding q b hq hb
    let V := Ordinary (Fin (Nat.sqrt q)) (Intact m)
    let d := b*(2*q-1)
    let c := capacity (support m) d
    (∀ x : V, (univ.filter fun y : V => 0 < c (.inl x) (.inl y)).card = d) ∧
    (∀ y : V, (univ.filter fun x : V => 0 < c (.inl x) (.inl y)).card = d) := by
  intro m V d c
  simpa only [m, c, d, grid_host_ordinary_support hq hb] using support_degrees m

theorem marked_second_half {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b) (i : Fin 2) :
    ((markedEmbedding q b hq hb (.inr (.inl i))).1 : ℕ) = q/2 := rfl

private theorem cut_static {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b)
    (x y : HalfIndex q b) :
    ¬ static (cutEmbedding (markedEmbedding q b hq hb) false x)
      (cutEmbedding (markedEmbedding q b hq hb) true y) := by
  let m := markedEmbedding q b hq hb
  let a := (coordinates m).symm (halfCells q b false x)
  let z := (coordinates m).symm (halfCells q b true y)
  have ha : ((coordinates m a).1 : ℕ) < q/2 := by
    simp only [a,Equiv.apply_symm_apply]
    change 0+x.1.val < q/2
    simpa only [zero_add] using x.1.isLt
  have hz : q/2 ≤ ((coordinates m z).1 : ℕ) := by
    simp only [z,Equiv.apply_symm_apply]
    change q/2 ≤ q/2+y.1.val
    omega
  change ¬ static (.inl a) (.inl z)
  intro e
  rcases a with i | (i | (i | i)) <;> rcases z with j | (j | (j | j))
  all_goals try solve | exact e
  · have H := marked_second_half hq hb i
    have er : (coordinates m (.inr (.inl i))).1.val = q/2 := H
    omega
  · have eq : i = j := e
    subst j
    omega

private theorem cut_capacity {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b)
    (x y : HalfIndex q b) :
    capacity (support (markedEmbedding q b hq hb)) (b*(2*q-1))
      (cutEmbedding (markedEmbedding q b hq hb) false x)
      (cutEmbedding (markedEmbedding q b hq hb) true y) =
      if x.2.1 = y.2.1 then 2 else 0 := by
  unfold capacity
  rw [ite_eq_right (cut_static hq hb x y),zero_add]
  have eq : ordinary (support (markedEmbedding q b hq hb))
      (cutEmbedding (markedEmbedding q b hq hb) false x)
      (cutEmbedding (markedEmbedding q b hq hb) true y) ↔ x.2.1 = y.2.1 := by
    let e := coordinates (markedEmbedding q b hq hb)
    change e (e.symm (halfCells q b true y)) ∈ gridNeighbors (e (e.symm (halfCells q b false x))) ↔ _
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply,gridNeighbor_iff]
    have neq : (halfCells q b true y).1 ≠ (halfCells q b false x).1 := by
      intro he
      have ey : q/2+y.1.val = 0+x.1.val := congrArg Fin.val he
      have h := x.1.isLt
      omega
    simp only [neq,false_or]
    change y.2.1 = x.2.1 ↔ x.2.1 = y.2.1
    exact eq_comm
  exact if_congr eq rfl rfl

/-- The two half-row sets have total size N, and every vertex sees exactly
bq crossing copies in the rectangle. This is the entire host capacity,
including the switched pairs and the two off-diagonal fillers. -/
theorem grid_rectangle_counts {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b) (even : q % 2 = 0) :
    let m := markedEmbedding q b hq hb
    let S := cutSet m false
    let T := cutSet m true
    let cap := capacity (support m) (b*(2*q-1))
    S.Nonempty ∧ T.Nonempty ∧ S.card+T.card = b*q^2 ∧
      (∀ x ∈ S, ∑ y ∈ T, cap x y = b*q) ∧ (∀ y ∈ T, ∑ x ∈ S, cap x y = b*q) := by
  intro m S T cap
  have sc : S.card = q/2*q*b := cutSet_card m false
  have tc : T.card = q/2*q*b := cutSet_card m true
  have hn : 0 < q/2*q*b := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  have sq : q/2+q/2 = q := by omega
  have total : S.card+T.card = b*q^2 := by rw [sc,tc]; nlinarith [congrArg (fun n => n*q*b) sq]
  have count (j : Fin q) : (∑ x : HalfIndex q b, if x.2.1 = j then 2 else 0) = b*q := by
    change (∑ x : Fin (q/2) × Fin q × Fin b, if x.2.1 = j then 2 else 0) = _
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have term : (∑ x : Fin q, ∑ _z : Fin b, if x = j then 2 else 0) = b*2 := by
      rw [sum_eq_single j]
      · simp
      · intro x _ hx
        simp [hx]
      · simp
    simp only [term,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    nlinarith [congrArg (fun n => n*b) sq]
  refine ⟨card_pos.mp (sc.symm ▸ hn),card_pos.mp (tc.symm ▸ hn),total,?_,?_⟩
  · intro x hx
    obtain ⟨u,_,rfl⟩ := mem_map.mp hx
    change (∑ y ∈ univ.map (cutEmbedding m true), cap (cutEmbedding m false u) y) = _
    rw [sum_map]
    simpa only [cap,m,cut_capacity hq hb,eq_comm] using count u.2.1
  · intro y hy
    obtain ⟨v,_,rfl⟩ := mem_map.mp hy
    change (∑ x ∈ univ.map (cutEmbedding m false), cap x (cutEmbedding m true v)) = _
    rw [sum_map]
    simpa only [cap,m,cut_capacity hq hb] using count v.2.1

theorem rectangle_fails_for_every_palette {q b : ℕ} (hq : 12 ≤ q) (hb : 0 < b) (even : q % 2 = 0)
    (threshold k : ℕ) (size : threshold < b*q^2) (hk : b*(2*q-1) ≤ k) :
    let m := markedEmbedding q b hq hb
    let cap := capacity (support m) (b*(2*q-1))
    ∃ S T : Finset (Side (Fin (Nat.sqrt q)) (Intact m)),
      S.Nonempty ∧ T.Nonempty ∧ threshold < S.card + T.card ∧
      (∀ x ∈ S, x ∈ Set.range (Sum.inl : Ordinary _ _ → Side _ _)) ∧
      (∀ y ∈ T, y ∈ Set.range (Sum.inl : Ordinary _ _ → Side _ _)) ∧
      (∀ x ∈ S, ∑ y ∈ T, cap x y < k) ∧ (∀ y ∈ T, ∑ x ∈ S, cap x y < k) := by
  intro m cap
  obtain ⟨s,t,h,u,v⟩ := grid_rectangle_counts hq hb even
  have strict : b*q < k := by
    exact (Nat.mul_lt_mul_of_pos_left (by omega : q < 2*q-1) hb).trans_le hk
  have ordinary (upper : Bool) (x : Side (Fin (Nat.sqrt q)) (Intact m)) (hx : x ∈ cutSet m upper) :
      x ∈ Set.range (Sum.inl : Ordinary _ _ → Side _ _) := by
    obtain ⟨a,_,rfl⟩ := mem_map.mp hx
    exact ⟨(coordinates m).symm (halfCells q b upper a),rfl⟩
  exact ⟨cutSet m false,cutSet m true,s,t,by rw [h]; exact size,ordinary false,ordinary true,
    fun x hx => by rw [u x hx]; exact strict,fun y hy => by rw [v y hy]; exact strict⟩
/-- One internal pair has d parallel copies, so the size of any proper
internal palette is at least d. -/
theorem internal_palette_lower_bound {H W : Type} (d k : ℕ) (color : Fin d × Bool → Fin k)
    (proper : ∀ e f, e ≠ f → (endpoint 0 e : Side H W ⊕ Side H W) = endpoint 0 f → color e ≠ color f) :
    d ≤ k := by
  have inj : Function.Injective (fun i : Fin d => color (i,true)) := by
    intro i j eq
    by_contra ne
    exact proper (i,true) (j,true) (fun e => ne (congrArg Prod.fst e)) rfl eq
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ inj

/-- The explicit placement of §6.3, on one and the same host, has a
factorization and fails the rectangle criterion for every admissible
internal palette and every value of the parameter a. -/
theorem sparse_grid_factorization_and_separation {q b : ℕ}
    (hq : 12 ≤ q) (hb : 0 < b) (even : q % 2 = 0) :
    let m := markedEmbedding q b hq hb
    let d := b*(2*q-1)
    let V := Side (Fin (Nat.sqrt q)) (Intact m)
    let cap := capacity (support m) d
    (∃ color : (Fin d × Bool) ⊕ CrossingCopy cap → Fin (3*d),
      ∀ (v : V ⊕ V) i,
        (univ.filter (fun e => color (.inl e) = i ∧ (endpoint 0 e = v ∨ endpoint 1 e = v))).card +
        ((univ : Finset (CrossingCopy cap)).filter (fun e => color (.inr e) = i ∧
          (Sum.inl e.1.1 = v ∨ Sum.inr e.1.2 = v))).card = 1) ∧
    ∀ a k, d ≤ k → ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧ b*q^2-Nat.sqrt q-2*a < S.card + T.card ∧
      (∀ x ∈ S, x ∈ Set.range (Sum.inl : Ordinary _ _ → V)) ∧
      (∀ y ∈ T, y ∈ Set.range (Sum.inl : Ordinary _ _ → V)) ∧
      (∀ x ∈ S, ∑ y ∈ T, cap x y < k) ∧ (∀ y ∈ T, ∑ x ∈ S, cap x y < k) := by
  intro m d V cap
  refine ⟨factorization_of_grid_layout hb hq m,fun a k hk => ?_⟩
  have s : 0 < Nat.sqrt q := Nat.sqrt_pos.mpr (by omega)
  have n : 0 < b*q^2 := by positivity
  exact rectangle_fails_for_every_palette hq hb even _ k (by omega) hk
end WeightedPaper.Repair.Grid
