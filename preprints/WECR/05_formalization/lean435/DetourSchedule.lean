import GalvinMultigraph.Local.Konig
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace WeightedPaper.Repair
open Finset

/-- Choose m eligible helpers at each hole and color the selected pairs.
Each helper has degree at most the number of holes. Kőnig's theorem supplies
m colors, each of which occurs once at every hole. -/
theorem helper_schedule {H W : Type*} [Fintype H] [Fintype W] [DecidableEq W]
    (neighbors : H → Finset W) (m : ℕ) (holes : Fintype.card H ≤ m)
    (room : ∀ h, m ≤ (neighbors h).card) :
    ∃ f : Fin m → H → W, (∀ j, Function.Injective (f j)) ∧
      (∀ h, Function.Injective (fun j => f j h)) ∧ ∀ j h, f j h ∈ neighbors h := by
  classical
  choose chosen sub count using fun h => exists_subset_card_eq (room h)
  let pairs : Finset (H × W) := univ.filter fun e => e.2 ∈ chosen e.1
  have ml (h : H) : GalvinMultigraph.Local.degLOn Prod.fst pairs h ≤ m := by
    have e : pairs.filter (fun e => e.1=h) = (chosen h).image (fun w => (h,w)) := by
      ext ⟨i,w⟩
      simp [pairs]
      aesop
    rw [GalvinMultigraph.Local.degLOn,e,card_image_of_injective]
    · exact (count h).le
    · exact fun _ _ eq => congrArg Prod.snd eq
  have mr (w : W) : GalvinMultigraph.Local.degROn Prod.snd pairs w ≤ m := by
    let S := pairs.filter (fun e => e.2=w)
    let project (e : ↥S) := e.val.1
    have inj : Function.Injective project := by
      intro u v eq
      apply Subtype.ext
      exact Prod.ext eq ((mem_filter.mp u.property).2.trans (mem_filter.mp v.property).2.symm)
    have b := Fintype.card_le_of_injective project inj
    rw [Fintype.card_coe] at b
    exact b.trans holes
  obtain ⟨c,less,proper⟩ := GalvinMultigraph.Local.konig_multigraph Prod.fst Prod.snd pairs m ml mr
  have inPairs (h : H) (w : ↥(chosen h)) : (h,w.val) ∈ pairs :=
    mem_filter.mpr ⟨mem_univ _,w.property⟩
  let color (h : H) (w : ↥(chosen h)) : Fin m := ⟨c (h,w.val),less _ (inPairs h w)⟩
  have inj (h : H) : Function.Injective (color h) := by
    intro u v eq
    apply Subtype.ext
    by_contra ne
    exact proper _ (inPairs h u) _ (inPairs h v)
      (fun e => ne (congrArg Prod.snd e)) (Or.inl rfl) (congrArg Fin.val eq)
  let equiv (h : H) : ↥(chosen h) ≃ Fin m := Equiv.ofBijective (color h)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj h,by simp [count]⟩)
  let f (j : Fin m) (h : H) := ((equiv h).symm j).val
  refine ⟨f,?_,fun h _ _ eq => (equiv h).symm.injective (Subtype.ext eq),
    fun j h => sub h ((equiv h).symm j).property⟩
  intro j h k eq
  by_contra ne
  let u := (equiv h).symm j
  let v := (equiv k).symm j
  have hc : color h u = j := (equiv h).apply_symm_apply j
  have kc : color k v = j := (equiv k).apply_symm_apply j
  exact proper _ (inPairs h u) _ (inPairs k v)
    (fun e => ne (congrArg Prod.fst e)) (Or.inr eq) (congrArg Fin.val (hc.trans kc.symm))

/-- Two tagged copies of the helper schedule yield d rounds with no repeated
use of the same tagged hole-helper pair. -/
theorem double_copy_schedule {H W : Type*} [Fintype H] [Fintype W] [DecidableEq W]
    (neighbors : H → Finset W) (d : ℕ) (holes : Fintype.card H ≤ (d+1)/2)
    (room : ∀ h, (d+1)/2 ≤ (neighbors h).card) :
    ∃ f : Fin d → H → W, ∃ tag : Fin d → Bool,
      (∀ j, Function.Injective (f j)) ∧
      (∀ h, Function.Injective (fun j => (tag j,f j h))) ∧
      ∀ j h, f j h ∈ neighbors h := by
  classical
  let m := (d+1)/2
  obtain ⟨f,cols,rows,valid⟩ := helper_schedule neighbors m holes room
  have size : Fintype.card (Fin d) ≤ Fintype.card (Bool × Fin m) := by simp [m]; omega
  obtain ⟨code⟩ := Function.Embedding.nonempty_of_card_le size
  refine ⟨fun j => f (code j).2, fun j => (code j).1, fun j => cols _, ?_,fun j h => valid _ _⟩
  intro h j k eq
  apply code.injective
  exact Prod.ext (congrArg (fun p : Bool × W => p.1) eq) (rows h (congrArg (fun p : Bool × W => p.2) eq))

/-- The degree and the total number of blocked coordinates suffice for
the improved helper schedule. -/
theorem grid_detour_room (b q : ℕ) (hb : 1 ≤ b) (hq : 12 ≤ q) :
    let d := b*(2*q-1)
    let r := Nat.sqrt q
    r ≤ (d+1)/2 ∧ (d+1)/2 ≤ d-(2*r+4) := by
  intro d r
  have root := Nat.sqrt_le q
  change r*r ≤ q at root
  have bound : 2*r+5 ≤ q := by
    by_cases small : r ≤ 3
    · omega
    have sq : (r:ℤ)*(r:ℤ) ≤ q := by exact_mod_cast root
    have large : (4:ℤ) ≤ r := by exact_mod_cast (show 4 ≤ r by omega)
    have h : (2:ℤ)*r+5 ≤ q := by
      nlinarith [mul_nonneg (show (0:ℤ) ≤ r-4 by linarith) (show (0:ℤ) ≤ r+2 by linarith)]
    exact_mod_cast h
  have deg : 2*q-1 ≤ d := Nat.le_mul_of_pos_left _ hb
  omega

/-- Replace the filler at each chosen helper by the two crossing edges of
a three-edge detour. The holes and all the original filler positions are
then paired bijectively. -/
theorem detour_permutation {H W : Type*} (f : H → W) (inj : Function.Injective f) :
    ∃ π : Equiv.Perm (H ⊕ W), (∀ h, π (.inl h) = .inr (f h)) ∧
      (∀ h, π (.inr (f h)) = .inl h) ∧
      ∀ w, w ∉ Set.range f → π (.inr w) = .inr w := by
  classical
  let g (w : W) : H ⊕ W := if h : ∃ x, f x = w then .inl h.choose else .inr w
  have back h : g (f h) = .inl h := by
    have ex : ∃ x, f x = f h := ⟨h,rfl⟩
    dsimp only [g]
    rw [dif_pos ex, inj ex.choose_spec]
  let flip : H ⊕ W → H ⊕ W := Sum.elim (fun h => .inr (f h)) g
  have inv : Function.Involutive flip := by
    rintro (h|w)
    · exact back h
    · by_cases hw : w ∈ Set.range f
      · obtain ⟨h,rfl⟩ := hw
        change flip (g (f h)) = _
        rw [back]; rfl
      · have stay : g w = .inr w := dif_neg hw
        change flip (g w) = _
        rw [stay]; exact stay
  exact ⟨inv.toPerm flip, fun _ => rfl, back, fun _ hw => dif_neg hw⟩

/-- For every round there is a full matching on holes and fillers.
Both crossing directions of a detour use the selected copy tag. Distinct
rounds never use the same tagged hole/helper pair. Unused helpers keep
the filler copy indexed by the round. -/
theorem detour_matchings {H W : Type*} [Fintype H] [Fintype W] [DecidableEq W]
    (neighbors : H → Finset W) (d : ℕ) (holes : Fintype.card H ≤ (d+1)/2)
    (room : ∀ h, (d+1)/2 ≤ (neighbors h).card) :
    ∃ (f : Fin d → H → W) (tag : Fin d → Bool) (π : Fin d → Equiv.Perm (H ⊕ W)),
      (∀ j h, f j h ∈ neighbors h) ∧
      (∀ h, Function.Injective (fun j => (tag j,f j h))) ∧
      (∀ j h, π j (.inl h) = .inr (f j h) ∧ π j (.inr (f j h)) = .inl h) ∧
      ∀ j w, w ∉ Set.range (f j) → π j (.inr w) = .inr w := by
  obtain ⟨f,tag,inj,resources,valid⟩ := double_copy_schedule neighbors d holes room
  choose π go back stay using fun j => detour_permutation (f j) (inj j)
  exact ⟨f,tag,π,valid,resources,fun j h => ⟨go j h,back j h⟩,stay⟩

end WeightedPaper.Repair
