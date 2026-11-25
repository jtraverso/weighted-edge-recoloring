import Mathlib.Combinatorics.Hall.Basic

namespace WeightedPaper.Repair
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Right vertices visited by a contracted alternating walk are its
intermediate vertices followed by its terminal vertex. -/
def follows (G : V → Finset V) (x : V) : List V → V → Prop
  | [], y => y ∈ G x
  | z :: zs, y => z ∈ G x ∧ follows G z zs y

private theorem first_exit (G : V → Finset V) (S T : Finset V) (hst : T ⊆ S)
    (x y : V) (hx : x ∈ S) (hy : y ∉ T) (zs : List V) (walk : follows G x zs y) :
    ∃ z ∈ (zs ++ [y]), z ∉ T ∧ z ∈ S.biUnion G := by
  induction zs generalizing x with
  | nil => exact ⟨y, by simp, hy, mem_biUnion.mpr ⟨x,hx,walk⟩⟩
  | cons z zs ih =>
    by_cases h : z ∈ T
    · obtain ⟨w,hw,ht,hg⟩ := ih z (hst h) walk.2
      exact ⟨w, List.mem_cons_of_mem _ hw, ht, hg⟩
    · exact ⟨z, by simp, h, mem_biUnion.mpr ⟨x,hx,walk.1⟩⟩

/-- A deterministic matching after conflict-free routing in one color.
Identify right vertices with left vertices using the initial matching on
covered vertices and the prescribed endpoint pairing on holes. A route
then starts and ends at its own hole. Distinct routes have disjoint right
visits. Repetitions within a single route are allowed. -/
theorem matching_of_routed_walks (G : V → Finset V) (holes : Finset V)
    (old : ∀ x ∉ holes, x ∈ G x) (mid : V → List V)
    (routes : ∀ x ∈ holes, follows G x (mid x) x)
    (separate : ∀ x ∈ holes, ∀ y ∈ holes, x ≠ y →
      List.Disjoint (mid x ++ [x]) (mid y ++ [y])) :
    ∃ π : Equiv.Perm V, ∀ x, π x ∈ G x := by
  classical
  have hall (S : Finset V) : S.card ≤ (S.biUnion G).card := by
    let T := S \ holes
    have exit (x : V) (hx : x ∈ S ∩ holes) :
        ∃ z ∈ mid x ++ [x], z ∉ T ∧ z ∈ S.biUnion G :=
      first_exit G S T sdiff_subset x x (mem_inter.mp hx).1
        (by simp [T, (mem_inter.mp hx).2]) _ (routes x (mem_inter.mp hx).2)
    choose out hout using exit
    let f (x : V) := if hx : x ∈ S ∩ holes then out x hx else x
    have outside (x : V) (hx : x ∈ S) (h : x ∉ S ∩ holes) : x ∈ T := by
      exact mem_sdiff.mpr ⟨hx, fun hh => h (mem_inter.mpr ⟨hx,hh⟩)⟩
    apply card_le_card_of_injOn f
    · intro x hx
      change f x ∈ S.biUnion G
      by_cases h : x ∈ S ∩ holes
      · simpa only [f,dif_pos h] using (hout x h).2.2
      · simpa only [f,dif_neg h] using mem_biUnion.mpr ⟨x,hx,old x (mem_sdiff.mp (outside x hx h)).2⟩
    · intro x hx y hy eq
      by_cases X : x ∈ S ∩ holes <;> by_cases Y : y ∈ S ∩ holes <;> simp only [f,X,Y,dif_pos,dif_neg] at eq
      · by_contra neq
        exact separate x (mem_inter.mp X).2 y (mem_inter.mp Y).2 neq
          (hout x X).1 (eq ▸ (hout y Y).1)
      · exact False.elim ((hout x X).2.1 (eq ▸ outside y hy Y))
      · exact False.elim ((hout y Y).2.1 (eq ▸ outside x hx X))
      · exact eq
  obtain ⟨f,hinj,hadj⟩ := (all_card_le_biUnion_card_iff_exists_injective G).mp hall
  exact ⟨Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, hadj⟩

end WeightedPaper.Repair
