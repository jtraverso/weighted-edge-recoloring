module

public import WeightedRecolouring.SharpGraph
public import Mathlib.Tactic.FinCases

@[expose] public section


namespace WeightedRecolouring.Example
open Finset SimpleGraph
set_option maxHeartbeats 1000000

private theorem edge_injective : Function.Injective edge := by decide

private def assigned (f : Fin 6 → Fin 3) (e : Sym2 (Fin 6)) (i : Fin 3) : ℕ :=
  ∑ j : Fin 6, if edge j=e ∧ f j=i then 1 else 0

private theorem assigned_at (f : Fin 6 → Fin 3) (j : Fin 6) (i : Fin 3) :
    assigned f (edge j) i=if f j=i then 1 else 0 := by
  unfold assigned
  rw [sum_eq_single j]
  · simp
  · intro k _ hk
    simp [show edge k≠edge j from fun h => hk (edge_injective h)]
  · simp

private theorem assigned_off (f : Fin 6 → Fin 3) (e : Sym2 (Fin 6)) (i : Fin 3)
    (h : ¬∃ j, edge j=e) : assigned f e i=0 := by
  apply sum_eq_zero
  intro j _
  simp [show edge j≠e from fun he => h ⟨j,he⟩]

private def initial : graph.EdgeColoring 3 where
  col := assigned ![0,1,2,2,0,1]
  sum_col := by decide
  proper := by decide

private theorem colourMass_initial : ∀ i, initial.colourMass i=2 := by decide

private theorem exists_assignment (C : graph.EdgeColoring 3) :
    ∃ f : Fin 6 → Fin 3, C.col=assigned f := by
  classical
  have choose_colour (j : Fin 6) : ∃ i : Fin 3, ∀ l : Fin 3,
      C.col (edge j) l=(if i=l then 1 else 0) := by
    have h := C.sum_col (edge j)
    have hmult : graph.mult (edge j)=1 := by simp [graph, show ∃ l,edge l=edge j from ⟨j,rfl⟩]
    rw [hmult,Fin.sum_univ_three] at h
    obtain h0|h1|h2 : C.col (edge j) 0=1 ∨ C.col (edge j) 1=1 ∨ C.col (edge j) 2=1 := by omega
    · exact ⟨0,fun l => by fin_cases l <;> simp <;> omega⟩
    · exact ⟨1,fun l => by fin_cases l <;> simp <;> omega⟩
    · exact ⟨2,fun l => by fin_cases l <;> simp <;> omega⟩
  choose f hf using choose_colour
  refine ⟨f,?_⟩
  funext e i
  by_cases h : ∃ j,edge j=e
  · obtain ⟨j,rfl⟩ := h
    rw [assigned_at]
    exact hf j i
  · rw [assigned_off _ _ _ h]
    apply Nat.eq_zero_of_le_zero
    calc
      C.col e i ≤ ∑ j,C.col e j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
      _ = 0 := by rw [C.sum_col]; simp [graph,h]

private def coversHeavy (f : Fin 6 → Fin 3) (i : Fin 3) : ℕ :=
  ∑ e : Sym2 (Fin 6), ((if (2 : Fin 6)∈e then 1 else 0)+(if (4 : Fin 6)∈e then 1 else 0)) * assigned f e i

private theorem finite_certificate (f : Fin 6 → Fin 3)
    (hp : ∀ v i, (∑ e ∈ univ.filter (fun e : Sym2 (Fin 6) => v∈e), assigned f e i)≤1) :
    ∃ a b, coversHeavy f a=2 ∧ coversHeavy f b=0 := by
  have distinct_colours {j l : Fin 6} (hjl : j≠l) {v : Fin 6}
      (hj : v∈edge j) (hl : v∈edge l) : f j≠f l := by
    intro hc
    let T := univ.filter (fun e : Sym2 (Fin 6) => v∈e)
    have hjT : edge j∈T := by simpa [T] using hj
    have hlT : edge l∈T := by simpa [T] using hl
    have hne : edge j≠edge l := fun h => hjl (edge_injective h)
    have hl' : edge l∈T.erase (edge j) := mem_erase.mpr ⟨hne.symm,hlT⟩
    have hc' : assigned f (edge l) (f j)=1 := by simp [assigned_at,hc]
    have hj' : assigned f (edge j) (f j)=1 := by simp [assigned_at]
    have hsum : assigned f (edge l) (f j) ≤ ∑ e∈T.erase (edge j), assigned f e (f j) :=
      single_le_sum (f:=fun e => assigned f e (f j)) (fun _ _ => Nat.zero_le _) hl'
    have hsub := sum_erase_add T (fun e => assigned f e (f j)) hjT
    have hh := hp v (f j)
    change (∑ e∈T,assigned f e (f j))≤1 at hh
    omega
  have h01 : f 0≠f 1 := distinct_colours (by decide) (v:=0) (by decide) (by decide)
  have h02 : f 0≠f 2 := distinct_colours (by decide) (v:=1) (by decide) (by decide)
  have h12 : f 1≠f 2 := distinct_colours (by decide) (v:=2) (by decide) (by decide)
  have h50 : f 5≠f 0 := distinct_colours (by decide) (v:=1) (by decide) (by decide)
  have h52 : f 5≠f 2 := distinct_colours (by decide) (v:=1) (by decide) (by decide)
  have third (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) (v : Fin 3)
      (hv₁ : v≠i) (hv₂ : v≠j) : v=k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases v <;> simp_all
  have h5 := third (f 0) (f 2) (f 1) h02 h01 h12.symm (f 5) h50 h52
  have hcovers (i : Fin 3) :
      coversHeavy f i=(if f 1=i then 1 else 0)+(if f 2=i then 1 else 0)+(if f 5=i then 1 else 0) := by
    unfold coversHeavy assigned
    simp only [mul_sum]
    rw [sum_comm,Fin.sum_univ_six]
    have hs (j : Fin 6) :
        (∑ e : Sym2 (Fin 6), ((if (2 : Fin 6)∈e then 1 else 0)+(if (4 : Fin 6)∈e then 1 else 0)) *
          (if edge j=e ∧ f j=i then 1 else 0))=
        ((if (2 : Fin 6)∈edge j then 1 else 0)+(if (4 : Fin 6)∈edge j then 1 else 0))*
          (if f j=i then 1 else 0) := by
      rw [sum_eq_single (edge j)]
      · simp
      · intro e _ he
        simp [Ne.symm he]
      · simp
    simp only [hs]
    have hcases : ∀ j : Fin 6, ((if (2 : Fin 6)∈edge j then 1 else 0) +
        (if (4 : Fin 6)∈edge j then 1 else 0) : ℕ) =
        if j=1 ∨ j=2 ∨ j=5 then 1 else 0 := by decide
    simp only [hcases]
    simp
  exact ⟨f 1,f 0,by simp [hcovers,h5,h12.symm],by simp [hcovers,h5,h01.symm,h02.symm]⟩

private theorem support_connected : support.Connected := by
  have root (v : Fin 6) : support.Reachable 0 v := by
    have adj01 : support.Adj 0 1 := by decide
    have adj02 : support.Adj 0 2 := by decide
    have adj03 : support.Adj 0 3 := by decide
    have adj14 : support.Adj 1 4 := by decide
    have adj35 : support.Adj 3 5 := by decide
    fin_cases v
    · exact Reachable.refl _
    · exact adj01.reachable
    · exact adj02.reachable
    · exact adj03.reachable
    · exact adj01.reachable.trans adj14.reachable
    · exact adj03.reachable.trans adj35.reachable
  exact SimpleGraph.Connected.mk (fun u v => (root u).symm.trans (root v))

private theorem support_not_two_colourable : ¬support.Colorable 2 := by
  rintro ⟨C⟩
  have h : ∀ a b c : Fin 2, a≠b → a≠c → b≠c → False := by decide
  exact h (C 0) (C 1) (C 2)
    (C.valid (by decide : support.Adj 0 1)) (C.valid (by decide : support.Adj 0 2))
    (C.valid (by decide : support.Adj 1 2))

/-- Three classes of size two can be realized, but every such proper
colouring of this simple graph has two loads differing by two. -/
theorem sharp_connected_example :
    (∀ e, graph.mult e≤1) ∧ support.Connected ∧ ¬support.Colorable 2 ∧
      (∀ v, 0≤weights v ∧ weights v≤1) ∧
      (∃ C : graph.EdgeColoring 3, ∀ i,C.colourMass i=2) ∧
      ∀ C : graph.EdgeColoring 3, (∀ i,C.colourMass i=2) →
        ∃ a b, load C weights a-load C weights b=2 := by
  refine ⟨by decide, support_connected, support_not_two_colourable, ?_,
    ⟨initial,colourMass_initial⟩, ?_⟩
  · intro v
    by_cases h : v=2 ∨ v=4 <;> simp [weights,heavy,h]
  intro C _
  obtain ⟨f,hf⟩ := exists_assignment C
  have hp (v : Fin 6) (i : Fin 3) :
      (∑ e ∈ univ.filter (fun e : Sym2 (Fin 6) => v∈e),assigned f e i)≤1 := by
    simpa only [hf] using C.proper v i
  obtain ⟨a,b,ha,hb⟩ := finite_certificate f hp
  have hload (i : Fin 3) : load C weights i=(coversHeavy f i:ℝ) := by
    unfold load
    rw [Fin.sum_univ_six]
    have hw : weights 0=0 ∧ weights 1=0 ∧ weights 2=1 ∧
        weights 3=0 ∧ weights 4=1 ∧ weights 5=0 := by norm_num [weights,heavy]
    obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hw
    rw [h0,h1,h2,h3,h4,h5]
    simp only [zero_mul,one_mul,zero_add,add_zero,←Nat.cast_add]
    have hnat : (C.colourGraph i).degree 2+(C.colourGraph i).degree 4=coversHeavy f i := by
      unfold coversHeavy
      simp only [add_mul,sum_add_distrib,ite_mul,one_mul,zero_mul,←sum_filter,
        MultiGraph.degree,MultiGraph.EdgeColoring.colourGraph,hf]
    exact_mod_cast hnat
  exact ⟨a,b,by rw [hload,hload,ha,hb]; norm_num⟩

end WeightedRecolouring.Example
