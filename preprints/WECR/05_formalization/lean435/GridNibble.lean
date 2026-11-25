import GridGrowth
import GridRate
import GridSpectrum
import SimpleIncidence

namespace WeightedPaper.Repair.Grid
open Finset Filter Pseudorandom
open scoped Classical Topology

private theorem polynomial_le_nibble_size (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ d : ℝ in atTop, 4*d^4 ≤ Real.exp (d^ε) := by
  have ratio := (tendsto_exp_div_rpow_atTop (4/ε)).comp (tendsto_rpow_atTop hε)
  filter_upwards [ratio.eventually_ge_atTop 4, eventually_gt_atTop (0:ℝ)] with d h hd
  change 4 ≤ Real.exp (d^ε)/(d^ε)^(4/ε) at h
  have exponent : (d^ε)^(4/ε) = d^4 := by
    rw [← Real.rpow_mul hd.le, mul_div_cancel₀ _ hε.ne']
    norm_num
  rw [exponent] at h
  exact (le_div_iff₀ (by positivity)).mp h

private theorem degree_tendsto (b : ℕ) (hb : 0 < b) :
    Tendsto (fun q : ℕ => (b:ℝ)*(2*(q:ℝ)-1)) atTop atTop := by
  have B : (1:ℝ) ≤ b := by exact_mod_cast hb
  refine tendsto_atTop_mono' (f₁ := fun q : ℕ => (q:ℝ)) atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ)] with q hq
  have Q : (1:ℝ) ≤ q := by exact_mod_cast hq
  calc
    (q:ℝ) ≤ 2*q-1 := by linarith
    _ ≤ (b:ℝ)*(2*q-1) := le_mul_of_one_le_left (by linarith) B

/-- Polynomial numbers of incidence triples and tests satisfy the nibble
bounds for every sufficiently large grid at fixed cell size. -/
private theorem size_budgets (b : ℕ) (hb : 0 < b) (Δ₀ : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      let d : ℝ := b*(2*(q:ℝ)-1)
      let N : ℝ := b*q^2
      Δ₀ ≤ d ∧ N*d*d ≤ Real.exp (d^((1/1800:ℝ)^2)) ∧
        2*N*(d+1) ≤ Real.exp (d^((1/1800:ℝ)^2)) := by
  have big := degree_tendsto b hb
  filter_upwards [big.eventually (polynomial_le_nibble_size ((1/1800:ℝ)^2) (by positivity)),
    big.eventually_ge_atTop Δ₀, eventually_ge_atTop (1:ℕ)] with q hsize hΔ hq
  dsimp only at hsize hΔ ⊢
  let d : ℝ := b*(2*(q:ℝ)-1)
  let N : ℝ := b*q^2
  have Q : (1:ℝ) ≤ q := by exact_mod_cast hq
  have B : (1:ℝ) ≤ b := by exact_mod_cast hb
  have bd : (b:ℝ)*q ≤ d := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have bq : 1 ≤ (b:ℝ)*q := one_le_mul_of_one_le_of_one_le B Q
  have hd := bq.trans bd
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have size : N ≤ d^2 := by
    calc
      N ≤ ((b:ℝ)*q)^2 := by
        dsimp [N]
        nlinarith [mul_nonneg (sq_nonneg (q:ℝ)) (mul_nonneg (Nat.cast_nonneg b) (sub_nonneg.mpr B))]
      _ ≤ d^2 := pow_le_pow_left₀ (by positivity) bd _
  have d2 : d ≤ d^2 := by nlinarith
  have first : N*d*d ≤ 4*d^4 := by
    calc
      N*d*d ≤ d^2*d*d := by gcongr
      _ = d^4 := by ring
      _ ≤ 4*d^4 := by nlinarith [sq_nonneg (d^2)]
  have second : 2*N*(d+1) ≤ 4*d^4 := by
    calc
      2*N*(d+1) ≤ 2*d^2*(2*d^2) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  exact ⟨hΔ, first.trans hsize, second.trans hsize⟩

private theorem filter_complement_le {A : Type*} [Fintype A] (X : Finset A) (p : A → Prop) :
    ((Xᶜ).filter p).card ≤ (Xᶜ).card :=
  card_filter_le _ _

private theorem filter_add_complement {A : Type*} [Fintype A] (X : Finset A) (p : A → Prop) :
    (X.filter p).card + ((Xᶜ).filter p).card = (univ.filter p).card := by
  classical
  have e : ((univ : Finset A).filter p).filter (· ∈ X) = X.filter p := by
    ext x; simp [and_comm]
  have e' : ((univ : Finset A).filter p).filter (· ∉ X) = Xᶜ.filter p := by
    ext x; simp [and_comm]
  rw [← e, ← e']
  exact card_filter_add_card_filter_not (· ∈ X)

set_option maxHeartbeats 1000000 in
/-- The incidence and spectral hypotheses hold uniformly for balanced
free sets that omit at most r+2 ordinary vertices per side. -/
theorem grid_hybrid_certificates (b : ℕ) (hb : 0 < b) (Δ₀ : ℝ) :
    ∀ᶠ q : ℕ in atTop, 12 ≤ q ∧
      ∀ (m : Marked q ↪ CellVertex q b),
      let d := b*(2*q-1)
      let A := Ordinary (Fin (Nat.sqrt q)) (Intact m)
      ∀ (X Y : Fin d → Finset A), (∀ i, (X i).card = (Y i).card) →
        (∀ i, Fintype.card A ≤ (X i).card+(Nat.sqrt q+2)) →
        (∀ i, Fintype.card A ≤ (Y i).card+(Nat.sqrt q+2)) →
        Nonempty (HybridCertificate (1/4) Δ₀
          (supportLeft (R := support m)) supportRight (support m) X Y) := by
  filter_upwards [grid_parameters_pass b hb, size_budgets b hb Δ₀,
    eventually_ge_atTop (12:ℕ)] with q budgets sizes hq
  refine ⟨hq, ?_⟩
  intro m d A X Y balanced leftMiss rightMiss
  letI : Fintype A := inferInstanceAs (Fintype (Ordinary (Fin (Nat.sqrt q)) (Intact m)))
  letI : DecidableEq A := Classical.decEq A
  let σ : ℝ := ((q:ℝ)-1)/(2*q-1)
  let η : ℝ := ((Nat.sqrt q : ℝ)+2)/d
  have Q : (12:ℝ) ≤ q := by exact_mod_cast hq
  have dpos : 0 < d := Nat.mul_pos hb (by omega)
  have dc : (d:ℝ) = (b:ℝ)*(2*(q:ℝ)-1) := by
    simp [d, Nat.cast_sub (by omega : 1 ≤ 2*q)]
  have dr : (0:ℝ) < d := by exact_mod_cast dpos
  have ηd : η*d = (Nat.sqrt q : ℝ)+2 := div_mul_cancel₀ _ dr.ne'
  have η0 : 0 ≤ η := by dsimp [η]; positivity
  have η1 : η < 1 := by
    have hroot := two_root_le q hq
    have hlt : Nat.sqrt q + 2 < d := by
      have bd : 2*q-1 ≤ d := Nat.le_mul_of_pos_left _ hb
      omega
    exact (div_lt_one dr).2 (by exact_mod_cast hlt)
  have d1 : (1:ℝ) ≤ d := by exact_mod_cast dpos
  have ncard : (Fintype.card A : ℝ) = (b:ℝ)*q^2 := by
    exact_mod_cast ordinary_count m
  have reg := support_degrees m
  obtain ⟨h,hh,mix,p1,p2⟩ := budgets
  have sizes' : Δ₀ ≤ (d:ℝ) ∧
      (Fintype.card A : ℝ)*d*d ≤ Real.exp ((d:ℝ)^((1/1800:ℝ)^2)) ∧
      2*(Fintype.card A : ℝ)*(d+1) ≤ Real.exp ((d:ℝ)^((1/1800:ℝ)^2)) := by
    simpa only [dc, ncard] using sizes
  have error : demandError (1/4) d η d = nibbleBound d η d := by
    unfold demandError nibbleBound
    norm_num
  have missingX i : ((X i)ᶜ).card ≤ Nat.sqrt q+2 := by
    have e := card_add_card_compl (X i)
    have le := leftMiss i
    omega
  have missingY i : ((Y i)ᶜ).card ≤ Nat.sqrt q+2 := by
    have e := card_add_card_compl (Y i)
    have le := rightMiss i
    omega
  have left i x : (((Y i)ᶜ.filter (support m x)).card : ℝ) ≤ η*d := by
    rw [ηd]
    exact_mod_cast (filter_complement_le (Y i) (support m x)).trans (missingY i)
  have right i y : (((X i)ᶜ.filter (fun x => support m x y)).card : ℝ) ≤ η*d := by
    rw [ηd]
    exact_mod_cast (filter_complement_le (X i) _).trans (missingX i)
  have ctest : Fintype.card (TestIndex (Fin d) A A) = 2*Fintype.card A*(d+1) := by
    simp only [TestIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  refine ⟨{
    pairs := eligibleSupport (support m) X Y
    Δ := d
    η := η
    d := d
    σ := σ
    β := η
    h := h
    large := sizes'.1
    eta0 := η0
    eta1 := η1
    positive := dpos
    regA := reg.1
    regB := reg.2
    sideCard := rfl
    freeCard := balanced
    eligible := fun p hp => (eligibleSupport_mem (support m) X Y p).mp hp
    degree_le := ?_
    codegree_le := ?_
    size_le := ?_
    test_le := ?_
    demandA := ?_
    demandB := ?_
    sigma0 := div_nonneg (by linarith) (by linarith)
    sigma1 := (div_le_iff₀ (by linarith : 0 < 2*(q:ℝ)-1)).2 (by linarith)
    beta0 := η0
    spectrum := ?_
    missedA := left
    missedB := right
    length := hh
    mixing := by change σ^h ≤ 1/(2*(Fintype.card A : ℝ)); rw [ncard]; exact mix
    budget1 := ?_
    budget2 := ?_
  }⟩
  · intro v
    change (degree (supportTriples (support m) X Y) v : ℝ) ≤ _
    exact_mod_cast support_degree_upper (support m) X Y d reg.1 reg.2 (by simp) v
  · intro u v ne
    have hle : (codegree (supportTriples (support m) X Y) u v : ℝ) ≤ 1 := by
      exact_mod_cast support_codegree (support m) X Y u v ne
    change (codegree (supportTriples (support m) X Y) u v : ℝ) ≤ _
    exact hle.trans (Real.one_le_rpow d1 (by norm_num : 0 ≤ 1-(1/4:ℝ)))
  · change ((supportTriples (support m) X Y).card : ℝ) ≤ _
    rw [show (1/4:ℝ)/450 = 1/1800 by norm_num]
    apply le_trans _ sizes'.2.1
    have hle := support_triple_count (support m) X Y d reg.1
    simp only [Fintype.card_fin] at hle
    exact_mod_cast (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hle :
      (supportTriples (support m) X Y).card ≤ Fintype.card A*d*d)
  · rw [ctest]
    push_cast
    convert sizes'.2.2 using 2 <;> norm_num
  · intro i x hx
    change _ ≤ (degree (supportTriples (support m) X Y) (.inl (i,x)) : ℝ)
    rw [support_degree_left _ _ _ _ _ hx]
    have cs := filter_add_complement (Y i) (support m x)
    rw [reg.1] at cs
    have e : ((Y i).filter (support m x)).card + (((Y i)ᶜ).filter (support m x)).card = d := cs
    have er : (((Y i).filter (support m x)).card : ℝ) +
        (((Y i)ᶜ).filter (support m x)).card = d := by exact_mod_cast e
    nlinarith only [er, left i x]
  · intro i y hy
    change _ ≤ (degree (supportTriples (support m) X Y) (.inr (.inl (i,y))) : ℝ)
    rw [support_degree_right _ _ _ _ _ hy]
    have cs := filter_add_complement (X i) (fun x => support m x y)
    rw [reg.2] at cs
    have e : ((X i).filter (fun x => support m x y)).card + (((X i)ᶜ).filter (fun x => support m x y)).card = d := cs
    have er : (((X i).filter (fun x => support m x y)).card : ℝ) +
        (((X i)ᶜ).filter (fun x => support m x y)).card = d := by exact_mod_cast e
    nlinarith only [er, right i y]
  · rw [dc]
    exact grid_reserve_contraction m (by omega) hb
  · rw [error]
    have hp : 3*(2*(h:ℝ))*(η+nibbleBound d η d/d) ≤ 1/2 := by
      simpa only [η, dc, show ∀ h : ℕ, 2*(h:ℝ)+1-1 = 2*(h:ℝ) from fun _ => by ring] using p1
    push_cast
    exact hp
  · simp only [Fintype.card_fin, error]
    have hl : ((2*h-1 : ℕ) : ℝ) = 2*(h:ℝ)+1-2 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hp : 6*(2*(h:ℝ)+1)*(2*nibbleBound d η d+(2*(h:ℝ)+1-2)*d*
        (η+nibbleBound d η d/d))/d+6*(2*(h:ℝ)+1-1)^2*(η+nibbleBound d η d/d) ≤ 4/27 := by
      simpa only [η, dc] using p2
    rw [hl]
    push_cast
    convert hp using 1
    ring

end WeightedPaper.Repair.Grid
