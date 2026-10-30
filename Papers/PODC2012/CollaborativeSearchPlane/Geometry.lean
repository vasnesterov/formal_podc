import Papers.PODC2012.CollaborativeSearchPlane.Phases

/-!
# Grid geometry for the upper bounds

* `card_ballFinset_le` — `|B(R)| ≤ (2R+1)²`;
* `card_near_ge` — if `d(s, τ) ≤ R` and `r ≤ R`, the ball `B(R)` contains at least
  `(r/2 + 1)(r/2 + 2)/2` nodes within distance `r` of `τ` (a constant fraction of the ball of
  radius `r` around `τ`: the paper's "at least some constant fraction of the ball `B(τ, √tᵢ/2)` is
  contained in `Bᵢ`");
* `uniformBall_succ_ge` — the resulting lower bound on the success probability of a phase.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

theorem dist_add_le (u v : Node) : dist (u + v) ≤ dist u + dist v := by
  unfold dist
  simp only [Prod.fst_add, Prod.snd_add]
  have := Int.natAbs_add_le u.1 v.1
  have := Int.natAbs_add_le u.2 v.2
  omega

theorem dist_sub_comm (u v : Node) : dist (u - v) = dist (v - u) := by
  unfold dist
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem card_ballFinset_le (R : ℕ) : (ballFinset R).card ≤ (2 * R + 1) ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset (fun u : Node => dist u ≤ R)
    ((Icc (-(R : ℤ)) R) ×ˢ (Icc (-(R : ℤ)) R)))
  rw [Finset.card_product, Int.card_Icc] at h
  have e : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
  rw [e] at h
  unfold ballFinset
  nlinarith [h]

/-- A node on a geodesic from `τ` to the source at distance `m ≤ d(s, τ)` from `τ`. -/
theorem exists_geodesic (τ : Node) (m : ℕ) (hm : m ≤ dist τ) :
    ∃ w : Node, dist w = m ∧ dist (τ - w) = dist τ - m := by
  obtain ⟨x, y⟩ := τ
  set a := min m x.natAbs
  set b := m - a
  refine ⟨(if 0 ≤ x then (a : ℤ) else -(a : ℤ), if 0 ≤ y then (b : ℤ) else -(b : ℤ)), ?_, ?_⟩
  · unfold dist at hm ⊢
    simp only at hm ⊢
    split_ifs <;> omega
  · unfold dist at hm ⊢
    simp only [Prod.fst_sub, Prod.snd_sub] at hm ⊢
    split_ifs <;> omega

theorem two_mul_sum_range_succ (m : ℕ) : 2 * ∑ n ∈ range m, (n + 1) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; ring

/-- The ball of radius `r'` around any node `c` has at least `(r'+1)(r'+2)/2` nodes. -/
theorem card_ball_around_ge (c : Node) (r' : ℕ) (A : Finset Node)
    (hA : ∀ v : Node, dist (v - c) ≤ r' → v ∈ A) :
    (r' + 1) * (r' + 2) ≤ 2 * A.card := by
  classical
  set Tri : Finset (ℕ × ℕ) := (range (r' + 1)).biUnion fun n => antidiagonal n
  have hdisj : ((range (r' + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint fun n => antidiagonal n := by
    intro n _ m _ hnm
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq hq'
    exact hnm (hq.symm.trans hq')
  have hcard : Tri.card = ∑ n ∈ range (r' + 1), (n + 1) := by
    rw [Finset.card_biUnion hdisj]
    simp
  have hinj : Tri.card ≤ A.card := by
    refine Finset.card_le_card_of_injOn (fun q => c + quad q) ?_ ?_
    · intro q hq
      simp only [Tri, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio,
        Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal, exists_prop] at hq
      obtain ⟨n, hn, hq⟩ := hq
      apply hA
      simp only [add_sub_cancel_left]
      rw [dist_quad]; omega
    · intro q _ q' _ h
      exact quad_injective (add_left_cancel h)
  have h2 : 2 * ∑ n ∈ range (r' + 1), (n + 1) = (r' + 1) * (r' + 2) :=
    two_mul_sum_range_succ (r' + 1)
  rw [← hcard] at h2
  omega

/-- If `d(s, τ) ≤ R` and `r ≤ R`, at least `(r/2+1)(r/2+2)/2` nodes of `B(R)` lie within distance
`r` of `τ`. -/
theorem card_near_ge {R r : ℕ} (hr : r ≤ R) {τ : Node} (hτ : dist τ ≤ R) :
    (r / 2 + 1) * (r / 2 + 2) ≤ 2 * ((ballFinset R).filter fun v => dist (v - τ) ≤ r).card := by
  classical
  set r' := r / 2
  -- the centre `c` of a ball of radius `r'` inside `B(R) ∩ B(τ, r)`
  obtain ⟨c, hc1, hc2⟩ : ∃ c : Node, dist (τ - c) ≤ r' ∧ dist c + r' ≤ R := by
    rcases le_total r' (dist τ) with h | h
    · obtain ⟨w, hw1, hw2⟩ := exists_geodesic τ r' h
      refine ⟨τ - w, ?_, ?_⟩
      · simp [hw1]
      · omega
    · refine ⟨0, by simpa using h, ?_⟩
      simp only [dist, Prod.fst_zero, Prod.snd_zero, Int.natAbs_zero]
      omega
  apply card_ball_around_ge c r'
  intro v hv
  rw [Finset.mem_filter, mem_ballFinset]
  constructor
  · have := dist_add_le c (v - c)
    simp only [add_sub_cancel] at this
    omega
  · have := dist_add_le (v - c) (c - τ)
    have e : v - c + (c - τ) = v - τ := by abel
    rw [e, dist_sub_comm c τ] at this
    omega

/-- The success probability of a phase "uniform node of `B(R)`, spiral of length `t`" when
`d(s, τ) ≤ R`, `r ≤ R` and `σ r² ≤ t`. -/
theorem uniformBall_succ_ge {σ R r t : ℕ} (hr : r ≤ R) (hrt : σ * r ^ 2 ≤ t) {τ : Node}
    (hτ : dist τ ≤ R) :
    ENNReal.ofReal (((r / 2 + 1) * (r / 2 + 2) : ℕ) / (2 * (2 * R + 1) ^ 2 : ℝ))
      ≤ uniformBall R (spiralSucc σ τ t) := by
  classical
  rw [uniformBall_apply]
  have hsub : ((ballFinset R).filter fun v => dist (v - τ) ≤ r)
      ⊆ (ballFinset R).filter (· ∈ spiralSucc σ τ t) := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    simp only [spiralSucc, Set.mem_ofPred_eq]
    exact le_trans (Nat.mul_le_mul_left σ (Nat.pow_le_pow_left hv.2 2)) hrt
  have h1 := card_near_ge hr hτ
  have h2 := Finset.card_le_card hsub
  have h3 := card_ballFinset_le R
  have hpos : 0 < (ballFinset R).card := (ballFinset_nonempty R).card_pos
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  have e1 : ENNReal.ofReal (((r / 2 + 1) * (r / 2 + 2) : ℕ) : ℝ)
      = (((r / 2 + 1) * (r / 2 + 2) : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
  have e2 : ENNReal.ofReal (2 * (2 * R + 1) ^ 2 : ℝ) = ((2 * (2 * R + 1) ^ 2 : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  rw [e1, e2]
  calc (((r / 2 + 1) * (r / 2 + 2) : ℕ) : ℝ≥0∞) / ((2 * (2 * R + 1) ^ 2 : ℕ) : ℝ≥0∞)
      ≤ ((2 * ((ballFinset R).filter (· ∈ spiralSucc σ τ t)).card : ℕ) : ℝ≥0∞)
          / ((2 * (ballFinset R).card : ℕ) : ℝ≥0∞) := by
        refine ENNReal.div_le_div ?_ ?_
        · exact_mod_cast h1.trans (Nat.mul_le_mul_left 2 h2)
        · exact_mod_cast Nat.mul_le_mul_left 2 h3
    _ = _ := by
        push_cast
        rw [ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- Success probability of a phase "uniform node of `B(R)`, spiral of length `t = ⌊Y⌋`" when
`d(s, τ) ≤ R`, `1 ≤ R` and `R² ≤ X`: at least `min(1/32, Y/(72 σ X))`. -/
theorem uniformBall_succ_ge' {σ : ℕ} (hσ : 1 ≤ σ) {R t : ℕ} {X Y : ℝ} (hR1 : 1 ≤ R)
    (hRX : (R : ℝ) ^ 2 ≤ X) (hY : Y < t + 1) {τ : Node} (hτ : dist τ ≤ R) :
    ENNReal.ofReal (min (1 / 32) (Y / (72 * σ * X))) ≤ uniformBall R (spiralSucc σ τ t) := by
  set n := t / σ
  set r := min (Nat.sqrt n) R
  have hrR : r ≤ R := min_le_right _ _
  have hrt : σ * r ^ 2 ≤ t := by
    have h1 : r ^ 2 ≤ n := (Nat.pow_le_pow_left (min_le_left _ _) 2).trans (Nat.sqrt_le' n)
    calc σ * r ^ 2 ≤ σ * n := Nat.mul_le_mul_left σ h1
      _ ≤ t := Nat.mul_div_le t σ
  refine le_trans ?_ (uniformBall_succ_ge hrR hrt hτ)
  apply ENNReal.ofReal_le_ofReal
  set Z := (r / 2 + 1) * (r / 2 + 2)
  have hZ : (r + 1) ^ 2 ≤ 4 * Z := by
    have h1 : r + 1 ≤ 2 * (r / 2 + 1) := by omega
    have h2 : r + 1 ≤ 2 * (r / 2 + 2) := by omega
    calc (r + 1) ^ 2 = (r + 1) * (r + 1) := by ring
      _ ≤ (2 * (r / 2 + 1)) * (2 * (r / 2 + 2)) := Nat.mul_le_mul h1 h2
      _ = 4 * Z := by ring
  have hZ' : ((r : ℝ) + 1) ^ 2 ≤ 4 * Z := by exact_mod_cast hZ
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hden : (0 : ℝ) < 2 * (2 * R + 1) ^ 2 := by positivity
  have hZ0 : (0 : ℝ) ≤ Z := by positivity
  rw [le_div_iff₀ hden]
  rcases le_total (Nat.sqrt n) R with hsq | hsq
  · have hr : r = Nat.sqrt n := min_eq_left hsq
    have h1 : n + 1 ≤ (r + 1) ^ 2 := by rw [hr]; exact Nat.lt_succ_sqrt' n
    have h2 : t < σ * (n + 1) := Nat.lt_mul_div_succ t (by omega)
    have h1' : ((n : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := by exact_mod_cast h1
    have h2' : (t : ℝ) + 1 ≤ σ * ((n : ℝ) + 1) := by exact_mod_cast h2
    have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
    have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hRX
    have h3 : Y < σ * (4 * Z) := by
      calc Y < t + 1 := hY
        _ ≤ σ * ((n : ℝ) + 1) := h2'
        _ ≤ σ * ((r : ℝ) + 1) ^ 2 := by gcongr
        _ ≤ σ * (4 * Z) := by gcongr
    have h5 : (2 * (R : ℝ) + 1) ^ 2 ≤ 9 * X := by nlinarith
    rcases le_or_gt Y 0 with hY0 | hY0
    · have : Y / (72 * σ * X) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hY0 (by positivity)
      have : min (1 / 32) (Y / (72 * σ * X)) ≤ 0 := (min_le_right _ _).trans this
      nlinarith
    calc min (1 / 32) (Y / (72 * σ * X)) * (2 * (2 * R + 1) ^ 2)
        ≤ Y / (72 * σ * X) * (2 * (2 * R + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hden.le
      _ ≤ Y / (72 * σ * X) * (18 * X) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Y / (4 * σ) := by field_simp; ring
      _ ≤ Z := by rw [div_le_iff₀ (by positivity)]; linarith
  · have hr : r = R := min_eq_right hsq
    rw [hr] at hZ'
    have hR0 : (0 : ℝ) ≤ R := by positivity
    have h5 : (2 * (R : ℝ) + 1) ^ 2 ≤ 4 * ((R : ℝ) + 1) ^ 2 := by nlinarith
    calc min (1 / 32) (Y / (72 * σ * X)) * (2 * (2 * R + 1) ^ 2)
        ≤ 1 / 32 * (2 * (2 * R + 1) ^ 2) := mul_le_mul_of_nonneg_right (min_le_left _ _) hden.le
      _ ≤ (Z : ℝ) := by nlinarith

end Podc.CollaborativeSearchPlane
