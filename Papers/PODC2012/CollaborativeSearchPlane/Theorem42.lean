import Papers.PODC2012.CollaborativeSearchPlane.Theorem41

/-!
# Theorem 4.2: a lower bound with `k^ε`-approximate knowledge of `k`

Every agent `a` receives an estimate `k̃ₐ` with `k̃ₐ^(1 - ε(k̃ₐ)) ≤ k ≤ k̃ₐ` and moves according to a
law `A k̃ₐ` depending only on its estimate. If such an algorithm is `φ(k)`-competitive with `φ`
non-decreasing, then `φ(k) = Ω(ε(k) log k)` (`theorem_4_2`, with the explicit bound
`φ(k) ≥ ε(k) · log k / (64 log 4)` for all `k ≥ 1`, `theorem_4_2_explicit`).

As in the paper, all agents receive the same estimate `k̃`; every `kᵢ = 4ⁱ` with
`k̃^(1-ε) ≤ 4ⁱ ≤ k̃` is a possible number of agents, and the shells
`Sᵢ = {u : 2^(j₀+i) < d(u) ≤ 2^(j₀+i+1)}` (our indices are shifted by one) are pairwise disjoint and
each carries `Ω(W)` expected visits of one agent, `W = 4^j₀`, by time `2T = O(W φ(k̃))`.

The paper's conclusion `φ(k̃) = Ω(ε(k̃) log k̃)` also needs, when `ε(k̃) log k̃` is small (possibly no
`i` at all), the trivial bound `φ(k̃) = Ω(1)` (footnote 2: `T ≥ Ω(D²/k)`); we prove it with the same
shell argument for `k = k̃` agents (`one_div_le_of_competitive`).
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset Filter
open scoped ENNReal

/-- §4.2: an estimate `est` is a `k^ε`-approximation of the number `k` of agents if
`est^(1 - ε(est)) ≤ k ≤ est`. -/
def IsApprox (ε : ℕ → ℝ) (k est : ℕ) : Prop := (est : ℝ) ^ (1 - ε est) ≤ k ∧ k ≤ est

/-- §4.2: a search algorithm with advice (agent `a` with estimate `est a` moves according to
`A (est a)`) is `φ(k)`-competitive for `k^ε`-approximations if `T ≤ φ(k) (D + D²/k)` for every
`k ≥ 1`, every assignment of `k^ε`-approximate estimates to the `k` agents and every treasure
`τ ≠ s`. -/
def IsCompetitiveAdvice (A : ℕ → Measure Traj) (ε : ℕ → ℝ) (φ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ est : Fin k → ℕ, (∀ a, IsApprox ε k (est a)) → ∀ τ : Node, 1 ≤ dist τ →
    expectedTime (fun a => A (est a)) τ ≤ ENNReal.ofReal (φ k * optBound k τ)

/-! ### Disjoint dyadic shells -/

theorem disjoint_shell {a b : ℕ} (h : a ≠ b) :
    Disjoint (Ioc (2 ^ a) (2 ^ (a + 1))) (Ioc (2 ^ b) (2 ^ (b + 1))) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [mem_Ioc] at hn hn'
  rcases Nat.lt_or_gt_of_ne h with hab | hab
  · have : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    omega
  · have : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hab
    omega

/-- One agent of law `μ` and a finite family of "scales" `j ∈ J`: if with `κ j` agents every node of
the dyadic shell `2^(m j) < d(u) ≤ 2^(m j + 1)` is found within expected time `T` (`2T ≤ N + 1`),
the shells being distinct, then `∑_{j ∈ J} 4^(m j) / (2 κ j) ≤ N + 1`. -/
theorem family_bound (μ : Measure Traj) [IsProbabilityMeasure μ] (N : ℕ) (T : ℝ)
    (hN : 2 * T ≤ N + 1) (J : Finset ℕ) (κ m : ℕ → ℕ) (hm : Set.InjOn m J)
    (hκ : ∀ j ∈ J, 0 < κ j)
    (hE : ∀ j ∈ J, ∀ n ∈ Ioc (2 ^ m j) (2 ^ (m j + 1)), ∀ u : Node, dist u = n →
      expectedTime (fun _ : Fin (κ j) => μ) u ≤ ENNReal.ofReal T) :
    ∑ j ∈ J, (4 : ℝ) ^ m j / (2 * κ j) ≤ N + 1 := by
  classical
  have hshell : ∀ j ∈ J, (4 : ℝ) ^ m j / (2 * κ j)
      ≤ ∑ n ∈ Ioc (2 ^ m j) (2 ^ (m j + 1)), diagMass μ N n := by
    intro j hj
    have hk : (0 : ℝ) < κ j := by exact_mod_cast hκ j hj
    have h1 : ∀ n ∈ Ioc (2 ^ m j) (2 ^ (m j + 1)), (2 : ℝ) ^ m j / (2 * κ j) ≤ diagMass μ N n := by
      intro n hn
      refine le_trans ?_ (diagMass_ge μ (hκ j hj) N n T hN (hE j hj n hn))
      have : (2 : ℝ) ^ m j ≤ n := by
        have := (mem_Ioc.1 hn).1; exact_mod_cast this.le
      gcongr; linarith
    have h2 := Finset.card_nsmul_le_sum _ _ _ h1
    rw [Nat.card_Ioc, nsmul_eq_mul] at h2
    have e : ((2 ^ (m j + 1) - 2 ^ m j : ℕ) : ℝ) = 2 ^ m j := by
      rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))]; push_cast; rw [pow_succ]; ring
    rw [e] at h2
    calc (4 : ℝ) ^ m j / (2 * κ j) = 2 ^ m j * (2 ^ m j / (2 * κ j)) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; field_simp; ring
      _ ≤ _ := h2
  have hdisj : (J : Set ℕ).PairwiseDisjoint fun j => Ioc (2 ^ m j) (2 ^ (m j + 1)) := by
    intro i hi j hj hij
    exact disjoint_shell fun h => hij (hm hi hj h)
  calc ∑ j ∈ J, (4 : ℝ) ^ m j / (2 * κ j)
      ≤ ∑ j ∈ J, ∑ n ∈ Ioc (2 ^ m j) (2 ^ (m j + 1)), diagMass μ N n := Finset.sum_le_sum hshell
    _ = ∑ n ∈ J.biUnion fun j => Ioc (2 ^ m j) (2 ^ (m j + 1)), diagMass μ N n :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ N + 1 := sum_diagMass_le μ _ N

/-! ### Competitiveness on dyadic shells -/

theorem le_of_forall_ge_add {a b C : ℝ} {K : ℕ} (h : ∀ M ≥ K, a ≤ b + C * (1 / 2) ^ M) :
    a ≤ b := by
  have ht : Tendsto (fun M : ℕ => b + C * (1 / 2 : ℝ) ^ M) atTop (nhds (b + C * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
  rw [mul_zero, add_zero] at ht
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨K, h⟩)

section Advice

variable {A : ℕ → Measure Traj} [∀ x, IsProbabilityMeasure (A x)] {ε : ℕ → ℝ} {φ : ℕ → ℝ}

theorem isApprox_self (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) {k : ℕ} (hk : 1 ≤ k) : IsApprox ε k k := by
  refine ⟨?_, le_rfl⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc (k : ℝ) ^ (1 - ε k) ≤ (k : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk' (by linarith [(hε k).1])
    _ = k := Real.rpow_one _

theorem IsCompetitiveAdvice.pos (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) (hA : IsCompetitiveAdvice A ε φ)
    {k : ℕ} (hk : 1 ≤ k) : 0 < φ k :=
  pos_of_expectedTime_le (A k) hk (φ k) (hA k hk (fun _ => k) fun _ => isApprox_self hε hk)

/-- With `κ` agents that all receive the estimate `est` (a `k^ε`-approximation of `κ`) and
`κ ≤ 2^m`, every node of the shell `2^m < d(u) ≤ 2^(m+1)` is found in expected time
`≤ 8 φ(est) 4^m / κ`. -/
theorem shell_time_le (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) (hA : IsCompetitiveAdvice A ε φ)
    (hφ : Monotone φ) {est κ m : ℕ} (hκ : 1 ≤ κ) (happ : IsApprox ε κ est) (hκm : κ ≤ 2 ^ m)
    {n : ℕ} (hn : n ∈ Ioc (2 ^ m) (2 ^ (m + 1))) (u : Node) (hu : dist u = n) :
    expectedTime (fun _ : Fin κ => A est) u ≤ ENNReal.ofReal (8 * φ est * 4 ^ m / κ) := by
  refine (hA κ hκ (fun _ => est) (fun _ => happ) u
    (by rw [hu]; exact lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.1 hn).1)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hp := hA.pos hε hκ
  have hmono : φ κ ≤ φ est := hφ happ.2
  have hk : (0 : ℝ) < κ := by exact_mod_cast hκ
  rw [mem_Ioc] at hn
  have hn1 : (κ : ℝ) ≤ n := by
    have : κ ≤ n := le_trans hκm hn.1.le
    exact_mod_cast this
  have hn2 : (n : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast hn.2
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hopt : optBound κ u ≤ 8 * 4 ^ m / κ := by
    unfold optBound
    rw [hu]
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 / κ := by rw [le_div_iff₀ hk]; nlinarith
    have h2 : (n : ℝ) ^ 2 ≤ 4 * 4 ^ m := by
      have : (2 : ℝ) ^ (m + 1) * 2 ^ (m + 1) = 4 * 4 ^ m := by
        rw [← mul_pow, pow_succ]; norm_num; ring
      nlinarith
    have h3 : (n : ℝ) ^ 2 / κ ≤ 4 * 4 ^ m / κ := by gcongr
    have : 8 * (4 : ℝ) ^ m / κ = 4 * 4 ^ m / κ + 4 * 4 ^ m / κ := by ring
    linarith
  have hopt0 : 0 ≤ optBound κ u := by unfold optBound; positivity
  calc φ κ * optBound κ u ≤ φ est * optBound κ u := mul_le_mul_of_nonneg_right hmono hopt0
    _ ≤ φ est * (8 * 4 ^ m / κ) := mul_le_mul_of_nonneg_left hopt (hp.trans_le hmono).le
    _ = 8 * φ est * 4 ^ m / κ := by ring

/-- Footnote 2 (the trivial lower bound `T = Ω(D²/k)`) in the form needed for Theorem 4.2: every
competitive ratio is at least `1/32`. -/
theorem one_div_le_of_competitive (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1)
    (hA : IsCompetitiveAdvice A ε φ) (hφ : Monotone φ) {k : ℕ} (hk : 1 ≤ k) :
    1 / 32 ≤ φ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine le_of_forall_ge_add (C := k / 8) (K := k) fun M hM => ?_
  have hkM : k ≤ 2 ^ M := le_trans hM Nat.lt_two_pow_self.le
  set T : ℝ := 8 * φ k * 4 ^ M / k
  have hT0 : 0 ≤ T := by have := hA.pos hε hk; positivity
  have hN1 : 2 * T ≤ (⌈2 * T⌉₊ : ℝ) + 1 := by have := Nat.le_ceil (2 * T); linarith
  have hN2 : (⌈2 * T⌉₊ : ℝ) + 1 ≤ 2 * T + 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * T); linarith
  have hfam := family_bound (A k) ⌈2 * T⌉₊ T hN1 {0} (fun _ => k) (fun _ => M)
    (by simp) (by simp; omega) (by
      intro j _ n hn u hu
      exact shell_time_le hε hA hφ hk (isApprox_self hε hk) hkM hn u hu)
  simp only [sum_singleton] at hfam
  have h4 : (0 : ℝ) < 4 ^ M := by positivity
  have e : (1 / 2 : ℝ) ^ M * 4 ^ M = 2 ^ M := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, ← mul_assoc, ← mul_pow]; norm_num
  have h2M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  -- `4^M / (2k) ≤ 16 φ 4^M / k + 2`
  have : (4 : ℝ) ^ M / (2 * k) ≤ 16 * φ k * 4 ^ M / k + 2 := by
    have := hfam.trans hN2; simp only [T] at this
    have e2 : 2 * (8 * φ k * 4 ^ M / k) = 16 * φ k * 4 ^ M / k := by ring
    linarith [this]
  rw [div_le_iff₀ (by positivity)] at this
  have hφ' := hA.pos hε hk
  have h5 : (4 : ℝ) ^ M ≤ (16 * φ k * 4 ^ M / k + 2) * (2 * k) := this
  have h6 : (16 * φ k * 4 ^ M / k + 2) * (2 * k) = 32 * φ k * 4 ^ M + 4 * k := by
    field_simp; ring
  rw [h6] at h5
  -- divide by `32 · 4^M`
  have : 1 / 32 ≤ φ k + k / 8 * (1 / 2) ^ M := by
    have h7 : k / 8 * (1 / 2 : ℝ) ^ M * 4 ^ M = k / 8 * 2 ^ M := by rw [mul_assoc, e]
    have h8 : (k : ℝ) / 8 * 2 ^ M ≥ k / 8 := by nlinarith
    rw [← mul_le_mul_iff_of_pos_right h4, add_mul, h7]
    nlinarith
  exact this

/-- The scales of the proof of Theorem 4.2: the `i` with `est^(1 - ε(est)) ≤ 4ⁱ ≤ est`, i.e. the
possible numbers of agents `kᵢ = 4ⁱ` for the estimate `est`. -/
noncomputable def scales (ε : ℕ → ℝ) (est : ℕ) : Finset ℕ :=
  (range (Nat.log 4 est + 1)).filter fun i => (est : ℝ) ^ (1 - ε est) ≤ 4 ^ i

omit [∀ x, IsProbabilityMeasure (A x)] in
theorem isApprox_of_mem_scales {est i : ℕ} (hest : 1 ≤ est) (hi : i ∈ scales ε est) :
    IsApprox ε (4 ^ i) est := by
  simp only [scales, mem_filter, mem_range] at hi
  refine ⟨by exact_mod_cast hi.2, ?_⟩
  exact Nat.pow_le_of_le_log (by omega) (Nat.lt_succ_iff.1 hi.1)

/-- **The main estimate of Theorem 4.2**: `φ(k̃) ≥ #scales / 32`. -/
theorem card_scales_le (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) (hA : IsCompetitiveAdvice A ε φ)
    (hφ : Monotone φ) {est : ℕ} (hest : 1 ≤ est) :
    ((scales ε est).card : ℝ) / 32 ≤ φ est := by
  set L := Nat.log 4 est
  have hφ0 := hA.pos hε hest
  refine le_of_forall_ge_add (C := 1 / 8) (K := L) fun j0 hj0 => ?_
  set T : ℝ := 8 * φ est * 4 ^ j0
  have hT0 : 0 ≤ T := by positivity
  have hN1 : 2 * T ≤ (⌈2 * T⌉₊ : ℝ) + 1 := by have := Nat.le_ceil (2 * T); linarith
  have hN2 : (⌈2 * T⌉₊ : ℝ) + 1 ≤ 2 * T + 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * T); linarith
  have hfam := family_bound (A est) ⌈2 * T⌉₊ T hN1 (scales ε est) (fun i => 4 ^ i)
    (fun i => j0 + i) (fun a _ b _ h => by simpa using h) (fun i _ => by positivity) (by
      intro i hi n hn u hu
      have hiL : i ≤ L := by
        simp only [scales, mem_filter, mem_range] at hi; omega
      have hκm : 4 ^ i ≤ 2 ^ (j0 + i) := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have := shell_time_le hε hA hφ (Nat.one_le_pow _ _ (by norm_num))
        (isApprox_of_mem_scales hest hi) hκm hn u hu
      refine this.trans (le_of_eq ?_)
      congr 1
      simp only [T]; push_cast; rw [pow_add]; field_simp)
  have e : ∀ i ∈ scales ε est, (4 : ℝ) ^ (j0 + i) / (2 * ((4 ^ i : ℕ) : ℝ)) = 4 ^ j0 / 2 := by
    intro i _; push_cast; rw [pow_add]; field_simp
  rw [Finset.sum_congr rfl e, sum_const, nsmul_eq_mul] at hfam
  have h4 : (0 : ℝ) < 4 ^ j0 := by positivity
  have h5 : ((scales ε est).card : ℝ) * (4 ^ j0 / 2) ≤ 16 * φ est * 4 ^ j0 + 2 := by
    have := hfam.trans hN2; simp only [T] at this; linarith
  have e2 : (1 / 2 : ℝ) ^ j0 * 4 ^ j0 = 2 ^ j0 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, ← mul_assoc, ← mul_pow]; norm_num
  have h2 : (1 : ℝ) ≤ 2 ^ j0 := one_le_pow₀ (by norm_num)
  rw [← mul_le_mul_iff_of_pos_right h4, add_mul, mul_assoc, e2]
  nlinarith

omit [∀ x, IsProbabilityMeasure (A x)] in
/-- There are at least `ε(k̃) log₄ k̃ - 1` scales. -/
theorem card_scales_ge (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) {est : ℕ} (hest : 1 ≤ est) :
    ε est * Real.logb 4 est - 1 ≤ (scales ε est).card := by
  set L := Nat.log 4 est
  set x := Real.logb 4 est
  have hest' : (1 : ℝ) ≤ est := by exact_mod_cast hest
  have hx0 : 0 ≤ x := Real.logb_nonneg (by norm_num) hest'
  have hε1 := hε est
  set a := ⌈(1 - ε est) * x⌉₊
  have ha : (a : ℝ) < (1 - ε est) * x + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) hx0)
  have hxL : x < L + 1 := by
    have h1 : est < 4 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) est
    have h2 : (est : ℝ) < (4 : ℝ) ^ ((L + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast h1
    have := (Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)).2 h2
    simpa using this
  have hsub : Icc a L ⊆ scales ε est := by
    intro i hi
    rw [mem_Icc] at hi
    simp only [scales, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    have hk : (est : ℝ) = 4 ^ x := (Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity)).symm
    calc (est : ℝ) ^ (1 - ε est) = (4 : ℝ) ^ (x * (1 - ε est)) := by
          rw [hk, ← Real.rpow_mul (by norm_num)]
      _ ≤ (4 : ℝ) ^ (i : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : ((1 - ε est) * x : ℝ) ≤ a := Nat.le_ceil _
          have : (a : ℝ) ≤ i := by exact_mod_cast hi.1
          linarith
      _ = 4 ^ i := Real.rpow_natCast _ _
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have : (L : ℝ) + 1 - a ≤ ((L + 1 - a : ℕ) : ℝ) := by
    rcases le_total a (L + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; rfl
    · have : (L : ℝ) + 1 ≤ a := by exact_mod_cast h
      have : (0 : ℝ) ≤ ((L + 1 - a : ℕ) : ℝ) := by positivity
      linarith
  have hc : ((L + 1 - a : ℕ) : ℝ) ≤ (scales ε est).card := by exact_mod_cast hcard
  nlinarith

/-- **Theorem 4.2** of [Feinerman–Korman–Lotker–Sereni], explicit form: if the agents have a
`k^ε`-approximation of `k` (`0 < ε ≤ 1`) and the algorithm is `φ(k)`-competitive with `φ`
non-decreasing, then `φ(k) ≥ ε(k) · log k / (64 · log 4)` for every `k ≥ 1`. -/
theorem theorem_4_2_explicit (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) (hA : IsCompetitiveAdvice A ε φ)
    (hφ : Monotone φ) {k : ℕ} (hk : 1 ≤ k) :
    ε k * Real.log k / (64 * Real.log 4) ≤ φ k := by
  have h1 := card_scales_le hε hA hφ hk
  have h2 := card_scales_ge hε hk
  have h3 := one_div_le_of_competitive hε hA hφ hk
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have e : ε k * Real.log k / (64 * Real.log 4) = ε k * Real.logb 4 k / 64 := by
    rw [Real.logb]; ring
  rw [e]
  rcases le_total (ε k * Real.logb 4 k) 2 with h | h
  · linarith
  · linarith

/-- **Theorem 4.2** of [Feinerman–Korman–Lotker–Sereni]: with a `k^ε`-approximation of `k`
(`0 < ε ≤ 1`), every `φ(k)`-competitive algorithm with `φ` non-decreasing has
`φ(k) = Ω(ε(k) log k)`. -/
theorem theorem_4_2 (hε : ∀ x, 0 < ε x ∧ ε x ≤ 1) (hA : IsCompetitiveAdvice A ε φ)
    (hφ : Monotone φ) : (fun k : ℕ => ε k * Real.log k) =O[atTop] φ := by
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine Asymptotics.IsBigO.of_bound (64 * Real.log 4) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h := theorem_4_2_explicit hε hA hφ hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hε k).1.le hlog),
    abs_of_pos (hA.pos hε hk)]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

end Advice

end Podc.CollaborativeSearchPlane
