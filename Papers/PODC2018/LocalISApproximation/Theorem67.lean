import Papers.PODC2018.LocalISApproximation.Weighted
import Papers.PODC2018.LocalISApproximation.Lemma2

/-!
# Theorems 6 and 7: the performance of `Max` on weighted graphs

* `theorem6`: for `Δ ≥ 1`, every weighted graph with degrees `≤ Δ` and every independent set `I`,
  `E[w(Max)] ≥ w(I) · g_Δ(x)` for some `x ∈ [0,1]`; and on `K_{Δ,Δ}` with weights `1`, `β`
  equality `E[w(Max)] = w(opt) · g_Δ(β)` holds. Together: `1/ρ(Δ) = min_{0≤x≤1} g_Δ(x)`.
* `theorem7`: `ρ(Δ)/(Δ+1) → 2^{2/3}/3 ≈ 0.529` as `Δ → ∞`, where `ρ(Δ) = 1/min_{[0,1]} g_Δ`.
* `rho_two_gt`: for `Δ = 2`, `ρ(2) > 1.68`, so the text's "`ρ ∼ 1.657`" is a slip (it is
  `≈ 1.686 = 1/0.593 ≈ 0.562 (Δ+1)`, consistent with the rest of that sentence).
-/

open Finset SimpleGraph MeasureTheory Filter Topology

namespace Podc.LocalISApproximation

section Thm6

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {w : V → ℝ}

/-- `E[w(Max)] = ∑_v w(v)²/w(N[v])` (Lemma 2 + linearity of expectation). -/
theorem expected_weight_max_eq (hw : ∀ v, 0 < w v) :
    ∫ x, (∑ v ∈ maxSet G w x, w v) ∂unifCube = maxValue G w :=
  expected_weight_max hw

/-- **Theorem 6.** Performance of `Max` (every node draws `x_v ∈ [0,1]` uniformly, joins iff
`x_v^{1/w_v}` beats all neighbours).
(1) For `Δ ≥ 1`, positive weights, all degrees `≤ Δ`, and every independent set `I` (in particular
an optimal one) there is `x ∈ [0,1]` with `w(I) · g_Δ(x) ≤ E[w(Max)]`.
(2) This is tight: for every `β ∈ (0,1]`, on `K_{Δ,Δ}` with weights `1` and `β`, the optimum is
`Δ` and `E[w(Max)] = Δ · g_Δ(β)`. -/
theorem theorem6 {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    ((∀ v, 0 < w v) → (∀ v, G.degree v ≤ Δ) → ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      ∃ x ∈ Set.Icc (0 : ℝ) 1,
        (∑ v ∈ I, w v) * gFun Δ x ≤ ∫ x, (∑ v ∈ maxSet G w x, w v) ∂unifCube) ∧
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      let K := completeBipartiteGraph (Fin Δ) (Fin Δ)
      let w' : Fin Δ ⊕ Fin Δ → ℝ := Sum.elim (fun _ => 1) (fun _ => β)
      (∀ I : Finset (Fin Δ ⊕ Fin Δ), K.IsIndepSet (I : Set _) → ∑ v ∈ I, w' v ≤ Δ) ∧
      (∃ I : Finset (Fin Δ ⊕ Fin Δ), K.IsIndepSet (I : Set _) ∧ ∑ v ∈ I, w' v = Δ) ∧
      ∫ x, (∑ v ∈ maxSet K w' x, w' v) ∂unifCube = Δ * gFun Δ β) := by
  refine ⟨fun hw hdeg I hI => ?_, fun β hβ0 hβ1 => ?_⟩
  · rw [expected_weight_max_eq hw]; exact theorem6_upper hw hΔ hdeg hI
  · intro K w'
    obtain ⟨h1, h2, h3⟩ := theorem6_tight (Δ := Δ) hβ0 hβ1
    refine ⟨h1, h2, ?_⟩
    have hw' : ∀ v, 0 < w' v := by rintro (a | b) <;> simp [w', hβ0]
    rw [expected_weight_max_eq hw']
    exact h3

end Thm6

/-! ### Theorem 7 -/

theorem gFun_nonneg {Δ : ℕ} {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gFun Δ x := by
  unfold gFun; positivity

/-- `1/ρ(Δ) = min_{0 ≤ x ≤ 1} g_Δ(x)` (as an infimum). -/
noncomputable def rhoInv (Δ : ℕ) : ℝ := sInf (gFun Δ '' Set.Icc 0 1)

/-- The performance ratio `ρ(Δ)` of `Max` given by Theorem 6. -/
noncomputable def rho (Δ : ℕ) : ℝ := 1 / rhoInv Δ

/-- `x₀ = 2^{-1/3}`, the minimizer of `x² + 1/x`. -/
noncomputable def x0 : ℝ := (2 : ℝ) ^ (-(1 / 3 : ℝ))

theorem x0_pos : 0 < x0 := by unfold x0; positivity

theorem x0_cube : x0 ^ 3 = 1 / 2 := by
  unfold x0
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg_one]

theorem x0_le_one : x0 ≤ 1 := by
  unfold x0
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-- `y² + 1/y ≥ 3x₀²` for `y > 0` (AM–GM): `y³ - 3x₀²y + 2x₀³ = (y-x₀)²(y+2x₀)`. -/
theorem amgm (y : ℝ) (hy : 0 < y) : 3 * x0 ^ 2 ≤ y ^ 2 + 1 / y := by
  have h := x0_cube
  have hx := x0_pos
  rw [← sub_nonneg]
  have : y ^ 2 + 1 / y - 3 * x0 ^ 2 = (y - x0) ^ 2 * (y + 2 * x0) / y := by
    field_simp
    linear_combination (-2) * h
  rw [this]; positivity

theorem rhoInv_bounds {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    3 * x0 ^ 2 - 4 / (Δ + 1) ≤ (Δ + 1) * rhoInv Δ ∧
      (Δ + 1) * rhoInv Δ ≤ 3 * x0 ^ 2 * (1 + 1 / Δ) := by
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hne : (gFun Δ '' Set.Icc 0 1).Nonempty := ⟨_, Set.mem_image_of_mem _ ⟨le_refl 0, zero_le_one⟩⟩
  have hbdd : BddBelow (gFun Δ '' Set.Icc 0 1) :=
    ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact gFun_nonneg hx.1⟩
  have hx := x0_pos
  have hc := x0_cube
  constructor
  · -- lower bound, uniformly in `x ∈ [0,1]`
    rw [← div_le_iff₀' (by positivity : (0 : ℝ) < Δ + 1)]
    refine le_csInf hne ?_
    rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩
    rw [div_le_iff₀' (by positivity)]
    set ε : ℝ := 1 / (Δ + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; linarith
    have t1 : x ^ 2 ≤ (Δ + 1) * (x ^ 2 / (Δ + x)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg x]
    have t2 : 1 / (x + ε) ≤ (Δ + 1) * (1 / (x * Δ + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), hε]
      field_simp; nlinarith
    have t3 := amgm (x + ε) (by positivity)
    have t4 : (x + ε) ^ 2 - 2 * ε * (x + ε) ≤ x ^ 2 := by nlinarith [sq_nonneg ε]
    have t5 : 4 / ((Δ : ℝ) + 1) = 4 * ε := by rw [hε]; ring
    unfold gFun
    rw [mul_add, t5]
    nlinarith
  · -- upper bound at `x₀`
    have hmem : gFun Δ x0 ∈ gFun Δ '' Set.Icc 0 1 := Set.mem_image_of_mem _ ⟨hx.le, x0_le_one⟩
    have h1 := csInf_le hbdd hmem
    unfold rhoInv
    refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
    unfold gFun
    have hΔ0 : (0 : ℝ) < Δ := by linarith
    have u1 : (Δ + 1) * (x0 ^ 2 / (Δ + x0)) ≤ x0 ^ 2 * (1 + 1 / Δ) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg x0]
    have u2 : (Δ + 1) * (1 / (x0 * Δ + 1)) ≤ 1 / x0 * (1 + 1 / Δ) := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    have u3 : 1 / x0 = 2 * x0 ^ 2 := by
      field_simp; nlinarith
    rw [mul_add]
    rw [u3] at u2
    linarith

/-- **Theorem 7.** The asymptotic performance ratio of `Max` is `2^{2/3}(Δ+1)/3 ≈ 0.529(Δ+1)`:
`ρ(Δ)/(Δ+1) → 2^{2/3}/3` as `Δ → ∞`. -/
theorem theorem7 : Tendsto (fun Δ : ℕ => rho Δ / (Δ + 1)) atTop (𝓝 ((2 : ℝ) ^ (2 / 3 : ℝ) / 3)) := by
  have hx := x0_pos
  -- `(Δ+1) · ρ⁻¹(Δ) → 3x₀²` by squeezing
  have hlim : Tendsto (fun Δ : ℕ => ((Δ : ℝ) + 1) * rhoInv Δ) atTop (𝓝 (3 * x0 ^ 2)) := by
    have hlo : Tendsto (fun Δ : ℕ => 3 * x0 ^ 2 - 4 / ((Δ : ℝ) + 1)) atTop (𝓝 (3 * x0 ^ 2)) := by
      have : Tendsto (fun Δ : ℕ => 4 / ((Δ : ℝ) + 1)) atTop (𝓝 0) := by
        have h4 : Tendsto (fun Δ : ℕ => (4 : ℝ) * (1 / ((Δ : ℝ) + 1))) atTop (𝓝 ((4 : ℝ) * 0)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 4
        simpa [div_eq_mul_inv] using h4
      simpa using this.const_sub (3 * x0 ^ 2)
    have hhi : Tendsto (fun Δ : ℕ => 3 * x0 ^ 2 * (1 + 1 / (Δ : ℝ))) atTop (𝓝 (3 * x0 ^ 2)) := by
      have : Tendsto (fun Δ : ℕ => 1 / (Δ : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
      simpa using (this.const_add 1).const_mul (3 * x0 ^ 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with Δ hΔ using (rhoInv_bounds hΔ).1
    · filter_upwards [eventually_ge_atTop 1] with Δ hΔ using (rhoInv_bounds hΔ).2
  have hne : (3 * x0 ^ 2) ≠ 0 := by positivity
  have hinv := hlim.inv₀ hne
  have heq : (3 * x0 ^ 2)⁻¹ = (2 : ℝ) ^ (2 / 3 : ℝ) / 3 := by
    unfold x0
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3) by norm_num, Real.rpow_neg (by norm_num)]
    field_simp
  rw [← heq]
  refine hinv.congr' ?_
  filter_upwards with Δ
  unfold rho
  rw [mul_inv, one_div, div_eq_mul_inv, mul_comm]

/-- For `Δ = 2`: `ρ(2) > 1.68`, so the paper's "`ρ ∼ 1.657`" is a slip for `≈ 1.686`. -/
theorem rho_two_gt : 1.68 < rho 2 := by
  have hbdd : BddBelow (gFun 2 '' Set.Icc 0 1) :=
    ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact gFun_nonneg hx.1⟩
  have h := csInf_le hbdd (Set.mem_image_of_mem (gFun 2) (⟨by norm_num, by norm_num⟩ :
    (0.6 : ℝ) ∈ Set.Icc 0 1))
  have hval : gFun 2 0.6 < 1 / 1.68 := by unfold gFun; norm_num
  have hlow : 1 / 2 ≤ rhoInv 2 := by
    refine le_csInf ⟨_, Set.mem_image_of_mem _ ⟨le_refl (0 : ℝ), zero_le_one⟩⟩ ?_
    rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩
    unfold gFun
    push_cast
    have : 1 / 2 ≤ x ^ 2 / (2 + x) + 1 / (x * 2 + 1) := by
      rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (x - 1 / 2), mul_nonneg hx0 (sq_nonneg (x - 1 / 2))]
    exact this
  have hpos : 0 < rhoInv 2 := lt_of_lt_of_le (by norm_num) hlow
  unfold rho
  rw [lt_div_iff₀ hpos]
  have : rhoInv 2 < 1 / 1.68 := lt_of_le_of_lt h hval
  nlinarith

end Podc.LocalISApproximation
