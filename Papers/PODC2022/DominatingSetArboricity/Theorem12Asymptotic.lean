import Mathlib

/-!
# Theorem 1.2: the asymptotic arithmetic

With `γ = max(2, α^{1/(2t)})`, `2 ≤ α` and `1 ≤ t ≤ α / ln α`, the extension cost of Lemma 4.6,
`γ(γ+1)⌈log_γ(4t(α+1))⌉`, is at most `416 α / t` — the `O(α/t)` of Theorem 1.2.
-/

namespace DominatingSetArboricity

/-- `ln a ≤ 4 a^{1/4}`. -/
theorem log_le_four_rpow {a : ℝ} (ha : 0 < a) : Real.log a ≤ 4 * a ^ (1 / 4 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ha (1 / 4 : ℝ))
  rw [Real.log_rpow ha] at h
  linarith

theorem half_lt_log_two : 1 / 2 < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- The arithmetic of Theorem 1.2. -/
theorem theorem_1_2_arith {α t : ℕ} (hα : 2 ≤ α) (ht : 1 ≤ t)
    (htα : (t : ℝ) * Real.log α ≤ α) :
    let γ : ℝ := max 2 ((α : ℝ) ^ (1 / (2 * (t : ℝ))))
    γ * (γ + 1) * ⌈Real.logb γ (4 * t * (α + 1))⌉₊ ≤ 416 * (α : ℝ) / t := by
  intro γ
  set a : ℝ := (α : ℝ) with ha_def
  set T : ℝ := (t : ℝ) with hT_def
  have ha2 : (2 : ℝ) ≤ a := by rw [ha_def]; exact_mod_cast hα
  have ha : 0 < a := by linarith
  have hT1 : (1 : ℝ) ≤ T := by rw [hT_def]; exact_mod_cast ht
  have hT : 0 < T := by linarith
  have hla : 1 / 2 < Real.log a :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) ha2)
  have hTa : T ≤ 2 * a := by nlinarith
  set X : ℝ := 4 * T * (a + 1)
  have hX1 : 1 < X := by nlinarith
  -- `ln X ≤ 6 ln a`
  have hlX : Real.log X ≤ 6 * Real.log a := by
    have hX : X ≤ a ^ 6 := by
      have h16 : (16 : ℝ) ≤ a ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) ha2 4]
      calc X ≤ 4 * (2 * a) * (2 * a) := by unfold X; gcongr; linarith
        _ = 16 * a ^ 2 := by ring
        _ ≤ a ^ 4 * a ^ 2 := by gcongr
        _ = a ^ 6 := by ring
    calc Real.log X ≤ Real.log (a ^ 6) := Real.log_le_log (by linarith) hX
      _ = 6 * Real.log a := by rw [Real.log_pow]; norm_num
  have hlXpos : 0 < Real.log X := Real.log_pos hX1
  have haT : Real.log a ≤ a / T := by rw [le_div_iff₀ hT]; linarith
  have hγ2 : 2 ≤ γ := le_max_left _ _
  rcases le_or_gt ((α : ℝ) ^ (1 / (2 * (t : ℝ)))) 2 with hcase | hcase
  · -- case `γ = 2`
    have hγ : γ = 2 := max_eq_left hcase
    rw [hγ]
    have hN : (⌈Real.logb 2 X⌉₊ : ℝ) ≤ 12 * Real.log a + 1 := by
      have h1 : Real.logb 2 X ≤ 12 * Real.log a := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [half_lt_log_two]
      have := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hX1.le)
      linarith
    have h6 : (1 : ℝ) ≤ 2 * (a / T) := by linarith
    calc (2 : ℝ) * (2 + 1) * ⌈Real.logb 2 X⌉₊ ≤ 6 * (12 * Real.log a + 1) := by nlinarith
      _ ≤ 6 * (12 * (a / T) + 2 * (a / T)) := by nlinarith
      _ = 84 * a / T := by ring
      _ ≤ 416 * a / T := by gcongr; norm_num
  · -- case `γ = α^{1/(2t)} > 2`
    have hγ : γ = a ^ (1 / (2 * T)) := max_eq_right hcase.le
    have hlγ : Real.log γ = Real.log a / (2 * T) := by
      rw [hγ, Real.log_rpow ha]; ring
    have hlγpos : Real.log 2 < Real.log γ := by
      rw [hγ]; exact Real.log_lt_log (by norm_num) hcase
    -- `T < ln a`
    have hTla : T < Real.log a := by
      have : Real.log 2 < Real.log a / (2 * T) := hlγ ▸ hlγpos
      rw [lt_div_iff₀ (by linarith)] at this
      nlinarith [half_lt_log_two]
    -- number of phases
    have hN : (⌈Real.logb γ X⌉₊ : ℝ) ≤ 13 * T := by
      have h1 : Real.logb γ X ≤ 12 * T := by
        rw [Real.logb, hlγ, div_le_iff₀ (by have := hla; positivity)]
        rw [show 12 * T * (Real.log a / (2 * T)) = 6 * Real.log a by field_simp; ring]
        exact hlX
      have := Nat.ceil_lt_add_one (Real.logb_nonneg (by linarith : (1 : ℝ) < γ) hX1.le)
      linarith
    have hγsq : γ * (γ + 1) ≤ 2 * a ^ (1 / T) := by
      have : γ * γ = a ^ (1 / T) := by
        rw [hγ, ← Real.rpow_add ha]; congr 1; field_simp; ring
      nlinarith
    -- `T² a^{1/T} ≤ 16 a`
    have hkey : T ^ 2 * a ^ (1 / T) ≤ 16 * a := by
      rcases eq_or_lt_of_le hT1 with h1 | h1
      · rw [← h1]; simp; linarith
      · have hT2 : (2 : ℝ) ≤ T := by
          have : (2 : ℕ) ≤ t := by
            by_contra h; push Not at h
            have : t = 1 := by omega
            rw [show T = 1 by simp [T, this]] at h1; linarith
          rw [hT_def]; exact_mod_cast this
        have hr : a ^ (1 / T) ≤ a ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by rw [div_le_div_iff₀ hT (by norm_num)]; linarith)
        have hl4 := log_le_four_rpow ha
        have hq : (a ^ (1 / 4 : ℝ)) ^ 2 = a ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
        have hs : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
        have hT2' : T ^ 2 ≤ 16 * a ^ (1 / 2 : ℝ) := by
          have : T ^ 2 ≤ (4 * a ^ (1 / 4 : ℝ)) ^ 2 := by
            gcongr; linarith
          nlinarith
        have hpos : 0 ≤ a ^ (1 / T) := (Real.rpow_pos_of_pos ha _).le
        calc T ^ 2 * a ^ (1 / T) ≤ 16 * a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by gcongr
          _ = 16 * a := by rw [mul_assoc, ← sq, hs]
    have hpos : 0 ≤ a ^ (1 / T) := (Real.rpow_pos_of_pos ha _).le
    calc γ * (γ + 1) * ⌈Real.logb γ X⌉₊ ≤ 2 * a ^ (1 / T) * (13 * T) := by
          gcongr
      _ = 26 * (T ^ 2 * a ^ (1 / T)) / T := by field_simp; norm_num
      _ ≤ 26 * (16 * a) / T := by gcongr
      _ = 416 * a / T := by ring

/-- The round arithmetic of Theorem 1.2: Lemma 4.6 with `γ = max(2, α^{1/(2t)})` and
`λ = 1/(4t(α+1))` runs `⌈log_γ(4t(α+1))⌉` phases of `⌈log_γ(Δ+1)⌉ + 1` iterations, i.e.
`≤ 50 t (ln(Δ+1) + 1) = O(t log Δ)` iterations. -/
theorem theorem_1_2_rounds_arith {α t Δ : ℕ} (hα : 2 ≤ α) (ht : 1 ≤ t)
    (htα : (t : ℝ) * Real.log α ≤ α) :
    let γ : ℝ := max 2 ((α : ℝ) ^ (1 / (2 * (t : ℝ))))
    (⌈Real.logb γ (4 * t * (α + 1))⌉₊ : ℝ) * (⌈Real.logb γ (Δ + 1)⌉₊ + 1) ≤
      50 * t * (Real.log (Δ + 1) + 1) := by
  intro γ
  set a : ℝ := (α : ℝ) with ha_def
  set T : ℝ := (t : ℝ) with hT_def
  have ha2 : (2 : ℝ) ≤ a := by rw [ha_def]; exact_mod_cast hα
  have ha : 0 < a := by linarith
  have hT1 : (1 : ℝ) ≤ T := by rw [hT_def]; exact_mod_cast ht
  have hT : 0 < T := by linarith
  have hla : 1 / 2 < Real.log a :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) ha2)
  have hTa : T ≤ 2 * a := by nlinarith
  set X : ℝ := 4 * T * (a + 1)
  have hX1 : 1 < X := by nlinarith
  have hlX : Real.log X ≤ 6 * Real.log a := by
    have hX : X ≤ a ^ 6 := by
      have h16 : (16 : ℝ) ≤ a ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) ha2 4]
      calc X ≤ 4 * (2 * a) * (2 * a) := by unfold X; gcongr; linarith
        _ = 16 * a ^ 2 := by ring
        _ ≤ a ^ 4 * a ^ 2 := by gcongr
        _ = a ^ 6 := by ring
    calc Real.log X ≤ Real.log (a ^ 6) := Real.log_le_log (by linarith) hX
      _ = 6 * Real.log a := by rw [Real.log_pow]; norm_num
  set L : ℝ := Real.log ((Δ : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _; linarith)
  have hγ2 : 2 ≤ γ := le_max_left _ _
  have hlγ0 : 1 / 2 < Real.log γ :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) hγ2)
  have hR0 : 0 ≤ Real.logb γ ((Δ : ℝ) + 1) :=
    Real.logb_nonneg (by linarith) (by have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _; linarith)
  have hRc := Nat.ceil_lt_add_one hR0
  have hNc := Nat.ceil_lt_add_one (Real.logb_nonneg (by linarith : (1 : ℝ) < γ) hX1.le)
  have hNpos : (0 : ℝ) ≤ ⌈Real.logb γ X⌉₊ := Nat.cast_nonneg _
  rcases le_or_gt ((α : ℝ) ^ (1 / (2 * (t : ℝ)))) 2 with hcase | hcase
  · have hγ : γ = 2 := max_eq_left hcase
    -- `ln a ≤ 2T`
    have hlaT : Real.log a ≤ 2 * T := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos ha _) hcase
      rw [Real.log_rpow ha] at h
      have h2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)] at h
      nlinarith
    have hN : Real.logb γ X ≤ 24 * T := by
      rw [hγ, Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith [half_lt_log_two]
    have hR : Real.logb γ ((Δ : ℝ) + 1) ≤ 2 * L := by
      rw [hγ, Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith [half_lt_log_two]
    calc (⌈Real.logb γ X⌉₊ : ℝ) * (⌈Real.logb γ ((Δ : ℝ) + 1)⌉₊ + 1)
        ≤ (24 * T + 1) * (2 * L + 2) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ ≤ 50 * T * (L + 1) := by nlinarith
  · have hγ : γ = a ^ (1 / (2 * T)) := max_eq_right hcase.le
    have hlγ : Real.log γ = Real.log a / (2 * T) := by
      rw [hγ, Real.log_rpow ha]; ring
    have hlγpos : Real.log 2 < Real.log γ := by
      rw [hγ]; exact Real.log_lt_log (by norm_num) hcase
    have hN : Real.logb γ X ≤ 12 * T := by
      rw [Real.logb, hlγ, div_le_iff₀ (by have := hla; positivity)]
      rw [show 12 * T * (Real.log a / (2 * T)) = 6 * Real.log a by field_simp; ring]
      exact hlX
    have hR : Real.logb γ ((Δ : ℝ) + 1) ≤ 2 * L := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith [half_lt_log_two]
    calc (⌈Real.logb γ X⌉₊ : ℝ) * (⌈Real.logb γ ((Δ : ℝ) + 1)⌉₊ + 1)
        ≤ (12 * T + 1) * (2 * L + 2) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ ≤ 50 * T * (L + 1) := by nlinarith

end DominatingSetArboricity
