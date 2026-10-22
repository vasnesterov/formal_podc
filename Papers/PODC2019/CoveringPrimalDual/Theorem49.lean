import Papers.PODC2019.CoveringPrimalDual.Main

/-!
# Theorem 4.9: the choice of `α`

Theorem 4.9 sets, for a constant `γ > 0`, `L = log Δ` and `g = f·log(f/ε)`,
`α = max(2, L/(g log L))` if `L/(g log L) ≥ L^{γ/2}` and `α = 2` otherwise, and claims
`T = O(g + L/log L + min{L, g·L^γ})`.

For `f = 1, ε = 1` we have `g = 0` and the definition divides by zero, and the bound
`O(g + …)` with `g = 0` cannot absorb the additive constant. We therefore use `F = f·z`
(`z = ⌈log₂(1/β)⌉ ≥ 1`) in place of `f·log(f/ε)`; `F = Θ(f·log(f/ε))` whenever `f/ε ≥ 2`
(`z_le`). With this choice we prove the bound with the explicit constant `C49 γ`
(`theorem_4_9`), for every `Δ ≥ 3` (the paper's assumption, so that `log log Δ > 0`).
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {I : Inst V E} {P : Params}

/-- The multiplier of Theorem 4.9 for `L = log Δ` and `F = f·z`. -/
noncomputable def alpha49 (γ L F : ℝ) : ℝ :=
  if L ^ (γ / 2) ≤ L / (F * Real.log L) then max 2 (L / (F * Real.log L)) else 2

/-- The constant of Theorem 4.9. -/
noncomputable def C49 (γ : ℝ) : ℝ := 5 + 2 / γ + (2 ^ (2 / γ) + max 1 (2 / γ)) / Real.log 2

theorem two_le_alpha49 (γ L F : ℝ) : 2 ≤ alpha49 γ L F := by
  unfold alpha49; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- Theorem 4.9 (with `F = f·z` in place of `f·log(f/ε)`): for `Δ ≥ 3`, with
`α = alpha49 γ (log Δ) (f z)`, the number of iterations is at most
`C49 γ · (f z + log Δ / log log Δ + min{log Δ, f z (log Δ)^γ})`. -/
theorem theorem_4_9 (hP : P.Valid I) (hκ : P.κ = 1) (hc : P.c₀ = 1 / 2) {γ : ℝ} (hγ : 0 < γ)
    {Δ : ℕ} (hΔ : ∀ v, I.deg v ≤ Δ) (hΔ3 : 3 ≤ Δ)
    (hα : P.α = alpha49 γ (Real.log Δ) (P.f * P.z)) :
    Terminated I P (iterBound P Δ) ∧
    (iterBound P Δ : ℝ) ≤ C49 γ * (P.f * P.z + Real.log Δ / Real.log (Real.log Δ) +
      min (Real.log Δ) (P.f * P.z * Real.log Δ ^ γ)) := by
  refine ⟨theorem_4_8 hP hΔ, ?_⟩
  set L := Real.log Δ with hLdef
  set F : ℝ := P.f * P.z with hFdef
  have hF1 : 1 ≤ F := by
    have h1 : (1 : ℝ) ≤ P.f := by exact_mod_cast hP.f_pos
    have h2 : (1 : ℝ) ≤ P.z := by exact_mod_cast hP.z_pos
    nlinarith
  have hΔ3' : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα2 : 2 ≤ P.α := hα ▸ two_le_alpha49 _ _ _
  have hT := iterBound_le hP hc hα2 (by omega : 1 ≤ Δ)
  rw [hκ, div_one] at hT
  have hlogb : Real.logb P.α Δ = L / Real.log P.α := rfl
  rw [hlogb] at hT
  -- `T ≤ L / log α + F (α + 2) + 1`
  have hLL : 0 < L / Real.log L := div_pos (by linarith) hlogL
  have hmin0 : 0 ≤ min L (F * L ^ γ) :=
    le_min (by linarith) (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
  have hγ2 : 0 < 2 / γ := by positivity
  have hpow2 : 0 < (2 : ℝ) ^ (2 / γ) := by positivity
  have hmax : 1 ≤ max 1 (2 / γ) := le_max_left _ _
  have hCge : 2 / γ + 1 ≤ C49 γ ∧ 5 ≤ C49 γ ∧ 2 ^ (2 / γ) / Real.log 2 + 5 ≤ C49 γ ∧
      max 1 (2 / γ) / Real.log 2 ≤ C49 γ := by
    unfold C49
    have h1 : 0 ≤ (2 ^ (2 / γ) + max 1 (2 / γ)) / Real.log 2 := by positivity
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · have : 2 ^ (2 / γ) / Real.log 2 ≤ (2 ^ (2 / γ) + max 1 (2 / γ)) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2.le
      linarith
    · have : max 1 (2 / γ) / Real.log 2 ≤ (2 ^ (2 / γ) + max 1 (2 / γ)) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2.le
      linarith
  obtain ⟨hC1, hC2, hC3, hC4⟩ := hCge
  have hC0 : 0 < C49 γ := by linarith
  set x := L / (F * Real.log L) with hxdef
  have hFx : F * x = L / Real.log L := by
    rw [hxdef]; field_simp
  unfold alpha49 at hα
  rw [← hxdef] at hα
  split_ifs at hα with h1
  · by_cases hx2 : 2 ≤ x
    · -- case A: `α = x ≥ L^{γ/2}`
      rw [max_eq_right hx2] at hα
      have hlogα : γ / 2 * Real.log L ≤ Real.log P.α := by
        rw [hα, ← Real.log_rpow (by linarith)]
        exact Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) h1
      have hlogα0 : 0 < Real.log P.α := lt_of_lt_of_le (by positivity) hlogα
      have hA : L / Real.log P.α ≤ 2 / γ * (L / Real.log L) := by
        rw [div_le_iff₀ hlogα0]
        calc L = 2 / γ * (L / Real.log L) * (γ / 2 * Real.log L) := by field_simp
          _ ≤ 2 / γ * (L / Real.log L) * Real.log P.α :=
            mul_le_mul_of_nonneg_left hlogα (by positivity)
      have hFα : F * P.α = L / Real.log L := by rw [hα, hFx]
      rw [mul_add, hFα] at hT
      have hT' : (iterBound P Δ : ℝ) ≤ (2 / γ + 1) * (L / Real.log L) + 3 * F := by
        linarith
      have h4 : (2 / γ + 1) * (L / Real.log L) ≤ C49 γ * (L / Real.log L) :=
        mul_le_mul_of_nonneg_right hC1 hLL.le
      have h5 : 3 * F ≤ C49 γ * F := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h6 : 0 ≤ C49 γ * min L (F * L ^ γ) := mul_nonneg hC0.le hmin0
      rw [mul_add, mul_add]
      linarith
    · -- case B: `L^{γ/2} ≤ x < 2`, so `L < 2^{2/γ}` and `α = 2`
      push Not at hx2
      rw [max_eq_left hx2.le] at hα
      have hLγ : L ^ (γ / 2) < 2 := lt_of_le_of_lt h1 hx2
      have hLb : L < 2 ^ (2 / γ) := by
        have := Real.rpow_lt_rpow (Real.rpow_nonneg (by linarith) _) hLγ hγ2
        rwa [← Real.rpow_mul (by linarith), show γ / 2 * (2 / γ) = 1 by field_simp,
          Real.rpow_one] at this
      rw [hα] at hT
      have hB : L / Real.log 2 ≤ 2 ^ (2 / γ) / Real.log 2 :=
        div_le_div_of_nonneg_right hLb.le hlog2.le
      have hB' : 2 ^ (2 / γ) / Real.log 2 ≤ 2 ^ (2 / γ) / Real.log 2 * F :=
        le_mul_of_one_le_right (by positivity) hF1
      have hT' : (iterBound P Δ : ℝ) ≤ (2 ^ (2 / γ) / Real.log 2 + 5) * F := by
        have : F * (2 + 2) + 1 ≤ 5 * F := by linarith
        have : (2 ^ (2 / γ) / Real.log 2 + 5) * F = 2 ^ (2 / γ) / Real.log 2 * F + 5 * F := by
          ring
        linarith
      have h5 : (2 ^ (2 / γ) / Real.log 2 + 5) * F ≤ C49 γ * F :=
        mul_le_mul_of_nonneg_right hC3 (by linarith)
      have h6 : 0 ≤ C49 γ * min L (F * L ^ γ) := mul_nonneg hC0.le hmin0
      have h7 : 0 ≤ C49 γ * (L / Real.log L) := mul_nonneg hC0.le hLL.le
      rw [mul_add, mul_add]
      linarith
  · -- case C: `x < L^{γ/2}`, `α = 2`, and `L ≤ (2/γ) F L^γ`
    push Not at h1
    rw [hα] at hT
    have hLeq : L = x * (F * Real.log L) := by rw [hxdef]; field_simp
    have hlogle : Real.log L ≤ L ^ (γ / 2) / (γ / 2) := Real.log_le_rpow_div (by linarith)
      (by positivity)
    have hLγ : L ≤ 2 / γ * (F * L ^ γ) := by
      have hpos : 0 < L ^ (γ / 2) := Real.rpow_pos_of_pos (by linarith) _
      calc L = x * (F * Real.log L) := hLeq
        _ ≤ L ^ (γ / 2) * (F * Real.log L) :=
            mul_le_mul_of_nonneg_right h1.le (by positivity)
        _ ≤ L ^ (γ / 2) * (F * (L ^ (γ / 2) / (γ / 2))) := by gcongr
        _ = 2 / γ * (F * (L ^ (γ / 2) * L ^ (γ / 2))) := by field_simp
        _ = 2 / γ * (F * L ^ γ) := by
            rw [← Real.rpow_add (by linarith), add_halves]
    have hLmin : L ≤ max 1 (2 / γ) * min L (F * L ^ γ) := by
      rcases min_cases L (F * L ^ γ) with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm]; exact le_mul_of_one_le_left (by linarith) hmax
      · rw [hm]
        exact hLγ.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)))
    have hC : L / Real.log 2 ≤ max 1 (2 / γ) / Real.log 2 * min L (F * L ^ γ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hLmin hlog2.le
    have hT' : (iterBound P Δ : ℝ) ≤ max 1 (2 / γ) / Real.log 2 * min L (F * L ^ γ) + 5 * F := by
      have : F * (2 + 2) + 1 ≤ 5 * F := by linarith
      linarith
    have h4 : max 1 (2 / γ) / Real.log 2 * min L (F * L ^ γ) ≤ C49 γ * min L (F * L ^ γ) :=
      mul_le_mul_of_nonneg_right hC4 hmin0
    have h5 : 5 * F ≤ C49 γ * F := mul_le_mul_of_nonneg_right hC2 (by linarith)
    have h6 : 0 ≤ C49 γ * (L / Real.log L) := mul_nonneg hC0.le hLL.le
    rw [mul_add, mul_add]
    linarith

end Podc.CoveringPrimalDual
