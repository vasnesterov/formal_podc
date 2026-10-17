import Papers.PODC2011.CoordinatedConsensusDynamic.StaticPathMain
import Cslib.Foundations.Data.Nat.Log

/-!
# Theorem 6.7, asymptotic form

With `γ = log₂ 3` and `α = 1/(2 + γ) ≈ 0.28`, choosing `β = ⌈Δ^α n^(1-α)⌉` in `theorem_6_7_clog`
gives: no node of the static line decides by time `n - 57 Δ^α n^(1-α)`, i.e. the paper's
`n - O(Δ^(1/(2+log₂3)) n^(1-1/(2+log₂3)))` (for `Δ ≥ 1`; for `Δ = 0` the bound is `n - 2`, not `n`).
The paper's exponent `log₂ e` (twice in the proof sketch) is a typo for `log₂ 3`.
-/

namespace CoordCons

namespace StaticPath

/-- `γ = log₂ 3`. -/
noncomputable def γ3 : ℝ := Real.logb 2 3

theorem two_rpow_γ3 : (2 : ℝ) ^ γ3 = 3 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

theorem γ3_pos : 0 < γ3 := Real.logb_pos (by norm_num) (by norm_num)

theorem three_pow_eq (j : ℕ) : (3 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ γ3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), two_rpow_γ3]

/-- `3^⌈log₂ q⌉ ≤ 3 q^(log₂ 3)`. -/
theorem three_pow_clog_le {q : ℕ} (hq : 1 ≤ q) : (3 : ℝ) ^ Nat.clog 2 q ≤ 3 * (q : ℝ) ^ γ3 := by
  have h : 2 ^ Nat.clog 2 q < 2 * q := Nat.pow_clog_lt_mul one_lt_two (by omega)
  rw [three_pow_eq]
  calc ((2 : ℝ) ^ Nat.clog 2 q) ^ γ3 ≤ (2 * (q : ℝ)) ^ γ3 :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast h.le) γ3_pos.le
    _ = 3 * (q : ℝ) ^ γ3 := by rw [Real.mul_rpow (by norm_num) (by positivity), two_rpow_γ3]

/-- The length of the walk of Theorem 6.7, times `Δ`, is at most `54 X` when `X ≤ β` and
`(n/X)^(1+γ) Δ = X`. -/
theorem walk_cost_le {n β Δ : ℕ} {X : ℝ} (hX : 0 < X) (hXβ : X ≤ β) (hβn : β ≤ n) (hβ : 1 ≤ β)
    (hXΔ : ((n : ℝ) / X) ^ (1 + γ3) * Δ = X) :
    ((n ⌈/⌉ β : ℕ) : ℝ) * (3 : ℝ) ^ (ellBeta n β + 1) * Δ ≤ 54 * X := by
  unfold ellBeta
  generalize hq : n ⌈/⌉ β = q
  have hq1 : 1 ≤ q := by
    rw [← hq, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]; omega
  have hqβ : q * β ≤ n + β - 1 := hq ▸ Nat.ceilDiv_mul_le _ _
  have hβR : (0 : ℝ) < β := by exact_mod_cast hβ
  have hqR : (q : ℝ) ≤ 2 * n / X := by
    have h1 : (q : ℝ) * β ≤ 2 * n := by
      have : q * β ≤ 2 * n := by omega
      exact_mod_cast this
    have h2 : (q : ℝ) ≤ 2 * n / β := by rw [le_div_iff₀ hβR]; exact h1
    exact h2.trans (div_le_div_of_nonneg_left (by positivity) hX hXβ)
  have h3 := three_pow_clog_le hq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hγ := γ3_pos
  have e1 : (q : ℝ) * (3 : ℝ) ^ (Nat.clog 2 q + 1) ≤ 9 * (q : ℝ) ^ (1 + γ3) := by
    rw [Real.rpow_add hq0, Real.rpow_one, pow_succ]
    nlinarith [Real.rpow_nonneg hq0.le γ3]
  have e2 : (q : ℝ) ^ (1 + γ3) ≤ 6 * ((n : ℝ) / X) ^ (1 + γ3) := by
    calc (q : ℝ) ^ (1 + γ3) ≤ (2 * ((n : ℝ) / X)) ^ (1 + γ3) :=
          Real.rpow_le_rpow hq0.le (by rw [mul_div_assoc] at hqR; exact hqR) (by linarith)
      _ = 6 * ((n : ℝ) / X) ^ (1 + γ3) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_add (by norm_num),
            Real.rpow_one, two_rpow_γ3]; ring
  have hΔ : (0 : ℝ) ≤ Δ := by positivity
  calc (q : ℝ) * 3 ^ (Nat.clog 2 q + 1) * Δ ≤ 9 * (6 * ((n : ℝ) / X) ^ (1 + γ3)) * Δ :=
        mul_le_mul_of_nonneg_right (e1.trans (by linarith)) hΔ
    _ = 54 * (((n : ℝ) / X) ^ (1 + γ3) * Δ) := by ring
    _ = 54 * X := by rw [hXΔ]

/-- With `X = Δ^α n^(1-α)`, `α = 1/(2+γ)`: `(n/X)^(1+γ) Δ = X`. -/
theorem balance {n Δ : ℝ} (hn : 0 < n) (hΔ : 0 < Δ) :
    (n / (Δ ^ (1 / (2 + γ3)) * n ^ (1 - 1 / (2 + γ3)))) ^ (1 + γ3) * Δ =
      Δ ^ (1 / (2 + γ3)) * n ^ (1 - 1 / (2 + γ3)) := by
  have hγ := γ3_pos
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  rw [Real.log_mul (by positivity) hΔ.ne', Real.log_rpow (by positivity), Real.log_div hn.ne'
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow hΔ,
    Real.log_rpow hn]
  field_simp
  ring

/-- **Theorem 6.7** of [KMO11] (asymptotic form, explicit constant): for `Δ ≥ 1`, no node of
the static line with any input assignment decides by any time
`t ≤ n - 57 Δ^(1/(2+log₂3)) n^(1-1/(2+log₂3))`. -/
theorem theorem_6_7_asymptotic {n Δ : ℕ} {D : Decision Bool} (hD : Consensus (KnownN n) D)
    (hC : Coordinated (KnownN n) Δ D) (hΔ : 1 ≤ Δ) (k : ℕ) (σ : ℕ → Bool) {t : ℕ}
    (ht : (t : ℝ) + 57 * ((Δ : ℝ) ^ (1 / (2 + Real.logb 2 3)) *
      (n : ℝ) ^ (1 - 1 / (2 + Real.logb 2 3))) ≤ n) :
    ∀ u ∈ (staticLine n k σ).V, D (staticLine n k σ) u t = none := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · intro u hu; simp [staticLine, exec] at hu
  have hγ := γ3_pos
  set X : ℝ := (Δ : ℝ) ^ (1 / (2 + γ3)) * (n : ℝ) ^ (1 - 1 / (2 + γ3)) with hXdef
  change (t : ℝ) + 57 * X ≤ n at ht
  have hα : 1 / (2 + γ3) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ (Δ : ℝ) ^ (1 / (2 + γ3)) :=
      Real.one_le_rpow (by exact_mod_cast hΔ) (by positivity)
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (2 + γ3)) :=
      Real.one_le_rpow (by exact_mod_cast hn0) (by linarith)
    nlinarith
  have ht0 : (0 : ℝ) ≤ t := by positivity
  set β := ⌈X⌉₊ with hβdef
  have hβX : X ≤ β := Nat.le_ceil X
  have hβlt : (β : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
  have hβ : 1 ≤ β := by
    have : (1 : ℝ) ≤ β := hX1.trans hβX
    exact_mod_cast this
  have hβn : β < n := by
    have : (β : ℝ) < n := by linarith
    exact_mod_cast this
  have hn3 : 3 ≤ n := by
    have : (3 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hcost := walk_cost_le (n := n) (β := β) (Δ := Δ) (by linarith) hβX hβn.le hβ
    (balance (by exact_mod_cast hn0) (by exact_mod_cast hΔ))
  apply theorem_6_7_clog hD hC hn3 hβ hβn k σ
  generalize n ⌈/⌉ β = q at hcost ⊢
  have : ((t + q * 3 ^ (ellBeta n β + 1) * Δ + β + 1 : ℕ) : ℝ) ≤ n := by
    push_cast
    linarith
  have := Nat.cast_le.mp this
  omega

end StaticPath

end CoordCons
