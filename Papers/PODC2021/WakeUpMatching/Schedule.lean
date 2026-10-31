import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The participation schedule of Algorithm 1

Dani, Gupta, Hayes, Pettie, *Wake up and join me! An energy-efficient algorithm for maximal
matching in radio networks*, PODC 2021 (arXiv:2104.09096), Algorithm 1.

In round `t` of Algorithm 1 every node participates with probability
`r(t) = 1 / (2 + 3 (1 - (t-1)/T) Δ)`, where `T` is the number of rounds and `Δ` the degree bound.
This file proves the elementary analytic facts about this schedule used in the analysis:

* positivity and monotonicity of `r` on `t ≤ T + 1`;
* the bounds `r(t) ≤ 1/2`, `r(1) < 1/(3Δ)` and `r(t) < 1/(2Δ)` for `t ≤ 1 + T/3`;
* `sum_rate_ge`: the lower bound
  `∑_{t=a+1}^{b} r(t) ≥ (T / (3Δ)) · log (r(b) / r(a))`,
  which replaces the paper's Riemann-sum / integral estimate. It follows from the fact that
  `1/r(t)` is affine with slope `-3Δ/T`, so each summand dominates a telescoping logarithmic
  increment (`log (1 + x) ≤ x`);
* `prod_one_sub_le_exp`: `∏ (1 - g t) ≤ exp (-∑ g t)` for `0 ≤ g t ≤ 1`.

Hypotheses throughout: `0 < T` and `1 ≤ Δ` (real numbers).
-/

namespace Podc.WakeUpMatching

open Finset

/-- The participation rate `r(t)` of round `t`. -/
noncomputable def rate (T Δ t : ℝ) : ℝ := 1 / (2 + 3 * (1 - (t - 1) / T) * Δ)

/-- The reciprocal `1 / r(t) = 2 + 3 (1 - (t-1)/T) Δ` of the participation rate; affine in `t`. -/
noncomputable def invRate (T Δ t : ℝ) : ℝ := 2 + 3 * (1 - (t - 1) / T) * Δ

variable {T Δ : ℝ}

lemma rate_eq_one_div_invRate (t : ℝ) : rate T Δ t = 1 / invRate T Δ t := rfl

/-- `1 / r(t) ≥ 2` for `t ≤ T + 1` (no lower bound on `t` is needed). -/
lemma two_le_invRate (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ T + 1) :
    2 ≤ invRate T Δ t := by
  unfold invRate
  have h1 : (t - 1) / T ≤ 1 := by rw [div_le_one hT]; linarith
  have h2 : 0 ≤ (1 - (t - 1) / T) * Δ := mul_nonneg (by linarith) (by linarith)
  linarith

lemma invRate_pos (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ T + 1) :
    0 < invRate T Δ t := by
  linarith [two_le_invRate hT hΔ ht]

/-- One step back in time increases `1 / r` by exactly `3Δ / T`. -/
lemma invRate_sub_one (hT : 0 < T) (t : ℝ) :
    invRate T Δ (t - 1) = invRate T Δ t + 3 * Δ / T := by
  unfold invRate
  field_simp
  ring

/-- `invRate s - invRate t = 3Δ (t - s) / T`. -/
lemma invRate_sub_invRate (hT : 0 < T) (s t : ℝ) :
    invRate T Δ s - invRate T Δ t = 3 * Δ * (t - s) / T := by
  unfold invRate
  field_simp
  ring

/-- The rate is positive in every round `t ≤ T + 1`. -/
theorem rate_pos (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ T + 1) : 0 < rate T Δ t := by
  rw [rate_eq_one_div_invRate]
  exact one_div_pos.mpr (invRate_pos hT hΔ ht)

/-- The rate is monotone on `t ≤ T + 1`. -/
theorem rate_mono (hT : 0 < T) (hΔ : 1 ≤ Δ) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ T + 1) :
    rate T Δ s ≤ rate T Δ t := by
  rw [rate_eq_one_div_invRate, rate_eq_one_div_invRate]
  apply one_div_le_one_div_of_le (invRate_pos hT hΔ ht)
  have := invRate_sub_invRate (Δ := Δ) hT s t
  have : 0 ≤ 3 * Δ * (t - s) / T :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hT.le
  linarith

/-- The rate is strictly monotone on `t ≤ T + 1`. -/
theorem rate_strictMono (hT : 0 < T) (hΔ : 1 ≤ Δ) {s t : ℝ} (hst : s < t) (ht : t ≤ T + 1) :
    rate T Δ s < rate T Δ t := by
  rw [rate_eq_one_div_invRate, rate_eq_one_div_invRate]
  apply one_div_lt_one_div_of_lt (invRate_pos hT hΔ ht)
  have := invRate_sub_invRate (Δ := Δ) hT s t
  have : 0 < 3 * Δ * (t - s) / T :=
    div_pos (mul_pos (by linarith) (by linarith)) hT
  linarith

/-- `r(t) ≤ 1/2` for `t ≤ T + 1`. -/
theorem rate_le_half (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ T + 1) :
    rate T Δ t ≤ 1 / 2 := by
  rw [rate_eq_one_div_invRate]
  exact one_div_le_one_div_of_le two_pos (two_le_invRate hT hΔ ht)

/-- `r(T + 1) = 1/2`. -/
theorem rate_T_add_one (hT : 0 < T) : rate T Δ (T + 1) = 1 / 2 := by
  simp [rate, hT.ne']

/-- `r(1) = 1 / (2 + 3Δ)`. -/
theorem rate_one : rate T Δ 1 = 1 / (2 + 3 * Δ) := by
  simp [rate]

/-- `r(t) ≤ r(1)` for `t ≤ 1`. -/
theorem rate_le_rate_one_of_le (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ 1) :
    rate T Δ t ≤ rate T Δ 1 :=
  rate_mono hT hΔ ht (by linarith)

/-- `r(t) < 1/(2Δ)` during the first third of the rounds, `t ≤ 1 + T/3`. -/
theorem rate_lt_of_le_third (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ 1 + T / 3) :
    rate T Δ t < 1 / (2 * Δ) := by
  rw [rate_eq_one_div_invRate]
  apply one_div_lt_one_div_of_lt (by linarith)
  unfold invRate
  have h1 : (t - 1) / T ≤ 1 / 3 := by
    rw [div_le_iff₀ hT]; linarith
  have h2 : 2 / 3 * Δ ≤ (1 - (t - 1) / T) * Δ :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- `r(1) < 1/(3Δ)`. -/
theorem rate_one_lt (hΔ : 1 ≤ Δ) : rate T Δ 1 < 1 / (3 * Δ) := by
  rw [rate_one]
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- One step of the telescoping bound:
`r(t) ≥ (T / (3Δ)) · log (r(t) / r(t-1))`, since `1/r` drops by `3Δ/T` per round and
`log (1 + x) ≤ x`. -/
lemma log_rate_div_le (hT : 0 < T) (hΔ : 1 ≤ Δ) {t : ℝ} (ht : t ≤ T + 1) :
    T / (3 * Δ) * Real.log (rate T Δ t / rate T Δ (t - 1)) ≤ rate T Δ t := by
  have hy := invRate_pos (Δ := Δ) hT hΔ ht
  have hy' := invRate_pos (Δ := Δ) hT hΔ (t := t - 1) (by linarith)
  have hratio : rate T Δ t / rate T Δ (t - 1) = invRate T Δ (t - 1) / invRate T Δ t := by
    rw [rate_eq_one_div_invRate, rate_eq_one_div_invRate]
    field_simp
  rw [hratio]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy' hy)
  have hc : 0 ≤ T / (3 * Δ) := div_nonneg hT.le (by linarith)
  calc T / (3 * Δ) * Real.log (invRate T Δ (t - 1) / invRate T Δ t)
      ≤ T / (3 * Δ) * (invRate T Δ (t - 1) / invRate T Δ t - 1) :=
        mul_le_mul_of_nonneg_left hlog hc
    _ = rate T Δ t := by
        rw [rate_eq_one_div_invRate, invRate_sub_one hT]
        have : Δ ≠ 0 := by positivity
        field_simp
        ring

/-- Telescoping lower bound on the total participation rate (replaces the paper's
Riemann-sum / integral computation): for naturals `a ≤ b ≤ T + 1`,
`∑_{t=a+1}^{b} r(t) ≥ (T / (3Δ)) · log (r(b) / r(a))`. -/
theorem sum_rate_ge (hT : 0 < T) (hΔ : 1 ≤ Δ) (a b : ℕ) (hab : a ≤ b) (hb : (b : ℝ) ≤ T + 1) :
    T / (3 * Δ) * Real.log (rate T Δ b / rate T Δ a) ≤ ∑ t ∈ Ioc a b, rate T Δ t := by
  induction b, hab using Nat.le_induction with
  | base => simp [div_self (rate_pos hT hΔ hb).ne']
  | succ n hn ih =>
    push_cast at hb
    have hn' : (n : ℝ) ≤ T + 1 := by linarith
    have ha : (a : ℝ) ≤ T + 1 := le_trans (by exact_mod_cast hn) hn'
    have pa := rate_pos (Δ := Δ) hT hΔ ha
    have pn := rate_pos (Δ := Δ) hT hΔ hn'
    have pn1 := rate_pos (Δ := Δ) hT hΔ hb
    rw [← Finset.sum_Ioc_consecutive _ hn (Nat.le_succ n), Nat.Ioc_succ_singleton,
      Finset.sum_singleton]
    have hsplit : Real.log (rate T Δ ((n : ℝ) + 1) / rate T Δ a) =
        Real.log (rate T Δ n / rate T Δ a) +
          Real.log (rate T Δ ((n : ℝ) + 1) / rate T Δ n) := by
      rw [← Real.log_mul (div_pos pn pa).ne' (div_pos pn1 pn).ne']
      congr 1
      field_simp
    have hstep := log_rate_div_le (Δ := Δ) hT hΔ hb
    simp only [add_sub_cancel_right] at hstep
    push_cast
    rw [hsplit, mul_add]
    linarith [ih hn']

/-- `∏ (1 - g t) ≤ exp (-∑ g t)` when `0 ≤ g t ≤ 1`. -/
theorem prod_one_sub_le_exp (s : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ t ∈ s, 0 ≤ g t ∧ g t ≤ 1) :
    ∏ t ∈ s, (1 - g t) ≤ Real.exp (-∑ t ∈ s, g t) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun t ht => sub_nonneg.mpr (hg t ht).2)
    (fun t _ => Real.one_sub_le_exp_neg (g t))

end Podc.WakeUpMatching
