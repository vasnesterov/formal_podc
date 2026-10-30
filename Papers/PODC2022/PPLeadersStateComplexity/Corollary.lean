import Papers.PODC2022.PPLeadersStateComplexity.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Corollary 4.4 of Leroux

For every `h < 1/2` and `m ≥ 1`, the number of states of a protocol with interaction-width
`≤ m` and at most `m` leaders stably computing `(i ≥ n)` is `Ω((log log n)^h)`.

The proof is the paper's: Theorem 4.3 gives `n ≤ (10m)^(d^((d+2)^2))` with `d = |P|`, hence
`log log n ≤ (d+2)^2 log d + log log (10m)`, and `log d ≤ (d+2)^ε / ε` with `1/(2+ε) = h`.
The asymptotic `Ω` is made explicit: there are `c > 0` and `N` such that
`c (log log n)^h ≤ |P|` for all `n ≥ N` (`(log log n)^h` is a real power, `Real.rpow`).
-/

namespace Podc.PPLeadersStateComplexity

open Real

/-- The numeric core of Corollary 4.4: if `n ≤ (10m)^(d^((d+2)^2))` with `d ≥ 1`, then
`d ≥ c (log log n)^h` for `n` large enough. -/
theorem corollary_4_4_numeric {h : ℝ} (hh : h < 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ d : ℕ, 1 ≤ d →
      n ≤ (10 * m) ^ (d ^ (d + 2) ^ 2) → c * (log (log n)) ^ h ≤ d := by
  -- `L₀ = log log (10m)`, `A = max(L₀, 0)`, and `N` with `log log N ≥ max(2A, 1)`
  set L₀ := log (log ((10 * m : ℕ) : ℝ))
  set B := max (2 * max L₀ 0) 1
  have hB1 : 1 ≤ B := le_max_right _ _
  refine (fun H => ?_) (fun n (hn : ⌈exp (exp B)⌉₊ ≤ n) =>
    (show B ≤ log (log n) ∧ 0 < log n from ?_))
  rotate_left
  · have h1 : exp (exp B) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : exp B ≤ log n := by
      rw [← log_exp (exp B)]; exact log_le_log (exp_pos _) h1
    have h3 : 0 < log n := (exp_pos _).trans_le h2
    exact ⟨by rw [← log_exp B]; exact log_le_log (exp_pos _) h2, h3⟩
  have hN1 : 1 ≤ ⌈exp (exp B)⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact exp_pos _)
  rcases le_or_gt h 0 with hh0 | hh0
  · -- `h ≤ 0`: `(log log n)^h ≤ 1 ≤ d`
    refine ⟨1, one_pos, _, hN1, fun n hn d hd _ => ?_⟩
    obtain ⟨hx, -⟩ := H n hn
    rw [one_mul]
    exact (rpow_le_one_of_one_le_of_nonpos (hB1.trans hx) hh0).trans (by exact_mod_cast hd)
  -- `0 < h < 1/2`: `ε = 1/h − 2 > 0`
  set ε := h⁻¹ - 2 with hε
  have hε0 : 0 < ε := by
    have : 2 < h⁻¹ := by
      rw [lt_inv_comm₀ two_pos hh0]; linarith
    linarith
  refine ⟨(ε / 2) ^ h / 3, by positivity, _, hN1, fun n hn d hd hnd => ?_⟩
  obtain ⟨hx, hlogn⟩ := H n hn
  set x := log (log n)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h10 : (1 : ℝ) < ((10 * m : ℕ) : ℝ) := by
    have : 10 ≤ 10 * m := by omega
    exact_mod_cast (show 1 < 10 * m by omega)
  -- `log n ≤ d^K · log (10m)`
  have hn0 : (0 : ℝ) < n := by
    have : 1 ≤ n := hN1.trans hn
    exact_mod_cast this
  have hlog : log n ≤ ((d ^ (d + 2) ^ 2 : ℕ) : ℝ) * log ((10 * m : ℕ) : ℝ) := by
    rw [← log_pow]
    exact log_le_log hn0 (by exact_mod_cast hnd)
  have hlog10 : 0 < log ((10 * m : ℕ) : ℝ) := log_pos h10
  have hdK : (0 : ℝ) < ((d ^ (d + 2) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (by omega)
  -- `log log n ≤ (d+2)^2 log d + L₀`
  have hx1 : x ≤ ((d + 2) ^ 2 : ℕ) * log d + L₀ := by
    have := log_le_log hlogn hlog
    rw [log_mul hdK.ne' hlog10.ne', Nat.cast_pow, log_pow] at this
    exact this
  -- `log d ≤ (d+2)^ε / ε`
  have hd2 : (0 : ℝ) < d + 2 := by positivity
  have hlogd : log d ≤ ((d : ℝ) + 2) ^ ε / ε :=
    (log_le_log (by linarith) (by linarith)).trans (log_le_rpow_div hd2.le hε0)
  have hK : (((d + 2) ^ 2 : ℕ) : ℝ) * log d ≤ ((d : ℝ) + 2) ^ (2 + ε) / ε := by
    rw [rpow_add hd2, rpow_two, mul_div_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_left hlogd (by positivity)
  have h3d : ((d : ℝ) + 2) ^ (2 + ε) ≤ (3 * d) ^ (2 + ε) :=
    rpow_le_rpow hd2.le (by linarith) (by linarith)
  have hA : L₀ ≤ x / 2 := by
    have := le_max_left (2 * max L₀ 0) 1
    have := le_max_left L₀ 0
    linarith
  -- `ε x / 2 ≤ (3d)^(1/h)`
  have hmain : ε / 2 * x ≤ (3 * d) ^ h⁻¹ := by
    have e : 2 + ε = h⁻¹ := by rw [hε]; ring
    rw [← e]
    have := (div_le_div_iff_of_pos_right hε0).2 (le_refl ε)
    have h4 : x / 2 ≤ ((d : ℝ) + 2) ^ (2 + ε) / ε := by linarith
    rw [le_div_iff₀ hε0] at h4
    nlinarith
  have hx0 : 0 ≤ x := by linarith
  have := rpow_le_rpow (by positivity) hmain hh0.le
  rw [mul_rpow (by positivity) hx0, rpow_inv_rpow (by positivity) hh0.ne'] at this
  linarith

/-- **Corollary 4.4.** Let `h < 1/2` and `m ≥ 1`. The number of states of a protocol stably
computing the `(i ≥ n)` predicate with an interaction-width bounded by `m` and a number of
leaders bounded by `m` is at least `Ω((log log n)^h)`: there are `c > 0` and `N` such that
`c (log log n)^h ≤ |P|` for every `n ≥ N` and every such protocol. -/
theorem corollary_4_4 {h : ℝ} (hh : h < 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ (P : Type) [Fintype P] [DecidableEq P] (Pr : Protocol P)
      (i : P), HasWidthLE Pr.R m → Pr.numLeaders ≤ m → Pr.StablyComputesGe i n →
      c * (log (log n)) ^ h ≤ Fintype.card P := by
  obtain ⟨c, hc, N, hN1, H⟩ := corollary_4_4_numeric hh hm
  refine ⟨c, hc, N, fun n hn P _ _ Pr i hw hL hst => H n hn _ (Fintype.card_pos_iff.2 ⟨i⟩) ?_⟩
  refine (theorem_4_3 Pr hw hst).trans (Nat.pow_le_pow_left ?_ _)
  omega

end Podc.PPLeadersStateComplexity
