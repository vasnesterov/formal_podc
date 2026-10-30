import Papers.PODC2021.ContentionPredictions.Randomized
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The `Θ`-upper bounds of Theorems 3.6 and 3.7 fail when the advice is long

Theorem 3.6 claims that for `b(n) < log₂ n` the optimal expected time without collision detection
is `t(n) = Θ(log n / 2^{b(n)})`, and Theorem 3.7 that for `b(n) < log₂ log₂ n` the optimal expected
time with collision detection is `t(n) = Θ(log log n − b(n))`. But every algorithm needs at least
one round (`one_le_expTime`, `one_le_expTimeCD`), while `log n / 2^{b(n)}` (resp.
`log log n − b(n)`) tends to `0` along admissible choices of `b(n)`:

* `b(n) = ⌊log₂ n⌋ − 1` (so `b(n) < log₂ n`): at `n = 2^j`, `log₂ n / 2^{b(n)} = j / 2^{j-1} → 0`.
* `b(n) = ⌈log₂ log₂ n⌉ − 1` (so `b(n) < log₂ log₂ n`): at `n = 2^{2^j + 1}`,
  `log₂ log₂ n − b(n) = log₂ (1 + 2^{-j}) → 0`.

So the claimed `O(·)` upper bounds are false; the correct statements are
`Θ(1 + log n / 2^{b(n)})` and `Θ(1 + log log n − b(n))` (the paper itself notes the `O(1)` regime
`b(n) ≥ log log n` after Theorem 3.7). The lower bounds are unaffected.
-/

namespace Podc.ContentionPredictions

open MeasureTheory Finset
open scoped ENNReal

/-- Optimal worst-case expected time of randomized contention resolution without collision
detection with `b` bits of advice (`t(n)` of Theorem 3.6). -/
noncomputable def optTimeNoCD (n b : ℕ) : ℝ≥0∞ :=
  ⨅ (D : Bits b → Fin n → Measure (ℕ → Bool)) (_ : ∀ a v, IsProbabilityMeasure (D a v))
    (f : Finset (Fin n) → Bits b), ⨆ (P : Finset (Fin n)) (_ : P.Nonempty), expTime (D (f P)) P

/-- Optimal worst-case expected time of randomized contention resolution with collision detection
with `b` bits of advice (`t(n)` of Theorem 3.7). -/
noncomputable def optTimeCD (n b : ℕ) : ℝ≥0∞ :=
  ⨅ (D : Bits b → Fin n → Measure (List Bool → Bool)) (_ : ∀ a v, IsProbabilityMeasure (D a v))
    (f : Finset (Fin n) → Bits b), ⨆ (P : Finset (Fin n)) (_ : P.Nonempty), expTimeCD (D (f P)) P

theorem one_le_optTimeNoCD {n : ℕ} (hn : 0 < n) (b : ℕ) : 1 ≤ optTimeNoCD n b := by
  unfold optTimeNoCD
  refine le_iInf fun D => le_iInf fun hD => le_iInf fun f => ?_
  have hP : ({⟨0, hn⟩} : Finset (Fin n)).Nonempty := singleton_nonempty _
  refine le_trans ?_ (le_iSup₂ (κ := fun P : Finset (Fin n) => P.Nonempty)
    (f := fun P _ => expTime (D (f P)) P) _ hP)
  have := hD (f {⟨0, hn⟩})
  exact one_le_expTime _ _

theorem one_le_optTimeCD {n : ℕ} (hn : 0 < n) (b : ℕ) : 1 ≤ optTimeCD n b := by
  unfold optTimeCD
  refine le_iInf fun D => le_iInf fun hD => le_iInf fun f => ?_
  have hP : ({⟨0, hn⟩} : Finset (Fin n)).Nonempty := singleton_nonempty _
  refine le_trans ?_ (le_iSup₂ (κ := fun P : Finset (Fin n) => P.Nonempty)
    (f := fun P _ => expTimeCD (D (f P)) P) _ hP)
  have := hD (f {⟨0, hn⟩})
  exact one_le_expTimeCD _ _

/-- Non-vacuity of the hypothesis `NewportBound n c` used for the lower bounds of Theorems 3.6 and
3.7: it holds whenever `c log₂ n ≤ 1` (every algorithm needs one round). For a constant `c > 0` and
all large `n` it is the theorem of [18], which we do not formalize. -/
theorem newportBound_of_le_one {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : c * Real.logb 2 n ≤ 1) :
    NewportBound n c := fun μ _ =>
  ⟨{⟨0, hn⟩}, singleton_nonempty _,
    (ENNReal.ofReal_le_one.2 hc).trans (one_le_expTime μ _)⟩

/-- The advice length `b(n) = ⌊log₂ n⌋ - 1` satisfies the hypothesis `b(n) < log₂ n` of
Theorem 3.6 (for `n ≥ 2`). -/
theorem bLong_lt {n : ℕ} (hn : 2 ≤ n) : ((Nat.log 2 n - 1 : ℕ) : ℝ) < Real.logb 2 n := by
  have h1 : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < n)),
      Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hpos : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  push_cast [Nat.cast_sub hpos]
  linarith

/-- **The upper bound of Theorem 3.6 is false** for long advice: with `b(n) = ⌊log₂ n⌋ - 1 < log₂ n`
bits, the optimal expected time `t(n)` (always `≥ 1`) is not `O(log n / 2^{b(n)})`. -/
theorem theorem_3_6_upper_false :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      optTimeNoCD n (Nat.log 2 n - 1) ≤
        ENNReal.ofReal (C * Real.logb 2 n / 2 ^ (Nat.log 2 n - 1)) := by
  rintro ⟨C, N, h⟩
  -- choose `j ≥ max N 1` with `C j < 2^(j-1)`
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ j : ℕ in Filter.atTop, ((j : ℝ) ^ 1 / 2 ^ j) < 1 / (2 * (|C| + 1)) :=
    hlim (gt_mem_nhds (by positivity))
  obtain ⟨j, hj, hjN⟩ := (hev.and (Filter.eventually_ge_atTop (N + 1))).exists
  have hjpos : 1 ≤ j := by omega
  have hNj : N ≤ 2 ^ j := le_trans (by omega) (Nat.lt_two_pow_self).le
  have key := h (2 ^ j) hNj
  rw [Nat.log_pow (by norm_num)] at key
  have h1 := (one_le_optTimeNoCD (by positivity) (j - 1)).trans key
  rw [ENNReal.one_le_ofReal] at h1
  push_cast at h1
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h1
  have h2j : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℝ) < 2 ^ (j - 1) := by positivity
  rw [le_div_iff₀ hpos] at h1
  rw [pow_one, div_lt_div_iff₀ (by positivity) (by positivity), h2j] at hj
  have hC : C ≤ |C| := le_abs_self C
  have : (j : ℝ) * (2 * (|C| + 1)) ≥ 2 * (C * j) + 2 * j := by nlinarith [abs_nonneg C]
  nlinarith

/-- The advice length `b(n) = ⌈log₂ log₂ n⌉ - 1` satisfies `b(n) < log₂ log₂ n` whenever
`log₂ log₂ n > 0` (the hypothesis of Theorem 3.7). -/
theorem bLongCD_lt {n : ℕ} (h : 0 < Real.logb 2 (Real.logb 2 n)) :
    ((⌈Real.logb 2 (Real.logb 2 n)⌉₊ - 1 : ℕ) : ℝ) < Real.logb 2 (Real.logb 2 n) := by
  have h1 := Nat.ceil_lt_add_one h.le
  have h2 : 1 ≤ ⌈Real.logb 2 (Real.logb 2 n)⌉₊ := Nat.one_le_iff_ne_zero.2 (by simpa using h)
  push_cast [Nat.cast_sub h2]
  linarith

/-- **The upper bound of Theorem 3.7 is false** close to `b(n) = log log n`: with
`b(n) = ⌈log₂ log₂ n⌉ - 1 < log₂ log₂ n` bits, the optimal expected time `t(n)` (always `≥ 1`) is
not `O(log log n − b(n))`. -/
theorem theorem_3_7_upper_false :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      optTimeCD n (⌈Real.logb 2 (Real.logb 2 n)⌉₊ - 1) ≤
        ENNReal.ofReal (C * (Real.logb 2 (Real.logb 2 n) -
          (⌈Real.logb 2 (Real.logb 2 n)⌉₊ - 1 : ℕ))) := by
  rintro ⟨C, N, h⟩
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (4 * (|C| + 1) + N) (by norm_num : (1 : ℝ) < 2)
  set n := 2 ^ (2 ^ j + 1) with hn
  have hjN : N ≤ n := by
    have h1 : (N : ℝ) < ((2 ^ j : ℕ) : ℝ) := by push_cast; linarith [abs_nonneg C]
    have h1' : N < 2 ^ j := by exact_mod_cast h1
    have h2 : 2 ^ j < n := by
      rw [hn]; exact (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have key := h n hjN
  have hlog : Real.logb 2 n = 2 ^ j + 1 := by
    rw [hn, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
      mul_one]
    push_cast; ring
  rw [hlog] at key
  -- `log₂ (2^j + 1) ∈ (j, j + 1]`
  have hlo : (j : ℝ) < Real.logb 2 (2 ^ j + 1) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]; linarith
  have hhi : Real.logb 2 (2 ^ j + 1) ≤ j + 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_succ]
    linarith
  have hceil : ⌈Real.logb 2 (2 ^ j + 1)⌉₊ = j + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    exact ⟨by linarith, hhi⟩
  rw [hceil, Nat.add_sub_cancel] at key
  have h1 := (one_le_optTimeCD (by positivity) j).trans key
  rw [ENNReal.one_le_ofReal] at h1
  -- `log₂ (2^j + 1) - j = log₂ (1 + 2^{-j}) ≤ 2 / 2^j`
  have hdiff : Real.logb 2 (2 ^ j + 1) - j ≤ 2 / 2 ^ j := by
    have hpos : (0 : ℝ) < 2 ^ j := by positivity
    have : Real.logb 2 (2 ^ j + 1) - j = Real.logb 2 (1 + 1 / 2 ^ j) := by
      rw [show (1 : ℝ) + 1 / 2 ^ j = (2 ^ j + 1) / 2 ^ j by field_simp,
        Real.logb_div (by positivity) hpos.ne']
      congr 1
      rw [show ((2 : ℝ) ^ j) = (2 : ℝ) ^ (j : ℝ) by rw [Real.rpow_natCast],
        Real.logb_rpow (by norm_num) (by norm_num)]
    rw [this, Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 2 ^ j by positivity)
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have : (0 : ℝ) ≤ 1 / 2 ^ j := by positivity
    calc Real.log (1 + 1 / 2 ^ j) ≤ 1 / 2 ^ j := by linarith
      _ = 2 / 2 ^ j * (1 / 2) := by ring
      _ ≤ 2 / 2 ^ j * Real.log 2 := by gcongr
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hdiff0 : 0 ≤ Real.logb 2 (2 ^ j + 1) - j := by linarith
  have : C * (Real.logb 2 (2 ^ j + 1) - j) ≤ |C| * (2 / 2 ^ j) := by
    calc C * (Real.logb 2 (2 ^ j + 1) - j) ≤ |C| * (Real.logb 2 (2 ^ j + 1) - j) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hdiff0
      _ ≤ |C| * (2 / 2 ^ j) := mul_le_mul_of_nonneg_left hdiff (abs_nonneg C)
  have h3 : |C| * (2 / 2 ^ j) < 1 := by
    rw [mul_div_assoc', div_lt_one hpos]; linarith [abs_nonneg C]
  linarith

end Podc.ContentionPredictions
