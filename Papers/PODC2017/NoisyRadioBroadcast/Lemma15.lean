import Papers.PODC2017.NoisyRadioBroadcast.StarLower
import Papers.PODC2017.NoisyRadioBroadcast.StarUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 15: the adaptive routing throughput of the star with receiver faults is `Θ(1/log n)`
-/

namespace Podc.NoisyRadioBroadcast

open Finset Filter
open scoped ENNReal

variable {n k : ℕ}

/-! ### From round bounds to throughput bounds -/

theorem inv_le_ratio {k c : ℕ} (hk : k ≠ 0) {N : ℕ∞} (hN : N ≤ ((k * c : ℕ) : ℕ∞)) :
    (c : ℝ≥0∞)⁻¹ ≤ (k : ℝ≥0∞) / (N : ℝ≥0∞) := by
  have hN' : (N : ℝ≥0∞) ≤ ((k * c : ℕ) : ℝ≥0∞) := by exact_mod_cast hN
  calc (c : ℝ≥0∞)⁻¹ = (k : ℝ≥0∞) / ((k * c : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast hk))
          (Or.inl (ENNReal.natCast_ne_top k)), mul_comm (k : ℝ≥0∞)⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast hk) (ENNReal.natCast_ne_top k), mul_one]
    _ ≤ (k : ℝ≥0∞) / (N : ℝ≥0∞) := ENNReal.div_le_div_left hN' _

theorem ratio_le {k m T : ℕ} (hT : T ≠ 0) (hm : k ≤ 2 * m) {N : ℕ∞}
    (hN : ((m * T : ℕ) : ℕ∞) ≤ N) : (k : ℝ≥0∞) / (N : ℝ≥0∞) ≤ 2 / (T : ℝ≥0∞) := by
  have hN' : ((m * T : ℕ) : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hN
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast hT
  have hc : (2 : ℝ≥0∞) / T ≠ ⊤ := ENNReal.div_ne_top (by norm_num) hT0
  have hc0 : (2 : ℝ≥0∞) / T ≠ 0 := ENNReal.div_ne_zero.2 ⟨by norm_num, ENNReal.natCast_ne_top T⟩
  rw [ENNReal.div_le_iff_le_mul (Or.inr hc) (Or.inr hc0)]
  calc (k : ℝ≥0∞) ≤ ((2 * m : ℕ) : ℝ≥0∞) := by exact_mod_cast hm
    _ = 2 / T * ((m * T : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_mul, mul_comm (m : ℝ≥0∞), ← mul_assoc,
          ENNReal.div_mul_cancel hT0 (ENNReal.natCast_ne_top T)]
        norm_num
    _ ≤ 2 / T * (N : ℝ≥0∞) := by gcongr

/-! ### Round bounds on the star -/

/-- Rounds lower bound (Lemma 15, impossibility part): if `n p^T ≥ 2`, every adaptive routing
schedule needs at least `⌈k/2⌉ · T` rounds to deliver `k ≥ 2` messages with probability
`1 - 1/k`. -/
theorem star_routingRounds_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T : ℕ}
    (hT : 2 ≤ (n : ℝ) * p ^ T) (hk : 2 ≤ k) :
    (((k - k / 2) * T : ℕ) : ℕ∞) ≤ routingRounds (star n) none .receiver p k := by
  refine le_iInf₂ fun R ⟨sch, hs⟩ => ?_
  by_contra hlt
  push Not at hlt
  have hlt' : R < (k - (k / 2 + 1) + 1) * T := by
    have : k - (k / 2 + 1) + 1 = k - k / 2 := by omega
    rw [this]; exact_mod_cast hlt
  have hb := star_prob_delivered_le hp0 hp1 sch (m := k / 2 + 1) (by omega) hlt'
  -- numerical bound
  have hpT : 0 ≤ p ^ T := pow_nonneg hp0 _
  have hpT1 : p ^ T ≤ 1 := pow_le_one₀ hp0 hp1
  have h1 : (1 - p ^ T) ^ n ≤ Real.exp (-2) := by
    calc (1 - p ^ T) ^ n ≤ (Real.exp (-p ^ T)) ^ n :=
          pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-p ^ T); linarith) n
      _ = Real.exp (-(n * p ^ T)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
  have h2 : ((k.choose (k / 2 + 1) : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow _ _
  have h3 : ((k.choose (k / 2 + 1) : ℕ) : ℝ) * ((1 - p ^ T) ^ n) ^ (k / 2 + 1) ≤
      2 ^ k * Real.exp (-2) ^ (k / 2 + 1) := by
    gcongr
  have h4 : (2 : ℝ) ^ k * Real.exp (-2) ^ (k / 2 + 1) ≤ Real.exp (-1) := by
    have e2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc (2 : ℝ) ^ k * Real.exp (-2) ^ (k / 2 + 1) ≤ Real.exp 1 ^ k * Real.exp (-2) ^ (k / 2 + 1) := by
          gcongr
      _ = Real.exp (k - 2 * (k / 2 + 1 : ℕ)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (-1) := Real.exp_le_exp.2 (by
          have : (k : ℝ) + 1 ≤ 2 * ((k / 2 + 1 : ℕ) : ℝ) := by
            have : k + 1 ≤ 2 * (k / 2 + 1) := by omega
            exact_mod_cast this
          linarith)
  have h5 : Real.exp (-1) < 1 - 1 / (k : ℝ) := by
    have := Real.exp_neg_one_lt_half
    have : 1 / (k : ℝ) ≤ 1 / 2 := by
      rw [one_div_le_one_div (by positivity) (by norm_num)]; exact_mod_cast hk
    linarith
  unfold RoutingSucceeds at hs
  change 1 - 1 / (k : ℝ) ≤ prob p R (fun ω => Delivered (starRun sch ω R)) at hs
  linarith

/-! ### Lemma 15 -/

/-- **Lemma 15** of the paper: with receiver faults of constant probability `p ∈ (0, 1)`, the
adaptive routing throughput of the star with `n` leaves is `Θ(1/log n)`. -/
theorem lemma15 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal (c₁ / Real.log n) ≤ routingThroughput (star n) none .receiver p ∧
        routingThroughput (star n) none .receiver p ≤ ENNReal.ofReal (c₂ / Real.log n) := by
  set L := Real.log (1 / p) with hL
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hp0]; linarith)
  have hb1 : 1 < 2 / (1 + p) := by rw [lt_div_iff₀ (by linarith)]; linarith
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (4 : ℝ) hb1
  -- thresholds
  set n₀ : ℕ := ⌈Real.exp ((1 + b) * L + 4 * (Real.log 2 + L))⌉₊ + 2 with hn₀
  refine ⟨L / 2, by positivity, 8 * L, by positivity, n₀, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : (1 + b) * L + 4 * (Real.log 2 + L) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    calc _ ≤ (⌈Real.exp ((1 + b) * L + 4 * (Real.log 2 + L))⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast (by omega : ⌈Real.exp ((1 + b) * L + 4 * (Real.log 2 + L))⌉₊ ≤ n)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogpos : 0 < Real.log n := by nlinarith
  have hbase : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; linarith
  constructor
  · -- possibility: `a = ⌈log_{1/p} n⌉`
    set a : ℕ := ⌈Real.logb (1 / p) n⌉₊ with ha
    have ha1 : (n : ℝ) * p ^ a ≤ 1 := by
      have h1 : (n : ℝ) ≤ (1 / p) ^ a := by
        calc (n : ℝ) = (1 / p) ^ Real.logb (1 / p) n := (Real.rpow_logb (by positivity)
              hbase.ne' hnpos).symm
          _ ≤ (1 / p) ^ (a : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase.le (Nat.le_ceil _)
          _ = (1 / p) ^ a := Real.rpow_natCast _ _
      rw [one_div_pow, le_div_iff₀ (pow_pos hp0 _)] at h1
      linarith
    have hround : ∀ k ≥ 1, routingRounds (star n) none .receiver p k ≤ ((k * (a + b) : ℕ) : ℕ∞) :=
      fun k hk => iInf₂_le _ ⟨greedy, star_greedy_succeeds hp0.le hp1 ha1 hb.le hk⟩
    have hthr : ((a + b : ℕ) : ℝ≥0∞)⁻¹ ≤ routingThroughput (star n) none .receiver p := by
      refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
      refine ((eventually_ge_atTop 1).mono fun k hk => ?_).frequently
      exact inv_le_ratio (by omega) (hround k hk)
    refine le_trans ?_ hthr
    have hlogb : Real.logb (1 / p) n = Real.log n / L := rfl
    have ha2 : (a : ℝ) ≤ Real.log n / L + 1 := by
      rw [← hlogb]; exact (Nat.ceil_lt_add_one (Real.logb_nonneg hbase (by
        exact_mod_cast (by omega : 1 ≤ n)))).le
    have hab : (0 : ℝ) < (a + b : ℕ) := by
      have : 0 < Real.logb (1 / p) n := Real.logb_pos hbase (by exact_mod_cast (by omega : 1 < n))
      have : 0 < a := Nat.ceil_pos.2 this
      exact_mod_cast (by omega : 0 < a + b)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hab]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hlogpos, ← div_eq_inv_mul, le_div_iff₀ hab]
    push_cast
    calc L / 2 * (a + b) ≤ L / 2 * (Real.log n / L + 1 + b) := by gcongr
      _ = Real.log n / 2 + L * (1 + b) / 2 := by field_simp; ring
      _ ≤ Real.log n := by nlinarith
  · -- impossibility: `T = ⌊log_{1/p} (n/2)⌋`
    set T : ℕ := ⌊Real.logb (1 / p) (n / 2)⌋₊ with hTdef
    have hn2' : (1 : ℝ) ≤ n / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 2 ≤ n)
    have hT2 : 2 ≤ (n : ℝ) * p ^ T := by
      have h1 : (1 / p) ^ T ≤ (n : ℝ) / 2 := by
        calc (1 / p) ^ T = (1 / p) ^ (T : ℝ) := (Real.rpow_natCast _ _).symm
          _ ≤ (1 / p) ^ Real.logb (1 / p) (n / 2) :=
              Real.rpow_le_rpow_of_exponent_le hbase.le (Nat.floor_le (Real.logb_nonneg hbase hn2'))
          _ = n / 2 := Real.rpow_logb (by positivity) hbase.ne' (by linarith)
      rw [one_div_pow, div_le_iff₀ (pow_pos hp0 _)] at h1
      linarith
    have hlogb : Real.logb (1 / p) (n / 2) = (Real.log n - Real.log 2) / L := by
      rw [Real.logb, Real.log_div (by positivity) (by norm_num)]
    have hTlb : (Real.log n - Real.log 2) / L - 1 < T := by
      rw [← hlogb]; exact Nat.sub_one_lt_floor _
    have hLT : Real.log n - Real.log 2 - L < L * T := by
      have := (div_sub_one hL0.ne').symm ▸ hTlb
      rw [div_lt_iff₀ hL0] at this; linarith
    have hT0 : T ≠ 0 := by
      intro h; rw [h] at hLT; push_cast at hLT; nlinarith
    have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT0
    have hthr : routingThroughput (star n) none .receiver p ≤ 2 / (T : ℝ≥0∞) := by
      refine limsup_le_of_le (by isBoundedDefault) ?_
      refine (eventually_ge_atTop 2).mono fun k hk => ?_
      exact ratio_le hT0 (by omega) (star_routingRounds_ge hp0.le hp1.le hT2 hk)
    refine hthr.trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_div_of_pos hTpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ hTpos hlogpos]
    nlinarith

end Podc.NoisyRadioBroadcast
