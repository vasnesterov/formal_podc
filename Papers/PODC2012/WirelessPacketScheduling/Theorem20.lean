import Papers.PODC2012.WirelessPacketScheduling.LocalClock
import Papers.PODC2012.WirelessPacketScheduling.Queue
import Cslib.Probability.CoinField

/-!
# Theorem 20: local clocks cost a factor `≈ m / (2 ln m)`

The network of Figure 1 has `m` links: `m - 1` short ones and one long one. With a global clock,
the TDMA protocol (even slots for the short links, odd slots for the long link) is stable for every
`λ < 1/2` (`Queue.tdma_stable` for the long link; a short link is the same queue). The paper shows
that with local clocks no acknowledgement-based protocol is stable for `λ ≥ ln m / m`, and
concludes that no such protocol is `m / (2 ln m)`-competitive.

* `theorem_20`: for every `m ≥ 4` there is `λ < ln m / m` at which no protocol with local clocks is
  stable on the network of Figure 1; with the TDMA rate `1/2` this gives competitive ratio
  `> (1/2) / (ln m / m) = m / (2 ln m)`. (Strictness matters: `m/(2 ln m)`-competitiveness only
  asks for stability at rates `< ln m / m`, which the paper's "no stability for `λ ≥ ln m/m`" does
  not exclude.)
* `paper_step_fails_four`: the paper's inequality `(1 - (1 - 1/m) λ)^{m-1} < 1/e^{ln m} ≤ λ` at
  `λ = ln m / m` fails for `m = 4` (both parts); we avoid the factor `1 - 1/m` (`no_stable_long_link`
  uses windows of arbitrary length).
* `immediate_stable_two`, `immediate_stable_three`: for `m = 2, 3` the claim "no protocol with only a
  local clock is stable for `λ ≥ ln m / m`" is false: if every short link sends each packet in the
  slot it arrives (no clock needed at all), the long link gets i.i.d. transmission opportunities of
  probability `(1 - λ)^{m-1} > λ` at `λ = ln m / m`, and its queue is stable.
-/

namespace Podc.WirelessPacketScheduling.Theorem20

open MeasureTheory LocalClock

/-! ### Numerics -/

lemma log_two_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
lemma log_two_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma log_three_lt : Real.log 3 < 1.1364 := by
  have h : Real.log 3 = Real.log 4 + Real.log (3 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
  rw [h, log_four]; linarith [log_two_lt]

lemma log_five_gt : 1.58 < Real.log 5 := by
  have h : Real.log 5 = Real.log 4 - Real.log (4 / 5) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
  rw [h, log_four]; linarith [log_two_gt]

/-- `(1 - ln m / m)^{m-1} < ln m / m` for every `m ≥ 4`. -/
lemma key_ineq (m : ℕ) (hm : 4 ≤ m) :
    (1 - Real.log m / m) ^ (m - 1) < Real.log m / m := by
  rcases Nat.lt_or_ge m 5 with h4 | h5
  · obtain rfl : m = 4 := by omega
    norm_num [log_four]
    have h1 := log_two_lt; have h2 := log_two_gt
    have hx : (1 - 2 * Real.log 2 / 4) ^ 3 ≤ (1 - 2 * 0.6931471803 / 4) ^ 3 := by
      apply pow_le_pow_left₀ (by linarith); linarith
    norm_num at hx ⊢
    nlinarith
  · have hm0 : (0 : ℝ) < m := by positivity
    have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast h5
    set x := Real.log m / m with hx
    have hlog5 : Real.log 5 ≤ Real.log m := Real.log_le_log (by norm_num) hm5
    have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg (by linarith)) hm0.le
    have hx1 : x ≤ 1 := by
      rw [hx, div_le_one hm0]
      have := Real.log_le_sub_one_of_pos hm0; linarith
    -- `(1 - x)^{m-1} ≤ exp(-x (m-1)) = exp(-ln m) · exp(x)`
    have h1 : (1 - x) ^ (m - 1) ≤ Real.exp (-x) ^ (m - 1) := by
      apply pow_le_pow_left₀ (by linarith)
      have := Real.add_one_le_exp (-x); linarith
    have h2 : Real.exp (-x) ^ (m - 1) = Real.exp x / m := by
      rw [← Real.exp_nat_mul, Nat.cast_sub (by omega)]
      have : (((m : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) * -x = x - Real.log m := by
        rw [hx]; field_simp; push_cast; ring
      rw [this, Real.exp_sub, Real.exp_log hm0]
    -- `exp(x) ≤ exp(ln 5 / 5) = 5^{1/5} < 1.5 < ln 5 ≤ ln m`
    have h3 : x ≤ Real.log 5 / 5 := by
      have := Real.log_div_self_antitoneOn (a := (5 : ℝ)) (b := (m : ℝ))
        (by show Real.exp 1 ≤ (5 : ℝ); linarith [Real.exp_one_lt_d9])
        (by show Real.exp 1 ≤ (m : ℝ); linarith [Real.exp_one_lt_d9]) hm5
      simpa [hx] using this
    have h4 : Real.exp (Real.log 5 / 5) < 1.5 := by
      have h : Real.exp (Real.log 5 / 5) ^ 5 = 5 := by
        rw [← Real.exp_nat_mul]; push_cast
        rw [show (5 : ℝ) * (Real.log 5 / 5) = Real.log 5 by ring, Real.exp_log (by norm_num)]
      by_contra hc
      push Not at hc
      have : (1.5 : ℝ) ^ 5 ≤ Real.exp (Real.log 5 / 5) ^ 5 := pow_le_pow_left₀ (by norm_num) hc 5
      rw [h] at this; norm_num at this
    have h5' : Real.exp x < Real.log m := by
      calc Real.exp x ≤ Real.exp (Real.log 5 / 5) := Real.exp_le_exp.2 h3
        _ < 1.5 := h4
        _ < Real.log 5 := by linarith [log_five_gt]
        _ ≤ Real.log m := hlog5
    calc (1 - x) ^ (m - 1) ≤ Real.exp x / m := h1.trans h2.le
      _ < Real.log m / m := by gcongr

/-- For `m ≥ 4` there is `λ < ln m / m` (with `0 < λ ≤ 1`) such that `(1 - λ)^{m-1} < λ`. -/
lemma exists_rate_below (m : ℕ) (hm : 4 ≤ m) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ lam < Real.log m / m ∧ (1 - lam) ^ (m - 1) < lam := by
  set x := Real.log m / m
  have hm0 : (0 : ℝ) < m := by positivity
  have hx0 : 0 < x := div_pos (Real.log_pos (by norm_cast; omega)) hm0
  have hx1 : x ≤ 1 := by
    rw [div_le_one hm0]; have := Real.log_le_sub_one_of_pos hm0; linarith
  have hk := key_ineq m hm
  -- continuity at `x`
  have hc : ContinuousAt (fun l : ℝ => (1 - l) ^ (m - 1) - l) x := by fun_prop
  have hev : ∀ᶠ l in nhdsWithin x (Set.Iio x), (1 - l) ^ (m - 1) - l < 0 :=
    (hc.eventually (gt_mem_nhds (by linarith : (1 - x) ^ (m - 1) - x < 0))).filter_mono
      nhdsWithin_le_nhds
  have hev2 : ∀ᶠ l in nhdsWithin x (Set.Iio x), 0 < l :=
    (lt_mem_nhds hx0).filter_mono nhdsWithin_le_nhds
  have hev3 : ∀ᶠ l in nhdsWithin x (Set.Iio x), l < x := self_mem_nhdsWithin
  obtain ⟨l, h1, h2, h3⟩ := (hev.and (hev2.and hev3)).exists
  exact ⟨l, h2, by linarith, h3, by linarith⟩

/-- **Theorem 20** (repaired form). For the network of Figure 1 with `m ≥ 4` links (`m - 1` short
links), there is an arrival rate `λ < ln m / m` such that for every family of stable executions of
the short links with rate `λ` (whatever acknowledgement-based protocol with a local clock they run)
there are switch-on times of the short links for which no execution of the long link with rate `λ`
is stable. Since TDMA with a global clock is stable for all `λ < 1/2` (`Queue.tdma_stable`), no
protocol with local clocks is `m / (2 ln m)`-competitive. -/
theorem theorem_20 (m : ℕ) (hm : 4 ≤ m) :
    ∃ lam : ℝ, 0 < lam ∧ lam < Real.log m / m ∧
      ∀ (Ω : Fin (m - 1) → Type) [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
        [∀ i, IsProbabilityMeasure (μ i)] (S : ∀ i, LinkExec (Ω i)),
        (∀ i, (S i).Rate (μ i) lam) → (∀ i, (S i).Stable (μ i)) →
        ∃ d : Fin (m - 1) → ℕ, ∀ (G : Type) [MeasurableSpace G] (ν : Measure G)
          [IsProbabilityMeasure ν] (LL : LongLink μ S d G ν), LL.L.Rate ν lam → ¬ LL.L.Stable ν := by
  obtain ⟨lam, h0, h1, h2, h3⟩ := exists_rate_below m hm
  exact ⟨lam, h0, h2, fun Ω _ μ _ S hR hS => no_stable_long_link μ S lam h1 h3 hR hS⟩

/-- The paper's chain `(1 - (1 - 1/m) λ)^{m-1} < 1/e^{ln m} ≤ λ` at `λ = ln m / m` fails for
`m = 4`: the left-hand side exceeds `λ` (and hence `1/m`). -/
theorem paper_step_fails_four :
    Real.log 4 / 4 < (1 - (1 - 1 / 4) * (Real.log 4 / 4)) ^ (4 - 1) := by
  rw [log_four]
  have h1 := log_two_lt; have h2 := log_two_gt
  have hx : (1 - (1 - 1 / 4) * (2 * 0.6931471808 / 4)) ^ 3 ≤
      (1 - (1 - 1 / 4) * (2 * Real.log 2 / 4)) ^ 3 := by
    apply pow_le_pow_left₀ (by norm_num); nlinarith
  norm_num at hx ⊢
  nlinarith

/-! ### `m = 2, 3`: a local protocol is stable at `λ = ln m / m` -/

/-- `ln m / m` as an element of `ℝ≥0`. -/
noncomputable def rate (m : ℕ) : NNReal := ⟨Real.log m / m, by positivity⟩

lemma rate_coe (m : ℕ) : (rate m : ℝ) = Real.log m / m := rfl

lemma rate_le_one (m : ℕ) : rate m ≤ 1 := by
  show Real.log m / m ≤ 1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_one hm0]; have := Real.log_le_sub_one_of_pos hm0; linarith

/-- Transmission-opportunity probability of the long link when each of the `m - 1` short links
transmits exactly in the slots where a packet arrives: `(1 - λ)^{m-1}`. -/
noncomputable def opp (m : ℕ) : NNReal := (1 - rate m) ^ (m - 1)

lemma opp_le_one (m : ℕ) : opp m ≤ 1 := pow_le_one₀ (by positivity) tsub_le_self

lemma rate_lt_opp_two : rate 2 < opp 2 := by
  rw [← NNReal.coe_lt_coe, opp, NNReal.coe_pow, NNReal.coe_sub (rate_le_one 2), NNReal.coe_one]
  rw [rate_coe]
  norm_num
  linarith [log_two_lt]

lemma rate_lt_opp_three : rate 3 < opp 3 := by
  rw [← NNReal.coe_lt_coe]
  rw [opp, NNReal.coe_pow, NNReal.coe_sub (rate_le_one 3), NNReal.coe_one]
  rw [rate_coe]
  norm_num
  have h := log_three_lt
  have hpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  nlinarith

/-- For `m = 2` the paper's claim "for `λ ≥ ln m / m` no acknowledgement-based protocol with only
a local clock can be stable" is false: with short links sending each packet on arrival, the long
link's queue (i.i.d. arrivals `λ = ln 2 / 2`, i.i.d. opportunities `1 - λ`) is stable. -/
theorem immediate_stable_two :
    Queue.Stable (Queue.slot (rate 2) (opp 2) (rate_le_one 2) (opp_le_one 2)) :=
  Queue.slot_stable _ _ _ _ rate_lt_opp_two

/-- Same for `m = 3` (`λ = ln 3 / 3 ≈ 0.366 < (1 - λ)^2 ≈ 0.402`). -/
theorem immediate_stable_three :
    Queue.Stable (Queue.slot (rate 3) (opp 3) (rate_le_one 3) (opp_le_one 3)) :=
  Queue.slot_stable _ _ _ _ rate_lt_opp_three

/-! ### Non-vacuity: stable short links with any rate exist -/

open Cslib.Probability unitInterval

/-- A short link that sends every packet in the slot it arrives, with i.i.d. `Bernoulli(p)`
arrivals: `tx = arr = dlv`, queue `0`. -/
noncomputable def immediateExec : LinkExec (ℕ → Bool) where
  tx τ ω := ω τ
  arr τ ω := (ω τ).toNat
  dlv τ ω := (ω τ).toNat
  q _ _ := 0
  q_zero _ := rfl
  q_succ _ _ := by simp
  arr_le τ ω := by cases ω τ <;> simp
  dlv_le _ _ := le_rfl
  meas_tx τ := measurable_pi_apply τ
  meas_arr τ := (measurable_from_top (f := Bool.toNat)).comp (measurable_pi_apply τ)
  meas_dlv τ := (measurable_from_top (f := Bool.toNat)).comp (measurable_pi_apply τ)

lemma immediateExec_rate (p : I) : immediateExec.Rate (coinMeasure p) p := by
  intro τ
  have := immediateExec.integral_tx (coinMeasure p) τ
  simp only [immediateExec] at this ⊢
  rw [this, coinMeasure_real_coord]
  simp

lemma immediateExec_stable (p : I) : immediateExec.Stable (coinMeasure p) :=
  ⟨0, fun τ => by simp [immediateExec]⟩

end Podc.WirelessPacketScheduling.Theorem20
