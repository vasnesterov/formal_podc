import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Entropy lower bound for uniform contention resolution (Theorem 2.4)

Gilbert, Newport, Vaidya, Weaver. *Contention Resolution with Predictions.* PODC 2021.

**Model.** A single-hop synchronous radio channel *without collision detection*. A *uniform*
algorithm is a sequence of probabilities `p 0, p 1, …` (`UniformAlg`): in round `r` (counted from
`0`) every participant transmits independently with probability `p r`. Without collision detection
every unsuccessful round sounds like silence, so the behaviour cannot depend on feedback; with `k`
participants round `r` succeeds (exactly one transmitter) with probability
`succProb k (p r) = k · p r · (1 - p r)^(k-1)`, independently over rounds. Hence
`surv A k m = ∏_{r < m} (1 - succProb k (p r))` is the probability that rounds `0, …, m-1` all
fail, and the expected number of rounds until success is `expTime A k = ∑_{m ≥ 0} Pr[T > m]`
(an element of `ℝ≥0∞`; it is `⊤` if the algorithm does not terminate almost surely).

The number of participants is drawn from a distribution `X` on `{2, …, n}` (the paper assumes sizes
`≥ 2`, footnote 4); `tX A X n = ∑_k X k · expTime A k` is the expected running time. The condensed
distribution `c(X)` aggregates `X` over the geometric ranges `(2^(y-1), 2^y]`, `y = 1, …, ⌈log n⌉`
(the range of `k` is `Nat.clog 2 k`), and `entropyBits X n = H(c(X))` is its Shannon entropy in
bits.

**Main result** (`theorem_2_4`): there is a universal constant `C > 0` such that for every `n ≥ 4`,
every size distribution `X` on `{2, …, n}` and every uniform algorithm `A`,
`t_X ≥ C · 2^H(c(X)) / log log n`, i.e. `t_X = Ω(2^H(c(X)) / log log n)`. We get `C = 1/(88 e)`
(`theorem_2_4_explicit`).

**Proof route.** The paper's proof (Lemmas 2.5–2.7) is repaired as follows.
* Lemma 2.6 analogue (`le_mul_of_good`, `mul_le_of_good`): if a round succeeds with probability at
  least `ε` for `k ≥ 2` participants, then `ε ≤ k p ≤ 8/ε`.
* Per-size bound (`expTime_ge`): if rounds `0, …, R-1` all succeed with probability `< ε` and
  `R ε ≤ 1/2`, then `E[T] ≥ (R+1)/2` (Weierstrass product inequality; this replaces the paper's
  incorrect "mean ⇒ median" step).
* A *guess index* `guess` on ranges (essentially the first round that is good for some size in the
  range) has fibers of size `O(log log n)` (`card_fiber_guess_le`) and
  `E[T_k] ≥ (guess (range k) + 1)/4` (`expTime_ge_guess`).
* Guesswork / Gibbs lemma (`sum_negMulLog_le_of_card_fiber_le`): for a distribution `q` and an index
  `h` with fibers of size `≤ K`, `H(q) ≤ log K + log (E[h+1] + 1) + 1` (nats). This replaces the
  paper's use of the source coding theorem for a code that is not uniquely decodable.
-/

namespace Podc.ContentionPredictions

open Finset

/-- A uniform contention-resolution algorithm without collision detection: in round `r` (counted
from `0`) every participant transmits with probability `p r`. -/
structure UniformAlg where
  /-- Transmission probability in round `r`. -/
  p : ℕ → ℝ
  nonneg : ∀ r, 0 ≤ p r
  le_one : ∀ r, p r ≤ 1

/-- Probability that exactly one of `k` independent participants, each transmitting with probability
`q`, transmits. -/
noncomputable def succProb (k : ℕ) (q : ℝ) : ℝ := k * q * (1 - q) ^ (k - 1)

namespace UniformAlg

variable (A : UniformAlg)

/-- Probability that rounds `0, …, m-1` all fail with `k` participants. -/
noncomputable def surv (k m : ℕ) : ℝ := ∏ r ∈ range m, (1 - succProb k (A.p r))

/-- Expected number of rounds until the first success with `k` participants:
`E[T] = ∑_{m ≥ 0} Pr[T > m]`. -/
noncomputable def expTime (k : ℕ) : ENNReal := ∑' m, ENNReal.ofReal (A.surv k m)

/-- Expected running time when the number of participants is drawn from `X` on `{2, …, n}`. -/
noncomputable def tX (X : ℕ → ℝ) (n : ℕ) : ENNReal :=
  ∑ k ∈ Icc 2 n, ENNReal.ofReal (X k) * A.expTime k

end UniformAlg

/-- The condensed distribution `c(X)`: the mass of the range `(2^(y-1), 2^y]`. -/
noncomputable def condensed (X : ℕ → ℝ) (n y : ℕ) : ℝ :=
  ∑ k ∈ (Icc 2 n).filter (fun k => Nat.clog 2 k = y), X k

/-- Shannon entropy in bits of the condensed distribution `c(X)` (ranges `1, …, ⌈log n⌉`). -/
noncomputable def entropyBits (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ y ∈ Icc 1 (Nat.clog 2 n), Real.negMulLog (condensed X n y) / Real.log 2

/-! ### Elementary facts about `succProb` -/

theorem succProb_nonneg (k : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : 0 ≤ succProb k q := by
  unfold succProb
  have : 0 ≤ 1 - q := by linarith
  positivity

theorem succProb_le_one (k : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : succProb k q ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [succProb]
  have hq : 0 ≤ 1 - q := by linarith
  have key := add_pow q (1 - q) k
  rw [add_sub_cancel, one_pow] at key
  have h1mem : 1 ∈ range (k + 1) := by simp; omega
  have := Finset.single_le_sum (f := fun m => q ^ m * (1 - q) ^ (k - m) * (k.choose m : ℝ))
    (fun m _ => by positivity) h1mem
  simp only [pow_one, Nat.choose_one_right] at this
  unfold succProb
  linarith [key, this, show (k : ℝ) * q * (1 - q) ^ (k - 1) = q * (1 - q) ^ (k - 1) * k by ring]

/-- Weierstrass product inequality: `∏ (1 - s r) ≥ 1 - ∑ s r` for `s r ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod (s : ℕ → ℝ) (h0 : ∀ r, 0 ≤ s r) (h1 : ∀ r, s r ≤ 1) (m : ℕ) :
    1 - ∑ r ∈ range m, s r ≤ ∏ r ∈ range m, (1 - s r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, prod_range_succ]
    have hS : 0 ≤ ∑ r ∈ range m, s r := sum_nonneg fun r _ => h0 r
    have hm : 0 ≤ 1 - s m := by linarith [h1 m]
    nlinarith [mul_le_mul_of_nonneg_right ih hm, h0 m]

/-- **Per-size bound.** If rounds `0, …, R-1` all succeed with probability `< ε` for `k`
participants and `R ε ≤ 1/2`, then the expected number of rounds is at least `(R + 1)/2`. -/
theorem UniformAlg.expTime_ge (A : UniformAlg) (k R : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hR : R * ε ≤ 1 / 2) (hbad : ∀ r < R, succProb k (A.p r) < ε) :
    ENNReal.ofReal ((R + 1) / 2) ≤ A.expTime k := by
  have hsurv : ∀ m ∈ range (R + 1), (1 / 2 : ℝ) ≤ A.surv k m := by
    intro m hm
    rw [mem_range] at hm
    have hW := one_sub_sum_le_prod (fun r => succProb k (A.p r))
      (fun r => succProb_nonneg k (A.nonneg r) (A.le_one r))
      (fun r => succProb_le_one k (A.nonneg r) (A.le_one r)) m
    have hsum : ∑ r ∈ range m, succProb k (A.p r) ≤ m * ε := by
      calc ∑ r ∈ range m, succProb k (A.p r) ≤ ∑ r ∈ range m, ε :=
            sum_le_sum fun r hr => (hbad r (by rw [mem_range] at hr; omega)).le
        _ = m * ε := by simp
    have : (m : ℝ) * ε ≤ R * ε :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : m ≤ R)) hε
    unfold UniformAlg.surv
    linarith
  calc ENNReal.ofReal ((R + 1) / 2) = ∑ m ∈ range (R + 1), ENNReal.ofReal (1 / 2) := by
        rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; push_cast; ring
    _ ≤ ∑ m ∈ range (R + 1), ENNReal.ofReal (A.surv k m) :=
        sum_le_sum fun m hm => ENNReal.ofReal_le_ofReal (hsurv m hm)
    _ ≤ A.expTime k := ENNReal.sum_le_tsum _

/-- Lemma 2.6 of [Gilbert–Newport–Vaidya–Weaver, PODC 2021], lower half (contrapositive form):
a round that succeeds with probability at least `ε` has `ε ≤ k p`. -/
theorem le_mul_of_good {k : ℕ} {q ε : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (hgood : ε ≤ succProb k q) :
    ε ≤ k * q := by
  unfold succProb at hgood
  have : (1 - q) ^ (k - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have : 0 ≤ (k : ℝ) * q := by positivity
  nlinarith

/-- Lemma 2.6 of [Gilbert–Newport–Vaidya–Weaver, PODC 2021], upper half (contrapositive form):
for `k ≥ 2`, a round that succeeds with probability at least `ε > 0` has `k p ≤ 8 / ε`. -/
theorem mul_le_of_good {k : ℕ} (hk : 2 ≤ k) {q ε : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (hε : 0 < ε)
    (hgood : ε ≤ succProb k q) : k * q ≤ 8 / ε := by
  set x : ℝ := k * q with hx
  have hxpos : 0 < x := lt_of_lt_of_le hε (le_mul_of_good h0 h1 hgood)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- `(1 - q)^(k-1) ≤ exp (-x/2)`
  have hpow : (1 - q) ^ (k - 1) ≤ Real.exp (-(x / 2)) := by
    have h1q : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
    calc (1 - q) ^ (k - 1) ≤ Real.exp (-q) ^ (k - 1) :=
          pow_le_pow_left₀ (by linarith) h1q _
      _ = Real.exp (-(((k - 1 : ℕ) : ℝ) * q)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(x / 2)) := by
          apply Real.exp_le_exp.mpr
          have : ((k - 1 : ℕ) : ℝ) = k - 1 := by
            rw [Nat.cast_sub (by omega)]; simp
          rw [this, hx]
          nlinarith
  have hexp : x ^ 2 / 8 ≤ Real.exp (x / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := x / 2) (by positivity)
    nlinarith
  have hε' : ε ≤ x * Real.exp (-(x / 2)) := by
    unfold succProb at hgood
    calc ε ≤ x * (1 - q) ^ (k - 1) := hgood
      _ ≤ x * Real.exp (-(x / 2)) := mul_le_mul_of_nonneg_left hpow hxpos.le
  rw [Real.exp_neg] at hε'
  have hE : 0 < Real.exp (x / 2) := Real.exp_pos _
  rw [le_div_iff₀ hε]
  have : ε * Real.exp (x / 2) ≤ x := by
    calc ε * Real.exp (x / 2) ≤ x * (Real.exp (x / 2))⁻¹ * Real.exp (x / 2) :=
          mul_le_mul_of_nonneg_right hε' hE.le
      _ = x := by field_simp
  nlinarith

/-! ### Guesswork (Gibbs) lemma -/

/-- **Guesswork lemma.** Let `q` be a probability distribution on a finset `Y` and `h : ι → ℕ` an
index all of whose fibers on `Y` have at most `K` elements. Then the entropy of `q` (in nats) is at
most `log K + log (μ + 1) + 1`, where `μ = E_q[h + 1]`. (Gibbs' inequality against the reference
weights `a (1-a)^(h y) / K` with `a = 1/(μ+1)`.) -- CSLib candidate -/
theorem sum_negMulLog_le_of_card_fiber_le {ι : Type*} (Y : Finset ι) (q : ι → ℝ)
    (hq0 : ∀ y ∈ Y, 0 ≤ q y) (hq1 : ∑ y ∈ Y, q y = 1) (h : ι → ℕ) {K : ℝ} (hK : 0 < K)
    (hfib : ∀ j, ((Y.filter (fun y => h y = j)).card : ℝ) ≤ K) :
    ∑ y ∈ Y, Real.negMulLog (q y) ≤
      Real.log K + Real.log (∑ y ∈ Y, q y * (h y + 1) + 1) + 1 := by
  classical
  set μ := ∑ y ∈ Y, q y * (h y + 1) with hμ
  have hμh : μ = ∑ y ∈ Y, q y * h y + 1 := by
    have : ∑ y ∈ Y, q y * (h y + 1) = ∑ y ∈ Y, q y * h y + ∑ y ∈ Y, q y := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun y _ => by ring
    rw [hμ, this, hq1]
  have hqh : 0 ≤ ∑ y ∈ Y, q y * h y := sum_nonneg fun y hy => mul_nonneg (hq0 y hy) (by positivity)
  have hμ1 : 1 ≤ μ := by linarith
  set a : ℝ := 1 / (μ + 1) with ha
  set b : ℝ := μ / (μ + 1) with hb
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  have hb1 : b < 1 := by rw [hb, div_lt_one (by linarith)]; linarith
  have hab : 1 - b = a := by rw [ha, hb]; field_simp; ring
  set w : ι → ℝ := fun y => a * b ^ (h y) / K with hw
  have hwpos : ∀ y, 0 < w y := fun y => by positivity
  -- the reference weights have total mass at most one
  have hwsum : ∑ y ∈ Y, w y ≤ 1 := by
    have hgeom : ∑ y ∈ Y, b ^ (h y) ≤ K / a := by
      rw [sum_comp (fun j => b ^ j) h]
      calc ∑ j ∈ Y.image h, (Y.filter (fun y => h y = j)).card • b ^ j
          ≤ ∑ j ∈ Y.image h, K * b ^ j := by
            refine sum_le_sum fun j _ => ?_
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (hfib j) (by positivity)
        _ = K * ∑ j ∈ Y.image h, b ^ j := by rw [mul_sum]
        _ ≤ K * ∑' j, b ^ j := by
            gcongr
            exact Summable.sum_le_tsum _ (fun j _ => by positivity)
              (summable_geometric_of_lt_one hbpos.le hb1)
        _ = K / a := by rw [tsum_geometric_of_lt_one hbpos.le hb1, hab, div_eq_mul_inv]
    calc ∑ y ∈ Y, w y = a / K * ∑ y ∈ Y, b ^ (h y) := by
          rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; simp only [hw]; ring
      _ ≤ a / K * (K / a) := by gcongr
      _ = 1 := by field_simp
  -- pointwise Gibbs inequality
  have hpt : ∀ y ∈ Y, Real.negMulLog (q y) ≤ w y - q y - q y * Real.log (w y) := by
    intro y hy
    rcases (hq0 y hy).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [(hwpos y).le]
    · rw [Real.negMulLog]
      have := Real.log_le_sub_one_of_pos (div_pos (hwpos y) hpos)
      rw [Real.log_div (hwpos y).ne' hpos.ne'] at this
      have := mul_le_mul_of_nonneg_left this hpos.le
      have e : q y * (w y / q y - 1) = w y - q y := by field_simp
      linarith
  have hlogw : ∀ y, Real.log (w y) = Real.log a + h y * Real.log b - Real.log K := fun y => by
    simp only [hw]
    rw [Real.log_div (by positivity) hK.ne', Real.log_mul hapos.ne' (by positivity),
      Real.log_pow]
  have hloga : Real.log a = -Real.log (μ + 1) := by
    rw [ha, one_div, Real.log_inv]
  have hlogb : -Real.log b ≤ 1 / μ := by
    rw [← Real.log_inv, hb, inv_div]
    have := Real.log_le_sub_one_of_pos (show 0 < (μ + 1) / μ by positivity)
    have h' : (μ + 1) / μ - 1 = 1 / μ := by field_simp; ring
    linarith
  calc ∑ y ∈ Y, Real.negMulLog (q y)
      ≤ ∑ y ∈ Y, (w y - q y - q y * Real.log (w y)) := sum_le_sum hpt
    _ = ∑ y ∈ Y, w y - 1 - ∑ y ∈ Y, q y * Real.log (w y) := by
        rw [sum_sub_distrib, sum_sub_distrib, hq1]
    _ ≤ - ∑ y ∈ Y, q y * Real.log (w y) := by linarith
    _ = Real.log K + Real.log (μ + 1) + (∑ y ∈ Y, q y * h y) * (-Real.log b) := by
        have e : ∑ y ∈ Y, q y * Real.log (w y) =
            (Real.log a - Real.log K) + (∑ y ∈ Y, q y * h y) * Real.log b := by
          simp_rw [hlogw]
          have : ∀ y, q y * (Real.log a + h y * Real.log b - Real.log K) =
              q y * (Real.log a - Real.log K) + q y * h y * Real.log b := fun y => by ring
          simp_rw [this]
          rw [sum_add_distrib, ← sum_mul, ← sum_mul, hq1, one_mul]
        rw [e, hloga]; ring
    _ ≤ Real.log K + Real.log (μ + 1) + (μ - 1) * (1 / μ) := by
        rw [show ∑ y ∈ Y, q y * h y = μ - 1 by linarith]
        linarith [mul_le_mul_of_nonneg_left hlogb (by linarith : (0 : ℝ) ≤ μ - 1)]
    _ ≤ Real.log K + Real.log (μ + 1) + 1 := by
        have : (μ - 1) * (1 / μ) ≤ 1 := by
          rw [mul_one_div, div_le_one (by linarith)]; linarith
        linarith

/-! ### Ranges and the guess index -/

/-- A set of naturals whose pairwise "ratios" `2^y₂ / 2^y₁` are all below `M` has at most
`log₂ M + 1` elements. -/
theorem card_le_logb_add_one (S : Finset ℕ) {M : ℝ} (hM : 1 ≤ M)
    (hS : ∀ y₁ ∈ S, ∀ y₂ ∈ S, (2 : ℝ) ^ y₂ < M * 2 ^ y₁) :
    (S.card : ℝ) ≤ Real.logb 2 M + 1 := by
  have hlog : 0 ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) hM
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp; linarith
  set m := S.min' hne
  have hsub : S ⊆ Ico m (m + ⌈Real.logb 2 M⌉₊) := by
    intro y hy
    rw [mem_Ico]
    refine ⟨S.min'_le y hy, ?_⟩
    have h := hS m (S.min'_mem hne) y hy
    have h' : (2 : ℝ) ^ ((y : ℝ) - m) < M := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast,
        div_lt_iff₀ (by positivity)]
      exact h
    have := (Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith)).mpr h'
    have hc := Nat.le_ceil (Real.logb 2 M)
    have : (y : ℝ) < m + ⌈Real.logb 2 M⌉₊ := by linarith
    exact_mod_cast this
  have hcard := card_le_card hsub
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  calc (S.card : ℝ) ≤ ⌈Real.logb 2 M⌉₊ := by exact_mod_cast hcard
    _ ≤ Real.logb 2 M + 1 := (Nat.ceil_lt_add_one hlog).le

/-- The threshold `ε = 1/(2 ⌈log n⌉)` for a round to be *good*. -/
noncomputable def threshold (n : ℕ) : ℝ := 1 / (2 * Nat.clog 2 n)

theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n := by unfold threshold; positivity

theorem clog_mul_threshold (n : ℕ) : (Nat.clog 2 n : ℝ) * threshold n ≤ 1 / 2 := by
  unfold threshold
  rcases eq_or_ne (Nat.clog 2 n : ℝ) 0 with h | h
  · rw [h]; norm_num
  · rw [le_div_iff₀ (by norm_num)]
    field_simp
    rfl

open Classical in
/-- The *guess index* of the range `y`: the first round `r < ⌈log n⌉` that is good (success
probability `≥ threshold n`) for some size `k ∈ [2, n]` of range `y`; if there is none,
`⌈log n⌉ + y`. -/
noncomputable def UniformAlg.guess (A : UniformAlg) (n y : ℕ) : ℕ :=
  if ∃ r, r < Nat.clog 2 n ∧ ∃ k ∈ Icc 2 n, Nat.clog 2 k = y ∧
      threshold n ≤ succProb k (A.p r) then
    sInf {r | r < Nat.clog 2 n ∧ ∃ k ∈ Icc 2 n, Nat.clog 2 k = y ∧
      threshold n ≤ succProb k (A.p r)}
  else Nat.clog 2 n + y

theorem UniformAlg.guess_cases (A : UniformAlg) (n y : ℕ) :
    (A.guess n y < Nat.clog 2 n ∧ ∃ k ∈ Icc 2 n, Nat.clog 2 k = y ∧
      threshold n ≤ succProb k (A.p (A.guess n y))) ∨ A.guess n y = Nat.clog 2 n + y := by
  unfold UniformAlg.guess
  split_ifs with h
  · left
    exact Nat.sInf_mem (s := {r | r < Nat.clog 2 n ∧ ∃ k ∈ Icc 2 n, Nat.clog 2 k = y ∧
      threshold n ≤ succProb k (A.p r)}) h
  · right; rfl

theorem UniformAlg.guess_le_of_good (A : UniformAlg) {n k r : ℕ} (hk : k ∈ Icc 2 n)
    (hr : r < Nat.clog 2 n) (hgood : threshold n ≤ succProb k (A.p r)) :
    A.guess n (Nat.clog 2 k) ≤ r := by
  classical
  have h : ∃ r, r < Nat.clog 2 n ∧ ∃ k' ∈ Icc 2 n, Nat.clog 2 k' = Nat.clog 2 k ∧
      threshold n ≤ succProb k' (A.p r) := ⟨r, hr, k, hk, rfl, hgood⟩
  unfold UniformAlg.guess
  split_ifs
  · exact Nat.sInf_le ⟨hr, k, hk, rfl, hgood⟩

theorem UniformAlg.guess_le (A : UniformAlg) {n k : ℕ} (hk : k ∈ Icc 2 n) :
    A.guess n (Nat.clog 2 k) ≤ 2 * Nat.clog 2 n := by
  classical
  have := Nat.clog_mono_right 2 (mem_Icc.mp hk).2
  rcases A.guess_cases n (Nat.clog 2 k) with h | h <;> omega

/-- **Per-size bound in terms of the guess index**: `E[T_k] ≥ (guess (range k) + 1)/4`. -/
theorem UniformAlg.expTime_ge_guess (A : UniformAlg) {n k : ℕ} (hk : k ∈ Icc 2 n) :
    ENNReal.ofReal ((A.guess n (Nat.clog 2 k) + 1) / 4) ≤ A.expTime k := by
  classical
  have hLε := clog_mul_threshold n
  have hε := threshold_nonneg n
  by_cases hex : ∃ r, r < Nat.clog 2 n ∧ threshold n ≤ succProb k (A.p r)
  · set r₀ := Nat.find hex
    have hr₀ := Nat.find_spec hex
    have hbad : ∀ r < r₀, succProb k (A.p r) < threshold n := by
      intro r hr
      have := Nat.find_min hex hr
      push Not at this
      exact this (hr.trans hr₀.1)
    have hR : (r₀ : ℝ) * threshold n ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hr₀.1.le) hε) hLε
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (A.expTime_ge k r₀ hε hR hbad)
    have : (A.guess n (Nat.clog 2 k) : ℝ) ≤ r₀ := by
      exact_mod_cast A.guess_le_of_good hk hr₀.1 hr₀.2
    linarith
  · push Not at hex
    have hbad : ∀ r < Nat.clog 2 n, succProb k (A.p r) < threshold n := hex
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (A.expTime_ge k _ hε hLε hbad)
    have : (A.guess n (Nat.clog 2 k) : ℝ) ≤ 2 * Nat.clog 2 n := by
      exact_mod_cast A.guess_le hk
    linarith

/-- **Fibers of the guess index are small**: at most `7 + 2 log₂ ⌈log n⌉ = O(log log n)` ranges
share a guess index. -/
theorem UniformAlg.card_fiber_guess_le (A : UniformAlg) {n : ℕ} (hn : 2 ≤ n) (j : ℕ) :
    (((Icc 1 (Nat.clog 2 n)).filter (fun y => A.guess n y = j)).card : ℝ) ≤
      7 + 2 * Real.logb 2 (Nat.clog 2 n) := by
  classical
  set L := Nat.clog 2 n with hLdef
  have hL1 : 1 ≤ L := Nat.clog_pos (by norm_num) (by omega)
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hlogL : 0 ≤ Real.logb 2 (L : ℝ) := Real.logb_nonneg (by norm_num) hL1'
  set F := (Icc 1 L).filter (fun y => A.guess n y = j)
  rcases lt_or_ge j L with hj | hj
  · -- every range of the fiber contains a size for which round `j` is good
    have hwit : ∀ y ∈ F, ∃ k ∈ Icc 2 n, Nat.clog 2 k = y ∧ threshold n ≤ succProb k (A.p j) := by
      intro y hy
      rw [mem_filter] at hy
      rcases A.guess_cases n y with h | h
      · rw [hy.2] at h; exact h.2
      · omega
    have hε : 0 < threshold n := by unfold threshold; positivity
    have key : ∀ y₁ ∈ F, ∀ y₂ ∈ F, (2 : ℝ) ^ y₂ < (64 * (L : ℝ) ^ 2) * 2 ^ y₁ := by
      intro y₁ hy₁ y₂ hy₂
      obtain ⟨k₁, hk₁, rfl, hg₁⟩ := hwit y₁ hy₁
      obtain ⟨k₂, hk₂, rfl, hg₂⟩ := hwit y₂ hy₂
      have hk₁2 := (mem_Icc.mp hk₁).1
      have hk₂2 := (mem_Icc.mp hk₂).1
      have hlo := le_mul_of_good (A.nonneg j) (A.le_one j) hg₁
      have hhi := mul_le_of_good hk₂2 (A.nonneg j) (A.le_one j) hε hg₂
      -- `2^(y₂ - 1) < k₂` and `k₁ ≤ 2^y₁`
      have hpred : (2 : ℝ) ^ (Nat.clog 2 k₂) < 2 * k₂ := by
        have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < k₂ by omega)
        have hpos := Nat.clog_pos (b := 2) (by norm_num) (show 1 < k₂ by omega)
        have : 2 ^ Nat.clog 2 k₂ = 2 * 2 ^ (Nat.clog 2 k₂).pred := by
          rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel hpos]
        have h' : 2 ^ Nat.clog 2 k₂ < 2 * k₂ := by omega
        exact_mod_cast h'
      have hle : (k₁ : ℝ) ≤ 2 ^ (Nat.clog 2 k₁) := by
        exact_mod_cast Nat.le_pow_clog (by norm_num) k₁
      -- `k₂ ε ≤ k₂ k₁ p = k₁ (k₂ p) ≤ k₁ 8/ε`
      have hk₂ : (k₂ : ℝ) ≤ 32 * (L : ℝ) ^ 2 * k₁ := by
        have h1 : (k₂ : ℝ) * threshold n ≤ k₁ * (8 / threshold n) := by
          calc (k₂ : ℝ) * threshold n ≤ k₂ * (k₁ * A.p j) :=
                mul_le_mul_of_nonneg_left hlo (by positivity)
            _ = k₁ * (k₂ * A.p j) := by ring
            _ ≤ k₁ * (8 / threshold n) := mul_le_mul_of_nonneg_left hhi (by positivity)
        have h2 : (k₂ : ℝ) ≤ k₁ * (8 / threshold n) / threshold n := by
          rw [le_div_iff₀ hε]; exact h1
        have h3 : (k₁ : ℝ) * (8 / threshold n) / threshold n = 32 * (L : ℝ) ^ 2 * k₁ := by
          unfold threshold
          rw [← hLdef]
          field_simp
          ring
        linarith
      have hL0 : (0 : ℝ) ≤ 32 * (L : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hle hL0]
    have hM : (1 : ℝ) ≤ 64 * (L : ℝ) ^ 2 := by nlinarith
    have := card_le_logb_add_one F hM key
    have hlog : Real.logb 2 (64 * (L : ℝ) ^ 2) = 6 + 2 * Real.logb 2 L := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
        show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      push_cast; ring
    linarith
  · -- for `j ≥ L` the fiber has at most one element
    have hsub : F ⊆ {j - L} := by
      intro y hy
      rw [mem_filter] at hy
      rw [mem_singleton]
      rcases A.guess_cases n y with h | h <;> omega
    have := card_le_card hsub
    rw [card_singleton] at this
    have : (F.card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith

/-! ### Theorem 2.4 -/

/-- Theorem 2.4 of [Gilbert–Newport–Vaidya–Weaver, PODC 2021], with an explicit constant: for
`n ≥ 4`, every distribution `X` of the number of participants on `{2, …, n}` and every uniform
algorithm `A` without collision detection,
`t_X ≥ 2^H(c(X)) / (88 e · log₂ log₂ n)`. -/
theorem theorem_2_4_explicit {n : ℕ} (hn : 4 ≤ n) (X : ℕ → ℝ)
    (hX0 : ∀ k ∈ Icc 2 n, 0 ≤ X k) (hX1 : ∑ k ∈ Icc 2 n, X k = 1) (A : UniformAlg) :
    ENNReal.ofReal (2 ^ entropyBits X n / (88 * Real.exp 1 * Real.logb 2 (Real.logb 2 n))) ≤
      A.tX X n := by
  classical
  set L := Nat.clog 2 n with hLdef
  set ℓ := Real.logb 2 n with hℓ
  have hL2 : 2 ≤ L := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by omega)
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ2 : 2 ≤ ℓ := by
    rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact hn
  have hℓ' : 1 ≤ Real.logb 2 ℓ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact hℓ2
  -- `L = ⌈log n⌉ ≤ ℓ²`
  have hLℓ : (L : ℝ) ≤ ℓ ^ 2 := by
    have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
    have h' : (2 : ℝ) ^ ((L : ℝ) - 1) < n := by
      have : ((L : ℝ) - 1) = ((L - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, Real.rpow_natCast]
      exact_mod_cast h
    have := (Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith)).mpr h'
    nlinarith
  -- the fiber bound `K` is `O(log log n)`
  set K : ℝ := 7 + 2 * Real.logb 2 L with hK
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hlogL : 0 ≤ Real.logb 2 (L : ℝ) := Real.logb_nonneg (by norm_num) hL1'
  have hKpos : 0 < K := by linarith
  have hKle : K ≤ 11 * Real.logb 2 ℓ := by
    have : Real.logb 2 (L : ℝ) ≤ Real.logb 2 (ℓ ^ 2) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hLℓ
    rw [Real.logb_pow] at this
    push_cast at this
    linarith
  -- the condensed distribution
  set q : ℕ → ℝ := condensed X n with hq
  have hmaps : ∀ k ∈ Icc 2 n, Nat.clog 2 k ∈ Icc 1 L := by
    intro k hk
    rw [mem_Icc] at hk ⊢
    exact ⟨Nat.clog_pos (by norm_num) (by omega), Nat.clog_mono_right 2 hk.2⟩
  have hq0 : ∀ y ∈ Icc 1 L, 0 ≤ q y := fun y _ =>
    sum_nonneg fun k hk => hX0 k (mem_filter.mp hk).1
  have hq1 : ∑ y ∈ Icc 1 L, q y = 1 := by
    rw [← hX1]; exact sum_fiberwise_of_maps_to hmaps X
  set g : ℕ → ℕ := A.guess n with hg
  set μ := ∑ y ∈ Icc 1 L, q y * (g y + 1) with hμ
  have hμk : μ = ∑ k ∈ Icc 2 n, X k * (g (Nat.clog 2 k) + 1) := by
    rw [hμ, ← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun y _ => ?_
    rw [hq, condensed, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    rw [(mem_filter.mp hk).2]
  have hμ1 : 1 ≤ μ := by
    have : ∑ y ∈ Icc 1 L, q y * 1 ≤ μ :=
      sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (by simp) (hq0 y hy)
    simpa [hq1] using this
  -- guesswork lemma
  have hgibbs := sum_negMulLog_le_of_card_fiber_le (Icc 1 L) q hq0 hq1 g hKpos
    (fun j => A.card_fiber_guess_le (by omega) j)
  rw [← hμ] at hgibbs
  have hH : (2 : ℝ) ^ entropyBits X n ≤ K * (μ + 1) * Real.exp 1 := by
    have h2 : (2 : ℝ) ^ entropyBits X n = Real.exp (∑ y ∈ Icc 1 L, Real.negMulLog (q y)) := by
      rw [Real.rpow_def_of_pos (by norm_num), entropyBits, ← sum_div, ← hLdef]
      rw [hq]
      congr 1
      field_simp
    rw [h2]
    calc Real.exp (∑ y ∈ Icc 1 L, Real.negMulLog (q y))
        ≤ Real.exp (Real.log K + Real.log (μ + 1) + 1) := Real.exp_le_exp.mpr hgibbs
      _ = K * (μ + 1) * Real.exp 1 := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hKpos, Real.exp_log (by linarith)]
  -- `t_X ≥ μ / 4`
  have htX : ENNReal.ofReal (μ / 4) ≤ A.tX X n := by
    have : μ / 4 = ∑ k ∈ Icc 2 n, X k * ((g (Nat.clog 2 k) + 1) / 4) := by
      rw [hμk, sum_div]; exact sum_congr rfl fun k _ => by ring
    rw [this, ENNReal.ofReal_sum_of_nonneg
      (fun k hk => mul_nonneg (hX0 k hk) (by positivity)), UniformAlg.tX]
    refine sum_le_sum fun k hk => ?_
    rw [ENNReal.ofReal_mul (hX0 k hk)]
    exact mul_le_mul_right (A.expTime_ge_guess hk) _
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) htX
  have hll : 0 < Real.logb 2 ℓ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  calc (2 : ℝ) ^ entropyBits X n ≤ K * (μ + 1) * Real.exp 1 := hH
    _ ≤ (11 * Real.logb 2 ℓ) * (2 * μ) * Real.exp 1 := by gcongr; linarith
    _ = μ / 4 * (88 * Real.exp 1 * Real.logb 2 ℓ) := by ring

/-- **Theorem 2.4** of [Gilbert–Newport–Vaidya–Weaver, PODC 2021]: for uniform contention
resolution algorithms without collision detection, `t_X(n) = Ω(2^H(c(X)) / log log n)`. There is a
universal constant `C > 0` such that for every `n ≥ 4`, every distribution `X` of the number of
participants on `{2, …, n}` and every uniform algorithm `A`, the expected running time satisfies
`t_X ≥ C · 2^H(c(X)) / log₂ log₂ n`. -/
theorem theorem_2_4 : ∃ C > (0 : ℝ), ∀ n : ℕ, 4 ≤ n → ∀ X : ℕ → ℝ,
    (∀ k ∈ Icc 2 n, 0 ≤ X k) → ∑ k ∈ Icc 2 n, X k = 1 → ∀ A : UniformAlg,
    ENNReal.ofReal (C * 2 ^ entropyBits X n / Real.logb 2 (Real.logb 2 n)) ≤ A.tX X n := by
  refine ⟨1 / (88 * Real.exp 1), by positivity, fun n hn X hX0 hX1 A => ?_⟩
  convert theorem_2_4_explicit hn X hX0 hX1 A using 2
  field_simp

end Podc.ContentionPredictions
