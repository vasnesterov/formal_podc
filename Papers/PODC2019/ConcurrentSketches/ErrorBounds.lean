import Mathlib

/-!
# Fast Concurrent Data Sketches (PODC 2019): error bounds of relaxed sketches

The deterministic / algebraic parts of the error analysis of Section 6 of the PODC version
("Deriving error bounds"; Section 7 of the full version: Claim 1, Lemma 9, eqs. (3)–(4),
Claims 2–6 and Lemma 10).

## Quantiles (Section 6.2; Lemma 10 of the full version)

The adversary hides `i` stream elements below the `φ`-quantile and `j` above it, `m = i + j ≤ r`.
The sequential PAC sketch run on the remaining `n - m` elements returns an element of rank `ρ`
among them with `(φ - ε)(n - m) ≤ ρ ≤ (φ + ε)(n - m)`; its rank in the original stream is `ρ + h`,
`0 ≤ h ≤ m` (the paper has `h = i`).

* `quantile_relaxed_rank`: then `(φ - ε_r) n ≤ ρ + h ≤ (φ + ε_r) n` with
  `ε_r = ε - r ε / n + r / n` (`relaxedEps`), for `0 ≤ φ ≤ 1` and **`ε ≤ 1`** (the full version
  assumes `ε < 1/2` and goes through Claims 2–6; the direct computation needs only `ε ≤ 1`).
* `quantile_relaxed_rank_paper`: the paper's form (`h = i`, `m = i + j`).
* `quantile_relaxed_rank_fails`: for `ε > 1` the implication (as stated, with ranks only constrained
  by the PAC interval) fails: `φ = 1/2, ε = 2, n = 10, r = 1, m = h = 0, ρ = 25`.
  This is degenerate: `quantile_relaxed_rank_of_rank_le` shows the claim holds for every `ε`
  once ranks are genuine ranks (`0 ≤ ρ ≤ n - m`) and `r ≤ n`.
* `quantile_relaxed_prob`: the probabilistic form (`≥ 1 - δ` transfers by monotonicity of
  the measure).

## Θ sketch (Section 6.1; Section 7.1 of the full version)

* `abs_div_sub_le_max` (Claim 1): for `c > 0` and `0 < a ≤ x ≤ b`,
  `|c/x - n| ≤ max |c/a - n| |c/b - n|`, i.e. the largest error is obtained for `j = 0` or `j = r`;
  `abs_est_sub_le_max` is the order-statistic form.
* `sqrt_expect_sq_sub_le` (Lemma 9): `√E[(e-n)²]/n ≤ √Var[e]/n + |E[e] - n|/n` for a real random
  variable `e ∈ L²` on a probability space (proved in full, via
  `E[(e-n)²] = Var[e] + (E[e]-n)²`, `expect_sq_sub_eq`).
* Weak adversary: `weakE k r n = n (k-1)/(k+r-1)` and
  `weakE2 k r n = (k-1)² n (n-1)/((k+r-1)(k+r-2))` are the order-statistic values of
  `E[(k-1)/M_(k+r)]` and `E[((k-1)/M_(k+r))²]` for the `(k+r)`-th smallest of `n` i.i.d. uniform
  `[0,1]` variables. **These moments are not proved here**: in `rse_weak_lt` they are hypotheses
  on the random variable `e`. Proved: `weakVar_nonneg`, `weakVar_lt` (`σ² < n²/(k+r-2)`),
  `sqrt_weakVar_div_weakE_lt` (eq. (3)), `weak_rse_bound_lt` (eq. (4)),
  `weak_rse_bound_le_two` (`≤ 2/√(k-2)` when `r ≤ √(k-2)`), `rse_weak_lt` (Lemma 9 + eq. (4)),
  and `weakError_monotone` (the expected error `n - n (k-1)/(k+j-1)` is non-decreasing in `j`).
-/

namespace Podc.ConcurrentSketches

open Real MeasureTheory ProbabilityTheory

/-! ## Quantiles sketch -/

/-- The relaxed error parameter `ε_r = ε - r ε / n + r / n` of Section 6.2. -/
noncomputable def relaxedEps (ε r n : ℝ) : ℝ := ε - r * ε / n + r / n

lemma relaxedEps_mul {ε r n : ℝ} (hn : n ≠ 0) : relaxedEps ε r n * n = ε * n - r * ε + r := by
  unfold relaxedEps; field_simp

/-- Section 6.2 of the PODC version / Lemma 10 of the full version (deterministic core, general
form). If the sequential sketch, run on the `n - m` elements not hidden by the adversary
(`0 ≤ m ≤ r`), returns an element of rank `ρ ∈ [(φ-ε)(n-m), (φ+ε)(n-m)]` among them, and `h ∈ [0, m]`
hidden elements lie below it, then its rank `ρ + h` in the whole stream lies in
`[(φ - ε_r) n, (φ + ε_r) n]`. Only `ε ≤ 1` is needed (the full version assumes `ε < 1/2`). -/
theorem quantile_relaxed_rank {φ ε n r m ρ h : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hε : ε ≤ 1)
    (hn : 0 < n) (hm0 : 0 ≤ m) (hmr : m ≤ r) (hh0 : 0 ≤ h) (hhm : h ≤ m)
    (hlo : (φ - ε) * (n - m) ≤ ρ) (hhi : ρ ≤ (φ + ε) * (n - m)) :
    (φ - relaxedEps ε r n) * n ≤ ρ + h ∧ ρ + h ≤ (φ + relaxedEps ε r n) * n := by
  have he := relaxedEps_mul (ε := ε) (r := r) hn.ne'
  constructor
  · have : (φ - relaxedEps ε r n) * n = φ * n - ε * n + r * ε - r := by
      rw [sub_mul, he]; ring
    rw [this]
    rcases le_total 0 (φ - ε) with h1 | h1
    · nlinarith [mul_le_mul_of_nonneg_left hmr (sub_nonneg.2 hε),
        mul_le_mul_of_nonneg_left (show φ - ε ≤ 1 - ε by linarith) hm0]
    · nlinarith [mul_nonneg (sub_nonneg.2 hε) (hm0.trans hmr), mul_nonpos_of_nonneg_of_nonpos hm0 h1]
  · have : (φ + relaxedEps ε r n) * n = φ * n + ε * n - r * ε + r := by
      rw [add_mul, he]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hmr (sub_nonneg.2 hε), mul_nonneg hm0 hφ0]

/-- Section 6.2 of the PODC version / Lemma 10 of the full version, in the paper's form: the
adversary hides `i ≥ 0` elements below the `φ`-quantile and `j ≥ 0` above it, `i + j ≤ r`; the
rank `ρ` among the remaining `n - (i + j)` elements is within `(φ ± ε)(n - (i + j))`; then the rank
`ρ + i` in the original stream is within `(φ ± ε_r) n` (eq. (1) of the PODC version). -/
theorem quantile_relaxed_rank_paper {φ ε n r i j ρ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hε : ε ≤ 1)
    (hn : 0 < n) (hi : 0 ≤ i) (hj : 0 ≤ j) (hijr : i + j ≤ r)
    (hlo : (φ - ε) * (n - (i + j)) ≤ ρ) (hhi : ρ ≤ (φ + ε) * (n - (i + j))) :
    (φ - relaxedEps ε r n) * n ≤ ρ + i ∧ ρ + i ≤ (φ + relaxedEps ε r n) * n :=
  quantile_relaxed_rank hφ0 hφ1 hε hn (by linarith) hijr hi (by linarith) hlo hhi

/-- For `ε > 1` the claim of Section 6.2 (as an implication from the PAC interval) fails:
`φ = 1/2`, `ε = 2`, `n = 10`, `r = 1`, nothing hidden (`m = h = 0`) and `ρ = (φ + ε) n = 25`;
then `ε_r = 1.9` and `(φ + ε_r) n = 24 < 25`. (Degenerate: `ρ > n`, see
`quantile_relaxed_rank_of_rank_le`.) -/
theorem quantile_relaxed_rank_fails :
    let φ : ℝ := 1 / 2; let ε : ℝ := 2; let n : ℝ := 10; let r : ℝ := 1
    let m : ℝ := 0; let h : ℝ := 0; let ρ : ℝ := 25
    (0 ≤ φ ∧ φ ≤ 1 ∧ 0 < n ∧ 0 ≤ m ∧ m ≤ r ∧ 0 ≤ h ∧ h ≤ m ∧
      (φ - ε) * (n - m) ≤ ρ ∧ ρ ≤ (φ + ε) * (n - m)) ∧
    ¬ (ρ + h ≤ (φ + relaxedEps ε r n) * n) := by
  simp only [relaxedEps]; norm_num

/-- The degenerate case `ε > 1` disappears once ranks are genuine ranks (`0 ≤ ρ ≤ n - m`) and
`r ≤ n`: then the conclusion of Section 6.2 holds for every `ε`. -/
theorem quantile_relaxed_rank_of_rank_le {φ ε n r m ρ h : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hn : 0 < n) (hm0 : 0 ≤ m) (hmr : m ≤ r) (hrn : r ≤ n) (hh0 : 0 ≤ h) (hhm : h ≤ m)
    (hρ0 : 0 ≤ ρ) (hρn : ρ ≤ n - m)
    (hlo : (φ - ε) * (n - m) ≤ ρ) (hhi : ρ ≤ (φ + ε) * (n - m)) :
    (φ - relaxedEps ε r n) * n ≤ ρ + h ∧ ρ + h ≤ (φ + relaxedEps ε r n) * n := by
  rcases le_or_gt ε 1 with hε | hε
  · exact quantile_relaxed_rank hφ0 hφ1 hε hn hm0 hmr hh0 hhm hlo hhi
  · have he := relaxedEps_mul (ε := ε) (r := r) hn.ne'
    have h1 : n ≤ relaxedEps ε r n * n := by
      rw [he]; nlinarith [mul_le_mul_of_nonneg_left hrn (sub_nonneg.2 hε.le)]
    constructor <;> nlinarith

/-- Section 6.2 of the PODC version / Lemma 10 of the full version, probabilistic form: if the
sequential guarantee holds with probability at least `1 - δ` and `h ∈ [0, m]` always, then the
relaxed guarantee holds with probability at least `1 - δ`. -/
theorem quantile_relaxed_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ρ h : Ω → ℝ)
    {φ ε n r m : ℝ} {δ : ENNReal} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hε : ε ≤ 1) (hn : 0 < n)
    (hm0 : 0 ≤ m) (hmr : m ≤ r) (hh : ∀ ω, 0 ≤ h ω ∧ h ω ≤ m)
    (hseq : 1 - δ ≤ μ {ω | (φ - ε) * (n - m) ≤ ρ ω ∧ ρ ω ≤ (φ + ε) * (n - m)}) :
    1 - δ ≤ μ {ω | (φ - relaxedEps ε r n) * n ≤ ρ ω + h ω ∧
      ρ ω + h ω ≤ (φ + relaxedEps ε r n) * n} :=
  hseq.trans <| measure_mono fun ω hω =>
    quantile_relaxed_rank hφ0 hφ1 hε hn hm0 hmr (hh ω).1 (hh ω).2 hω.1 hω.2

/-! ## Θ sketch: Claim 1 -/

/-- Claim 1 of the full version (Section 6.1 of the PODC version: "the largest error is always
obtained either for `j = 0` or for `j = r`"): for `c > 0` and `0 < a ≤ x ≤ b`,
`|c/x - n| ≤ max |c/a - n| |c/b - n|`. -/
theorem abs_div_sub_le_max {c a b x n : ℝ} (hc : 0 < c) (ha : 0 < a) (hax : a ≤ x)
    (hxb : x ≤ b) : |c / x - n| ≤ max |c / a - n| |c / b - n| := by
  have h1 : c / x ≤ c / a := div_le_div_of_nonneg_left hc.le ha hax
  have h2 : c / b ≤ c / x := div_le_div_of_nonneg_left hc.le (ha.trans_le hax) hxb
  rcases le_total n (c / x) with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact le_max_of_le_left ((sub_le_sub_right h1 n).trans (le_abs_self _))
  · rw [abs_of_nonpos (sub_nonpos.2 h)]
    refine le_max_of_le_right ?_
    calc -(c / x - n) = n - c / x := by ring
      _ ≤ n - c / b := by linarith
      _ ≤ |c / b - n| := by rw [abs_sub_comm]; exact le_abs_self _

/-- Claim 1, order-statistic form: if `M` is non-decreasing with `M k > 0` (the order statistics
`M_(i)`), then for every `j ≤ r` the error `|(k-1)/M_(k+j) - n|` is at most the larger of the
errors for `j = 0` and `j = r`. -/
theorem abs_est_sub_le_max {M : ℕ → ℝ} (hM : Monotone M) {k r j : ℕ} (hk : 1 < k)
    (hpos : 0 < M k) (hj : j ≤ r) (n : ℝ) :
    |(k - 1 : ℝ) / M (k + j) - n| ≤
      max |(k - 1 : ℝ) / M k - n| |(k - 1 : ℝ) / M (k + r) - n| := by
  have hk' : (0 : ℝ) < k - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  exact abs_div_sub_le_max hk' hpos (hM (Nat.le_add_right k j)) (hM (by omega))

/-! ## Lemma 9: RSE around `n` versus standard deviation and bias -/

/-- Mean squared error decomposition used in Lemma 9 of the full version:
`E[(e - n)²] = Var[e] + (E[e] - n)²`. -/
theorem expect_sq_sub_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e : Ω → ℝ} (he : MemLp e 2 μ) (n : ℝ) :
    μ[fun ω => (e ω - n) ^ 2] = Var[e; μ] + (μ[e] - n) ^ 2 := by
  have hsub : MemLp (fun ω => e ω - n) 2 μ := he.sub (memLp_const n)
  have h1 := variance_eq_sub hsub
  rw [variance_sub_const he.aestronglyMeasurable] at h1
  have h2 : μ[fun ω => e ω - n] = μ[e] - n := by
    rw [integral_sub (he.integrable one_le_two) (integrable_const n)]
    simp
  rw [h1, h2]
  have h3 : ((fun ω => e ω - n) ^ 2) = fun ω => (e ω - n) ^ 2 := rfl
  rw [h3]; ring

/-- Lemma 9 of the full version (Section 6.1 of the PODC version): the relative standard error
around the true value `n`, `RSE[e] = √E[(e-n)²] / n`, is at most `√Var[e]/n + |E[e] - n|/n`. -/
theorem sqrt_expect_sq_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {e : Ω → ℝ} (he : MemLp e 2 μ) {n : ℝ} (hn : 0 < n) :
    √(μ[fun ω => (e ω - n) ^ 2]) / n ≤ √(Var[e; μ]) / n + |μ[e] - n| / n := by
  rw [expect_sq_sub_eq he, ← add_div]
  gcongr
  have hv := variance_nonneg e μ
  rw [sqrt_le_left (by positivity)]
  nlinarith [sq_sqrt hv, sq_abs (μ[e] - n), sqrt_nonneg (Var[e; μ]), abs_nonneg (μ[e] - n),
    mul_nonneg (sqrt_nonneg (Var[e; μ])) (abs_nonneg (μ[e] - n))]

/-! ## Θ sketch: the weak adversary -/

/-- `E[(k-1)/M_(k+r)] = n (k-1)/(k+r-1)`: expected estimate under the weak adversary (order
statistics of `n` i.i.d. uniforms; the formula is taken as given, not proved). -/
noncomputable def weakE (k r : ℕ) (n : ℝ) : ℝ := n * (k - 1) / (k + r - 1)

/-- `E[((k-1)/M_(k+r))²] = (k-1)² n (n-1) / ((k+r-1)(k+r-2))` (order statistics; taken as
given, not proved). -/
noncomputable def weakE2 (k r : ℕ) (n : ℝ) : ℝ :=
  (k - 1) ^ 2 * n * (n - 1) / ((k + r - 1) * (k + r - 2))

/-- The variance `σ²[e_Aw] = E[e_Aw²] - E[e_Aw]²` of the weak adversary's estimate. -/
noncomputable def weakVar (k r : ℕ) (n : ℝ) : ℝ := weakE2 k r n - weakE k r n ^ 2

lemma weakVar_eq {k r : ℕ} (hk : 3 ≤ k) (n : ℝ) :
    weakVar k r n =
      (k - 1) ^ 2 * n * (n - (k + r) + 1) / ((k + r - 1) ^ 2 * (k + r - 2)) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have h1 : (k + r - 1 : ℝ) ≠ 0 := by linarith
  have h2 : (k + r - 2 : ℝ) ≠ 0 := by linarith
  unfold weakVar weakE2 weakE
  field_simp
  ring

/-- The variance of the weak adversary's estimate is non-negative (for `n ≥ k + r - 1`). -/
theorem weakVar_nonneg {k r : ℕ} (hk : 3 ≤ k) {n : ℝ} (hn : (k + r : ℝ) - 1 ≤ n) :
    0 ≤ weakVar k r n := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  rw [weakVar_eq hk]
  apply div_nonneg
  · apply mul_nonneg (mul_nonneg (by positivity) (by linarith)); linarith
  · apply mul_nonneg (by positivity); linarith

/-- Section 7.1 of the full version: `σ²[e_Aw] < n² / (k + r - 2)`. -/
theorem weakVar_lt {k r : ℕ} (hk : 3 ≤ k) {n : ℝ} (hn : 0 < n) :
    weakVar k r n < n ^ 2 / (k + r - 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  rw [weakVar_eq hk, div_lt_div_iff₀ (by apply mul_pos (pow_pos (by linarith) 2); linarith)
    (by linarith)]
  have ha : (0 : ℝ) < k + r - 2 := by linarith
  have hb : (k - 1 : ℝ) ^ 2 ≤ (k + r - 1) ^ 2 := by
    apply pow_le_pow_left₀ <;> linarith
  have hc : (k - 1 : ℝ) ^ 2 * n * (n - (k + r) + 1) < (k - 1) ^ 2 * n * n := by
    exact mul_lt_mul_of_pos_left (by linarith) (mul_pos (pow_pos (by linarith) 2) hn)
  calc (k - 1 : ℝ) ^ 2 * n * (n - (k + r) + 1) * (k + r - 2)
      < (k - 1) ^ 2 * n * n * (k + r - 2) := mul_lt_mul_of_pos_right hc ha
    _ ≤ n ^ 2 * ((k + r - 1) ^ 2 * (k + r - 2)) := by
      have := mul_le_mul_of_nonneg_right hb (mul_nonneg (sq_nonneg n) ha.le)
      nlinarith [this]

/-- Eq. (3) of the full version: `√σ²[e_Aw] / E[e_Aw] < 1/√(k-2)` (for `n > k + r`). -/
theorem sqrt_weakVar_div_weakE_lt {k r : ℕ} (hk : 3 ≤ k) {n : ℝ} (hn : (k + r : ℝ) < n) :
    √(weakVar k r n) / weakE k r n < 1 / √(k - 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have hn0 : 0 < n := by linarith
  have hE : 0 < weakE k r n := by
    unfold weakE; apply div_pos (mul_pos hn0 (by linarith)); linarith
  have hk2 : (0 : ℝ) < k - 2 := by linarith
  have hsk : 0 < √((k : ℝ) - 2) := sqrt_pos.2 hk2
  rw [div_lt_div_iff₀ hE hsk, one_mul, ← sqrt_mul (weakVar_nonneg hk (by linarith)),
    sqrt_lt' hE]
  -- `weakVar = weakE² (n - (k+r) + 1) / (n (k+r-2))`
  have hV : weakVar k r n =
      weakE k r n ^ 2 * (n - (k + r) + 1) / (n * (k + r - 2)) := by
    rw [weakVar_eq hk]; unfold weakE
    have h1 : (k + r - 1 : ℝ) ≠ 0 := by linarith
    have h2 : (k + r - 2 : ℝ) ≠ 0 := by linarith
    field_simp
  rw [hV, div_mul_eq_mul_div, div_lt_iff₀ (by apply mul_pos hn0; linarith)]
  have hE2 : 0 < weakE k r n ^ 2 := by positivity
  have : (n - (k + r) + 1) * (k - 2) < n * (k + r - 2) := by nlinarith
  calc weakE k r n ^ 2 * (n - (k + r) + 1) * (k - 2)
      = weakE k r n ^ 2 * ((n - (k + r) + 1) * (k - 2)) := by ring
    _ < weakE k r n ^ 2 * (n * (k + r - 2)) := mul_lt_mul_of_pos_left this hE2

/-- Eq. (4) of the full version (Section 6.1 of the PODC version): the RSE bound of Lemma 9 for
the weak adversary, `√σ²[e_Aw]/n + |E[e_Aw] - n|/n < 1/√(k-2) + r/(k-2)`. -/
theorem weak_rse_bound_lt {k r : ℕ} (hk : 3 ≤ k) {n : ℝ} (hn : (k + r : ℝ) < n) :
    √(weakVar k r n) / n + |weakE k r n - n| / n < 1 / √(k - 2) + r / (k - 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have hn0 : 0 < n := by linarith
  have hE : 0 < weakE k r n := by
    unfold weakE; apply div_pos (mul_pos hn0 (by linarith)); linarith
  have hEn : weakE k r n ≤ n := by
    unfold weakE; rw [div_le_iff₀ (by linarith)]; nlinarith
  have h1 : √(weakVar k r n) / n < 1 / √(k - 2) :=
    (div_le_div_of_nonneg_left (sqrt_nonneg _) hE hEn).trans_lt (sqrt_weakVar_div_weakE_lt hk hn)
  have h2 : |weakE k r n - n| / n ≤ r / (k - 2) := by
    rw [abs_of_nonpos (by linarith), neg_sub]
    have : (n - weakE k r n) / n = r / (k + r - 1) := by
      unfold weakE
      have : (k + r - 1 : ℝ) ≠ 0 := by linarith
      field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_left hr (by linarith) (by linarith)
  linarith

/-- Section 6.1 of the PODC version: "whenever `r` is at most `√(k-2)`, the RSE of the relaxed Θ
sketch is coarsely bounded by twice that of the sequential one": `1/√(k-2) + r/(k-2) ≤ 2/√(k-2)`. -/
theorem weak_rse_bound_le_two {k r : ℕ} (hk : 3 ≤ k) (hr : (r : ℝ) ≤ √(k - 2)) :
    1 / √(k - 2) + r / (k - 2) ≤ 2 / √(k - 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < k - 2 := by linarith
  have hs : 0 < √((k : ℝ) - 2) := sqrt_pos.2 hk2
  have : (r : ℝ) / (k - 2) ≤ 1 / √(k - 2) :=
    calc (r : ℝ) / (k - 2) ≤ √(k - 2) / (k - 2) := by gcongr
      _ = 1 / √(k - 2) := by
        rw [div_eq_div_iff hk2.ne' hs.ne', one_mul, mul_self_sqrt hk2.le]
  calc 1 / √(k - 2) + r / (k - 2) ≤ 1 / √(k - 2) + 1 / √(k - 2) := by gcongr
    _ = 2 / √(k - 2) := by ring

/-- Section 6.1 of the PODC version / eq. (4) of the full version, combined with Lemma 9: if the
weak adversary's estimate `e ∈ L²` has the order-statistic moments `E[e] = weakE k r n` and
`E[e²] = weakE2 k r n` (hypotheses), then `RSE[e] = √E[(e-n)²]/n < 1/√(k-2) + r/(k-2)`. -/
theorem rse_weak_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {e : Ω → ℝ} (he : MemLp e 2 μ) {k r : ℕ} (hk : 3 ≤ k) {n : ℝ} (hn : (k + r : ℝ) < n)
    (hE : μ[e] = weakE k r n) (hE2 : μ[e ^ 2] = weakE2 k r n) :
    √(μ[fun ω => (e ω - n) ^ 2]) / n < 1 / √(k - 2) + r / (k - 2) := by
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ k + r := by positivity
    linarith
  have hV : Var[e; μ] = weakVar k r n := by rw [variance_eq_sub he, hE, hE2]; rfl
  have := sqrt_expect_sq_sub_le he hn0
  rw [hV, hE] at this
  exact this.trans_lt (weak_rse_bound_lt hk hn)

/-- Section 6.1 of the PODC version (weak adversary): the expected error
`E[n - est(M_(k+j))] = n - n (k-1)/(k+j-1)` is non-decreasing in the number `j` of hidden
elements, hence "maximised for `j = r`". -/
theorem weakError_monotone {k : ℕ} (hk : 2 ≤ k) {n : ℝ} (hn : 0 ≤ n) :
    Monotone fun j : ℕ => n - n * (k - 1) / (k + j - 1) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  intro a b hab
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha : (0 : ℝ) ≤ a := a.cast_nonneg
  simp only [sub_le_sub_iff_left]
  exact div_le_div_of_nonneg_left (mul_nonneg hn (by linarith)) (by linarith) (by linarith)

end Podc.ConcurrentSketches
