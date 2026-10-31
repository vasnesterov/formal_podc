import Mathlib

/-!
# The parameters of `Sampler` (Sections 3–4)

Arithmetic facts behind Lemmas 4.1–4.3, 4.7 and Theorem 5.1, with `δ = 1/(2^{k+1} − 1)`, `ε = 1/h`,
`p_j = n^{−2^j δ}`:

* `sum_two_pow_mul`: `p̂_{j−1} = ∏_{i<j} p_i = n^{−(2^j − 1)δ}` (exponent identity).
* `one_sub_mul_delta`: `1 − (2^k − 1)δ = 2^k δ`, used for `n_k ≤ 3 n^{2^k δ}/2` in Lemma 4.3.
* `size_exponent`: `n_j · s_j ≈ n^{1 − (2^j − 1)δ} · n^{2^j δ + ε} = n^{1 + δ + ε}` — the true per-level
  edge count (Theorem 5.1's message count, and the corrected Lemma 4.7).
* `lemma_4_2_bound`: `(1 − p)^m ≤ n^{−c}` when `p m ≥ c ln n` (Lemma 4.2).
* `lemma_4_3_parameters`: with `L = 2h`, `b = n^{1/h}`, `α = 3c n^a ln² n / h`, `τ = c n^a ln n` and
  `s ≥ c² n^{a+1/h} ln³ n` (`a = 2^j δ`), the hypotheses of `Setup.lemma_4_3_node` hold
  (`b^L = n²`, `τ ≤ α/3`, `α ≥ 6`) and `(1 − 1/(L α b))^s ≤ n^{−c/6}`.
-/

namespace Podc.LocalMessageReduction

open Real

lemma sum_two_pow_mul (δ : ℝ) (j : ℕ) : ∑ i ∈ Finset.range j, (2 : ℝ) ^ i * δ = (2 ^ j - 1) * δ := by
  rw [← Finset.sum_mul]
  congr 1
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- `p̂_{j−1} = ∏_{i<j} n^{−2^i δ} = n^{−(2^j−1)δ}` (Section 4, before Lemma 4.1). -/
lemma prod_p (n δ : ℝ) (hn : 0 < n) (j : ℕ) :
    ∏ i ∈ Finset.range j, n ^ (-((2 : ℝ) ^ i * δ)) = n ^ (-((2 ^ j - 1) * δ)) := by
  rw [← sum_two_pow_mul, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hn]

/-- `1 − (2^k − 1)δ = 2^k δ` for `δ = 1/(2^{k+1} − 1)`. -/
lemma one_sub_mul_delta (k : ℕ) :
    1 - (2 ^ k - 1) * (1 / (2 ^ (k + 1) - 1) : ℝ) = 2 ^ k * (1 / (2 ^ (k + 1) - 1)) := by
  have h : (2 : ℝ) ^ (k + 1) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  field_simp
  rw [pow_succ]
  ring

/-- `n^{1 − (2^j − 1)δ} · n^{2^j δ + ε} = n^{1 + δ + ε}`: the number of level-`j` nodes times the
samples per node and trial. -/
lemma size_exponent (n δ ε : ℝ) (hn : 0 < n) (j : ℕ) :
    n ^ (1 - (2 ^ j - 1) * δ) * n ^ (2 ^ j * δ + ε) = n ^ (1 + δ + ε) := by
  rw [← rpow_add hn]
  ring_nf

/-- **Lemma 4.2 (bound).** `(1 − p)^m ≤ n^{−c}` if `p ≤ 1` and `p m ≥ c ln n`. -/
lemma lemma_4_2_bound {n p c : ℝ} (hn : 0 < n) (hp1 : p ≤ 1) {m : ℕ}
    (hm : c * log n ≤ p * m) : (1 - p) ^ m ≤ n ^ (-c) := by
  calc (1 - p) ^ m ≤ (exp (-p)) ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-p)]) m
    _ = exp (-(p * m)) := by rw [← exp_nat_mul]; ring_nf
    _ ≤ exp (-(c * log n)) := exp_le_exp.mpr (by linarith)
    _ = n ^ (-c) := by rw [rpow_def_of_pos hn]; ring_nf

/-- **The parameters of Lemma 4.3.** For `n > 1`, `1 ≤ h ≤ ln n`, `c ≥ 2`, `a ≥ 0` (`a = 2^j δ`), with
`L = 2h`, `b = n^{1/h}`, `α = 3c n^a ln² n / h`, `τ = c n^a ln n` and `s ≥ c² n^{a + 1/h} ln³ n`:
`b^L = n²`, `τ ≤ α / 3`, `6 ≤ α` (as `c ln n ≥ 2`), and `(1 − 1/(L α b))^s ≤ n^{−c/6}`. -/
lemma lemma_4_3_parameters {n c h a : ℝ} {s : ℕ} (hn : 1 < n) (hh : 1 ≤ h) (hhn : h ≤ log n)
    (hc : 0 < c) (hcl : 2 ≤ c * log n) (ha : 0 ≤ a) (hs : c ^ 2 * n ^ (a + 1 / h) * log n ^ 3 ≤ s) :
    (n ^ (1 / h)) ^ (2 * h) = n ^ (2 : ℝ) ∧
    c * n ^ a * log n ≤ (3 * c * n ^ a * log n ^ 2 / h) / 3 ∧
    6 ≤ 3 * c * n ^ a * log n ^ 2 / h ∧
    (1 - 1 / (2 * h * (3 * c * n ^ a * log n ^ 2 / h) * n ^ (1 / h))) ^ s ≤ n ^ (-(c / 6)) := by
  have hn0 : 0 < n := by linarith
  have hlog : 0 < log n := log_pos hn
  have hh0 : 0 < h := by linarith
  have hna : 1 ≤ n ^ a := one_le_rpow hn.le ha
  have hnh : 0 < n ^ (1 / h) := rpow_pos_of_pos hn0 _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← rpow_mul hn0.le]; congr 1; field_simp
  · rw [div_div, le_div_iff₀ (by positivity)]
    have : c * n ^ a * log n * h ≤ c * n ^ a * log n * log n :=
      mul_le_mul_of_nonneg_left hhn (by positivity)
    nlinarith
  · rw [le_div_iff₀ hh0]
    have h1 : c * log n * h ≤ c * log n * log n := mul_le_mul_of_nonneg_left hhn (by positivity)
    have h2 : 0 ≤ c * log n * log n * (n ^ a - 1) := by
      have := sub_nonneg.mpr hna; positivity
    nlinarith
  · -- `L α b = 6 c n^{a+1/h} ln² n`, so `θ s ≥ c ln n / 6`
    have hLab : 2 * h * (3 * c * n ^ a * log n ^ 2 / h) * n ^ (1 / h) =
        6 * c * n ^ (a + 1 / h) * log n ^ 2 := by
      rw [rpow_add hn0]; field_simp; ring
    rw [hLab]
    set θ := 1 / (6 * c * n ^ (a + 1 / h) * log n ^ 2)
    have hpos : 0 < 6 * c * n ^ (a + 1 / h) * log n ^ 2 := by positivity
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by
      have h1 : (1 : ℝ) ≤ n ^ (a + 1 / h) := one_le_rpow hn.le (by positivity)
      have h2 : (1 : ℝ) ≤ log n := hh.trans hhn
      have h3 : (1 : ℝ) ≤ 6 * c * n ^ (a + 1 / h) * log n ^ 2 := by
        have : 6 * c * n ^ (a + 1 / h) * log n ^ 2 = 6 * (c * log n) * n ^ (a + 1 / h) * log n := by
          ring
        rw [this]
        have h4 : (1 : ℝ) ≤ 6 * (c * log n) := by linarith
        exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h4 h1) h2
      exact div_le_one_of_le₀ h3 hpos.le
    apply lemma_4_2_bound hn0 hθ1
    -- `c/6 · ln n ≤ θ s`
    have : c / 6 * log n * (6 * c * n ^ (a + 1 / h) * log n ^ 2) ≤ s := by
      nlinarith [hs]
    rw [show θ * s = s / (6 * c * n ^ (a + 1 / h) * log n ^ 2) by ring, le_div_iff₀ hpos]
    linarith

end Podc.LocalMessageReduction
