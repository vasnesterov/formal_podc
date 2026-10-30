import Papers.PODC2012.WirelessPacketScheduling.Model

/-!
# The running time of Algorithm 1 (first part of the proof of Theorem 1)

Algorithm 1 has a fixed schedule: iteration `i` of the first loop runs `ψ_i` executions of
`𝒜(χ, mχ)` of `f(mχ)·χ` steps each, and the clean-up loop runs `⌈φ⌉ + 1` executions of
`𝒜(2φχ log n, n)` of `f(n)·2φχ log n` steps each. We check the paper's estimate
`∑_{i=1}^{ξ} ⌈2^{-i+1} I/χ⌉ f(mχ) χ + (⌈φ⌉+1) f(n) 2φχ log n
   ≤ 2 f(mχ) I + ξ f(mχ) χ + (⌈φ⌉+1) f(n) 2φχ log n`.

The paper then writes the middle term as `O(log n · f(mχ))`; since `χ = Θ(log m)` it is really
`O(log n · log m · f(mχ))` (this is the bound `O(log n · log² m)` stated in the introduction for
`f = O(log)`). See `differencies.md`.
-/

namespace Podc.WirelessPacketScheduling

open Finset

/-- The number of time steps used by Algorithm 1, for static running-time function `f`. -/
noncomputable def alg1Time (f : ℝ → ℝ) (b : ℝ) (m n : ℕ) (I φ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (xi b m n I φ).toNat, (psi m I (i + 1) : ℝ) * f (m * chi m) * chi m) +
    (⌈φ⌉₊ + 1) * f n * finalParam b m n φ

lemma chi_pos (m : ℕ) (hm : 1 ≤ m) : 0 < chi m := by
  unfold chi
  have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  positivity

/-- `∑_{i=1}^{k} ⌈2^{-i+1} I/χ⌉ ≤ 2 I/χ + k`. -/
lemma sum_psi_le (m : ℕ) (hm : 1 ≤ m) (I : ℝ) (hI : 0 ≤ I) (k : ℕ) :
    ∑ i ∈ Finset.range k, (psi m I (i + 1) : ℝ) ≤ 2 * I / chi m + k := by
  have hc := chi_pos m hm
  have hterm : ∀ i : ℕ, (psi m I (i + 1) : ℝ) ≤ (1 / 2 : ℝ) ^ i * I / chi m + 1 := by
    intro i
    unfold psi
    have h2 : (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) + 1) = (1 / 2 : ℝ) ^ i := by
      rw [show (-((i + 1 : ℕ) : ℤ) + 1) = -(i : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        one_div, inv_pow]
    rw [h2]
    have : 0 ≤ (1 / 2 : ℝ) ^ i * I / chi m := by positivity
    exact (Nat.ceil_lt_add_one this).le
  have hgeom : ∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ i ≤ 2 := by
    have := sum_geometric_two_le k
    simpa using this
  calc ∑ i ∈ Finset.range k, (psi m I (i + 1) : ℝ)
      ≤ ∑ i ∈ Finset.range k, ((1 / 2 : ℝ) ^ i * I / chi m + 1) := sum_le_sum fun i _ => hterm i
    _ = (∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ i) * (I / chi m) + k := by
        rw [sum_add_distrib, sum_mul]; simp [mul_div_assoc]
    _ ≤ 2 * (I / chi m) + k := by gcongr
    _ = 2 * I / chi m + k := by ring

/-- The displayed running-time estimate in the proof of **Theorem 1**:
`time ≤ 2 f(mχ) I + ξ f(mχ) χ + (⌈φ⌉+1) f(n) 2φχ log n` (for `I ≥ 0`, `f(mχ) ≥ 0`, `m ≥ 1`). -/
theorem alg1Time_le (f : ℝ → ℝ) (b : ℝ) (m n : ℕ) (hm : 1 ≤ m) (I φ : ℝ) (hI : 0 ≤ I)
    (hf : 0 ≤ f (m * chi m)) :
    alg1Time f b m n I φ ≤ 2 * f (m * chi m) * I + (xi b m n I φ).toNat * f (m * chi m) * chi m +
      (⌈φ⌉₊ + 1) * f n * finalParam b m n φ := by
  have hc := chi_pos m hm
  unfold alg1Time
  have hs := sum_psi_le m hm I hI (xi b m n I φ).toNat
  have : (∑ i ∈ Finset.range (xi b m n I φ).toNat, (psi m I (i + 1) : ℝ) * f (m * chi m) * chi m)
      = (∑ i ∈ Finset.range (xi b m n I φ).toNat, (psi m I (i + 1) : ℝ)) * (f (m * chi m) * chi m) := by
    rw [sum_mul]; simp [mul_assoc]
  rw [this]
  have hfc : 0 ≤ f (m * chi m) * chi m := by positivity
  have := mul_le_mul_of_nonneg_right hs hfc
  have e : (2 * I / chi m + (xi b m n I φ).toNat) * (f (m * chi m) * chi m) =
      2 * f (m * chi m) * I + (xi b m n I φ).toNat * f (m * chi m) * chi m := by
    field_simp
  linarith

end Podc.WirelessPacketScheduling
