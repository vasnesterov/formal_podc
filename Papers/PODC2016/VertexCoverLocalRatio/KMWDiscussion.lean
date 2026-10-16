import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Section 5: the arithmetic of the discussion of [KMW10]

Section 5 argues that the last step of the proof of Theorem 9 of Kuhn–Moscibroda–Wattenhofer
(arXiv 1011.5470, 2010) is valid only for small `k`. The two constraints taken from [KMW10] are
`n ≤ 2^{2k³+4k} δ^{4k²}` and `Δ = 2^{k(k+1)/2} δ^{k+1}`, and [KMW10] concludes
`δ = Ω(n^{(1/4-ε)/k²})` and `δ = Ω(Δ^{(1-ε)/(k+1)})`.

We check the paper's arithmetic, writing `n = 2^L`, `Δ = 2^D`, and keeping the constant `c > 0`
hidden in `Ω`:
* `first_constraint_iff`: the smallest `δ` allowed by the first constraint,
  `δ₀ = n^{1/4k²} / 2^{(2k³+4k)/4k²}`, satisfies `δ₀ ≥ c·n^{(1/4-ε)/k²}` iff
  `2k³ + 4k ≤ 4εL - 4k²·log₂ c`; hence (`first_constraint_k_le`) `k ≤ max(4·log₂(1/c), (4εL)^{1/3})`,
  i.e. `k = O((log n)^{1/3})` for a fixed constant.
* `second_constraint_iff`: `δ = Δ^{1/(k+1)} / 2^{k/2} ≥ c·Δ^{(1-ε)/(k+1)}` iff
  `k(k+1) ≤ 2εD - 2(k+1)·log₂ c`; hence (`second_constraint_k_le`) `k ≤ max(4·log₂(1/c), 2√(εD))`,
  i.e. `k = O(√(log Δ))`.

This confirms the computation in Section 5 (with the `Ω`-constant made explicit). Whether the two
constraints are all that [KMW10] has available is a statement about [KMW10] and is not formalized.
-/

namespace VertexCoverLocalRatio.KMW

open Real

/-- First constraint. -/
theorem first_constraint_iff {L k ε c : ℝ} (hk : 0 < k) (hc : 0 < c) :
    c * (2 : ℝ) ^ ((1 / 4 - ε) * L / k ^ 2) ≤
        (2 : ℝ) ^ (L / (4 * k ^ 2)) / (2 : ℝ) ^ ((2 * k ^ 3 + 4 * k) / (4 * k ^ 2)) ↔
      2 * k ^ 3 + 4 * k ≤ 4 * ε * L - 4 * k ^ 2 * logb 2 c := by
  have hc2 : c = (2 : ℝ) ^ logb 2 c := (rpow_logb (by norm_num) (by norm_num) hc).symm
  rw [hc2, ← rpow_add (by norm_num), ← rpow_sub (by norm_num),
    rpow_le_rpow_left_iff (by norm_num), ← hc2]
  have hk2 : 0 < 4 * k ^ 2 := by positivity
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h hk2.le
    have e1 : 4 * k ^ 2 * (logb 2 c + (1 / 4 - ε) * L / k ^ 2) =
        4 * k ^ 2 * logb 2 c + L - 4 * ε * L := by field_simp; ring
    have e2 : 4 * k ^ 2 * (L / (4 * k ^ 2) - (2 * k ^ 3 + 4 * k) / (4 * k ^ 2)) =
        L - (2 * k ^ 3 + 4 * k) := by field_simp
    rw [e1, e2] at h'
    linarith
  · intro h
    rw [← mul_le_mul_iff_of_pos_left hk2]
    have e1 : 4 * k ^ 2 * (logb 2 c + (1 / 4 - ε) * L / k ^ 2) =
        4 * k ^ 2 * logb 2 c + L - 4 * ε * L := by field_simp; ring
    have e2 : 4 * k ^ 2 * (L / (4 * k ^ 2) - (2 * k ^ 3 + 4 * k) / (4 * k ^ 2)) =
        L - (2 * k ^ 3 + 4 * k) := by field_simp
    rw [e1, e2]
    linarith

/-- Consequence of the first constraint: `k ≤ max(4 log₂(1/c), (4εL)^{1/3})`. -/
theorem first_constraint_k_le {L k ε c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (h : c * (2 : ℝ) ^ ((1 / 4 - ε) * L / k ^ 2) ≤
        (2 : ℝ) ^ (L / (4 * k ^ 2)) / (2 : ℝ) ^ ((2 * k ^ 3 + 4 * k) / (4 * k ^ 2))) :
    k ≤ 4 * logb 2 (1 / c) ∨ k ^ 3 ≤ 4 * ε * L := by
  rw [first_constraint_iff hk hc] at h
  rw [one_div, logb_inv]
  by_cases hk4 : k ≤ 4 * -logb 2 c
  · exact Or.inl hk4
  · right
    push Not at hk4
    have : -(4 * k ^ 2 * logb 2 c) ≤ k ^ 3 := by nlinarith
    nlinarith

/-- Second constraint. -/
theorem second_constraint_iff {D k ε c : ℝ} (hk : 0 < k) (hc : 0 < c) :
    c * (2 : ℝ) ^ ((1 - ε) * D / (k + 1)) ≤ (2 : ℝ) ^ (D / (k + 1)) / (2 : ℝ) ^ (k / 2) ↔
      k * (k + 1) ≤ 2 * ε * D - 2 * (k + 1) * logb 2 c := by
  have hc2 : c = (2 : ℝ) ^ logb 2 c := (rpow_logb (by norm_num) (by norm_num) hc).symm
  rw [hc2, ← rpow_add (by norm_num), ← rpow_sub (by norm_num),
    rpow_le_rpow_left_iff (by norm_num), ← hc2]
  have hk1 : 0 < 2 * (k + 1) := by positivity
  have e1 : 2 * (k + 1) * (logb 2 c + (1 - ε) * D / (k + 1)) =
      2 * (k + 1) * logb 2 c + 2 * D - 2 * ε * D := by field_simp; ring
  have e2 : 2 * (k + 1) * (D / (k + 1) - k / 2) = 2 * D - k * (k + 1) := by field_simp
  rw [← mul_le_mul_iff_of_pos_left hk1, e1, e2]
  constructor <;> intro h <;> linarith

/-- Consequence of the second constraint: `k ≤ 4 log₂(1/c)` or `k² ≤ 4εD`. -/
theorem second_constraint_k_le {D k ε c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (h : c * (2 : ℝ) ^ ((1 - ε) * D / (k + 1)) ≤ (2 : ℝ) ^ (D / (k + 1)) / (2 : ℝ) ^ (k / 2)) :
    k ≤ 4 * logb 2 (1 / c) ∨ k ^ 2 ≤ 4 * ε * D := by
  rw [second_constraint_iff hk hc] at h
  rw [one_div, logb_inv]
  by_cases hk4 : k ≤ 4 * -logb 2 c
  · exact Or.inl hk4
  · right
    push Not at hk4
    nlinarith

end VertexCoverLocalRatio.KMW
