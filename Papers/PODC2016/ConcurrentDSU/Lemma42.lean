import Mathlib

/-!
# Lemma 4.2: the Chernoff step does not give the stated exponent

Lemma 4.2 claims: the probability that a node `x` has an ancestor `y` of rank `< h` such that the
path from `x` to `y` has `c·h` parent pointers is at most `1 / exp ((c/2 - 1)^2 h^2 / c)`.
The proof: along the path there are fewer than `h` "good" links (links between nodes of
different ranks), each of the `c·h` links is good with probability at least `1/2` independently
of the others (Lemma 4.1), "and the lemma follows by a Chernoff bound".

The Chernoff bound `P[X ≤ (1 - δ) μ] ≤ exp (-δ² μ / 2)` with `μ = c h / 2`, `(1 - δ) μ = h`
gives `exp (-(c/2 - 1)^2 h / c)`: the exponent is linear in `h`, not quadratic. The quadratic
exponent does not hold in the very model the proof reduces to: with fair coins (each link good
with probability exactly `1/2`, which Lemma 4.1 allows), `c = 4`, `h = 6`, the probability of
fewer than `6` good links among `24` is `55455 / 2^24 ≈ 3.3·10⁻³`, larger than the claimed bound
`exp (-9) ≈ 1.2·10⁻⁴` (`chernoff_step_fails`).

Whether the *statement* of Lemma 4.2 is nevertheless true for the actual union forest is not
settled by this: we only show that its proof does not establish it. Corollary 4.2.1 and
Theorem 4.3 survive with the linear exponent (choose `c` larger), but the second case (`d < 1`)
of the proof of Theorem 5.1 uses the quadratic exponent (`n / 2^(h²/16)` middle nodes); with the
linear exponent the argument needs a larger constant in place of `4h` in the definition of
"low" nodes (see `differencies.md`).
-/

namespace Podc.ConcurrentDSU

/-- Probability that `n` independent fair coins show fewer than `h` heads. -/
def coinTail (n h : ℕ) : ℚ := (∑ i ∈ Finset.range h, (n.choose i : ℚ)) / 2 ^ n

lemma coinTail_24_6 : coinTail 24 6 = 55455 / 16777216 := by
  simp only [coinTail, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]

/-- **Lemma 4.2, proof gap.** For `c = 4`, `h = 6` the bound `1 / exp ((c/2 - 1)^2 h^2 / c)`
claimed by Lemma 4.2 is smaller than the probability that `24` fair coins show fewer than `6`
heads, to which the proof reduces the event. -/
theorem chernoff_step_fails :
    1 / Real.exp (((4 : ℝ) / 2 - 1) ^ 2 * 6 ^ 2 / 4) < ((coinTail 24 6 : ℚ) : ℝ) := by
  rw [coinTail_24_6]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ^ 9 < Real.exp 1 ^ 9 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (2.7 : ℝ) ^ 9 := by positivity
  have he : ((4 : ℝ) / 2 - 1) ^ 2 * 6 ^ 2 / 4 = 9 := by norm_num
  rw [he, h9]
  calc 1 / Real.exp 1 ^ 9 < 1 / (2.7 : ℝ) ^ 9 := one_div_lt_one_div_of_lt hpos h2
    _ < _ := by push_cast; norm_num

/-- With the exponent linear in `h` (what the Chernoff bound gives), the bound is consistent with
the fair-coin model at `c = 4`, `h = 6`. -/
theorem chernoff_linear_ok :
    ((coinTail 24 6 : ℚ) : ℝ) ≤ 1 / Real.exp (((4 : ℝ) / 2 - 1) ^ 2 * 6 / 4) := by
  rw [coinTail_24_6]
  have he : ((4 : ℝ) / 2 - 1) ^ 2 * 6 / 4 = 3 / 2 := by norm_num
  rw [he]
  have h1 : Real.exp (3 / 2) ≤ Real.exp 2 := Real.exp_le_exp.2 (by norm_num)
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (by norm_num)
  have hpos := Real.exp_pos (3 / 2)
  rw [le_div_iff₀ hpos]
  push_cast
  nlinarith

end Podc.ConcurrentDSU
