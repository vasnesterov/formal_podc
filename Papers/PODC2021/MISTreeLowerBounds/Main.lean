import Papers.PODC2021.MISTreeLowerBounds.RoundElim
import Papers.PODC2021.MISTreeLowerBounds.Lemma8
import Papers.PODC2021.MISTreeLowerBounds.Lemma9
import Papers.PODC2021.MISTreeLowerBounds.Lemmas

/-!
# Lemma 8 (time complexity form), Corollary 10, Lemma 13 and the port-numbering lower bound

* `lemma_8`: if `Π_Δ(a, x)` is solvable in `T` rounds, then `Π⁺_Δ(a, x)` is solvable in
  `max(T - 1, 0)` rounds (round elimination `RoundElim.lean` + the relaxation `Lemma8.lean`).
* `corollary_10`: the same for `Π_Δ(⌊(a - 2x - 1)/2⌋, x + 1)` (with Lemma 9).
* `lemma_13`: the lower-bound sequence `Π_i = Π_Δ(⌊Δ/2^{3i}⌋, k + i)`, `i ≤ t`, with an explicit
  arithmetic condition `8^t (k + t + 1) ≤ Δ` in place of "`t = ε log Δ`, `k ≤ Δ^ε`, `Δ` large".
* `odsLowerBound`: every deterministic algorithm computing a `k`-outdegree dominating set on the
  `Δ`-regular tree (port-numbering model, with a `Δ`-edge colouring and an edge orientation as
  input) needs at least `t` rounds whenever `8^t (k + t + 1) ≤ Δ`.
* `odsLowerBound_log`: the asymptotic form: `⌊log₂ Δ / 6⌋` rounds for all `k ≤ 2^{⌊log₂ Δ / 6⌋}`
  (so `ε = 1/6` works in "`Ω(log Δ)` rounds for `k ≤ Δ^ε`"). This is the port-numbering lower bound
  claimed in §1.1 and proved in §3.5 of the paper.
-/

namespace Podc.MISTreeLowerBounds

variable {Δ : ℕ}

/-- Lemma 8 of [paper]: if `Π_Δ(a, x)` has time complexity `T`, then `Π⁺_Δ(a, x)` has time
complexity at most `max{T - 1, 0}`, for `x + 2 ≤ a ≤ Δ`. -/
theorem lemma_8 {a x T : ℕ} (hxa : x + 2 ≤ a) (ha : a ≤ Δ) (h : (Pi Δ a x).SolvableIn T) :
    (PiPlus Δ a x).SolvableIn (T - 1) :=
  h.Rbar_R_sub.of_reduction (lemma_8_reduction hxa ha)

/-- Corollary 10 of [paper]: if `Π_Δ(a, x)` has time complexity `T`, then
`Π_Δ(⌊(a - 2x - 1)/2⌋, x + 1)` has complexity at most `max{T - 1, 0}`, given a `Δ`-edge colouring,
for `2x + 1 ≤ a`, `x + 2 ≤ a ≤ Δ`. -/
theorem corollary_10 {a x T : ℕ} (h2x : 2 * x + 1 ≤ a) (hxa : x + 2 ≤ a) (ha : a ≤ Δ)
    (h : (Pi Δ a x).SolvableIn T) : (Pi Δ ((a - 2 * x - 1) / 2) (x + 1)).SolvableIn (T - 1) :=
  (lemma_8 hxa ha h).of_reduction (lemma_9 h2x ha)

/-- The problem sequence of Lemma 13: `Π_i = Π_Δ(⌊Δ/2^{3i}⌋, k + i)`. -/
def seqProblem (Δ k i : ℕ) : Problem Δ L5 := Pi Δ (Δ / 8 ^ i) (k + i)

/-- One step of the sequence: `Π_{i+1}` is 0-round solvable from `R̄(R(Π_i))` (given the colouring). -/
theorem seqProblem_step {k t i : ℕ} (h : 8 ^ t * (k + t + 1) ≤ Δ) (hi : i < t) :
    ZeroRoundReduction (seqProblem Δ k i).R.Rbar (seqProblem Δ k (i + 1)) := by
  unfold seqProblem
  have hq : 8 ^ (i + 1) * (k + i + 2) ≤ Δ := by
    calc 8 ^ (i + 1) * (k + i + 2) ≤ 8 ^ t * (k + t + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hi) (by omega)
      _ ≤ Δ := h
  have ha : 8 * (k + i + 2) ≤ Δ / 8 ^ i := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc 8 * (k + i + 2) * 8 ^ i = 8 ^ (i + 1) * (k + i + 2) := by ring
      _ ≤ Δ := hq
  have hdiv : Δ / 8 ^ (i + 1) = Δ / 8 ^ i / 8 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have haΔ : Δ / 8 ^ i ≤ Δ := Nat.div_le_self _ _
  refine ((lemma_8_reduction (by omega) haΔ).trans (lemma_9 (by omega) haΔ)).trans ?_
  rw [hdiv, show k + (i + 1) = k + i + 1 by ring]
  exact lemma_11 (by omega) le_rfl (by omega)

/-- The last problem of the sequence is not 0-round solvable. -/
theorem seqProblem_not_zero {k t : ℕ} (h : 8 ^ t * (k + t + 1) ≤ Δ) :
    ¬ (seqProblem Δ k t).SolvableIn 0 := by
  have h8 : 1 ≤ 8 ^ t := Nat.one_le_pow _ _ (by norm_num)
  have hkt : k + t + 1 ≤ Δ := le_trans (Nat.le_mul_of_pos_left _ h8) h
  refine lemma_12 (by omega) ?_
  rw [Nat.le_div_iff_mul_le (by positivity)]
  nlinarith

/-- Lemma 13 of [paper], with an explicit condition: if `8^t (k + t + 1) ≤ Δ`, the problems
`Π_i = Π_Δ(⌊Δ/2^{3i}⌋, k + i)`, `0 ≤ i ≤ t`, satisfy (given a `Δ`-edge colouring)
1. `Π_0 = Π_Δ(Δ, k)`,
2. `Π_{i+1}` can be solved in 0 rounds given a solution to `R̄(R(Π_i))` for `i < t`,
3. `Π_t` cannot be solved in 0 rounds in the deterministic port-numbering model,
4. all problems use the 5 labels `L5`.
(The paper takes `t = ε log Δ`, `k ≤ Δ^ε` and `Δ` large enough; see `odsLowerBound_log`.) -/
theorem lemma_13 {k t : ℕ} (h : 8 ^ t * (k + t + 1) ≤ Δ) :
    seqProblem Δ k 0 = Pi Δ Δ k ∧
    (∀ i < t, ZeroRoundReduction (seqProblem Δ k i).R.Rbar (seqProblem Δ k (i + 1))) ∧
    ¬ (seqProblem Δ k t).SolvableIn 0 ∧
    Fintype.card L5 = 5 :=
  ⟨by simp [seqProblem], fun _ hi => seqProblem_step h hi, seqProblem_not_zero h, rfl⟩

/-- **Lower bound in the port-numbering model** (§3.5): computing a `k`-outdegree dominating set
on the `Δ`-regular tree, deterministically in the port-numbering model with a `Δ`-edge colouring
and an edge orientation given as input, requires at least `t` rounds whenever
`8^t (k + t + 1) ≤ Δ`. -/
theorem odsLowerBound {k t T : ℕ} (h : 8 ^ t * (k + t + 1) ≤ Δ) (hA : ODSSolvableIn Δ k T) :
    t ≤ T := by
  by_contra hT
  push Not at hT
  have hk : k ≤ Δ := by
    have h8 : 1 ≤ 8 ^ t := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  -- `Π_0` is solvable in `T + 1` rounds (Lemma 5)
  have h0 : (seqProblem Δ k 0).SolvableIn (T + 1) := by
    simpa [seqProblem] using lemma_5 hk Δ hA
  -- `Π_j` is solvable in `T + 1 - j` rounds
  have hj : ∀ j ≤ T + 1, (seqProblem Δ k j).SolvableIn (T + 1 - j) := by
    intro j hj
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have := (ih (by omega)).Rbar_R_sub.of_reduction (seqProblem_step h (by omega))
      rwa [show T + 1 - j - 1 = T + 1 - (j + 1) by omega] at this
  have hlast := hj (T + 1) le_rfl
  rw [Nat.sub_self] at hlast
  -- but `Π_{T+1}` is not 0-round solvable (Lemma 12, `T + 1 ≤ t`)
  have h' : 8 ^ (T + 1) * (k + (T + 1) + 1) ≤ Δ :=
    le_trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hT) (by omega)) h
  exact seqProblem_not_zero h' hlast

/-- **Main port-numbering lower bound, asymptotic form** (§1.1, §3.5): for all `Δ` and all
`k ≤ 2^{⌊log₂ Δ / 6⌋}` (≈ `Δ^{1/6}`), every deterministic port-numbering algorithm computing a
`k`-outdegree dominating set on the `Δ`-regular tree (with a `Δ`-edge colouring and an edge
orientation as input) needs at least `⌊log₂ Δ / 6⌋` rounds: `Ω(log Δ)` rounds for `k ≤ Δ^ε`. -/
theorem odsLowerBound_log {k T : ℕ} (hk : k ≤ 2 ^ (Nat.log 2 Δ / 6)) (hA : ODSSolvableIn Δ k T) :
    Nat.log 2 Δ / 6 ≤ T := by
  set L := Nat.log 2 Δ
  set t := L / 6
  rcases Nat.eq_zero_or_pos t with ht | ht
  · rw [ht]; exact Nat.zero_le _
  refine odsLowerBound ?_ hA
  have hΔ : Δ ≠ 0 := by
    rintro rfl; simp [L, t] at ht
  have hL : 2 ^ L ≤ Δ := Nat.pow_log_le_self 2 hΔ
  have ht1 : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  have h4 : 4 * t + 1 ≤ L := by omega
  calc 8 ^ t * (k + t + 1) ≤ 8 ^ t * (2 * 2 ^ t) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (4 * t + 1) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]; ring
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) h4
    _ ≤ Δ := hL

end Podc.MISTreeLowerBounds
