import Papers.PODC2024.ListDefectiveColoring.Basic

/-!
# Theorem 1.2 of [FK24]: the arithmetic of the parameter choice

Theorem 1.2 of [FK24] (oriented list defective colouring in CONGEST with slack `3√C`) is obtained
by plugging the algorithm of Theorem 1.1 (with `p = ⌈√Λ⌉` and `ε = 1/(3⌈log₄ C⌉)`) into the colour
space reduction of Lemma 3.5 (Theorem 3 of [FK23a]) with splitting parameter `λ = 4`. Both are
cited/algorithmic black boxes; what is checkable is the inequality that turns the slack condition
of the composed algorithm, eq. (8),
`∑_{x ∈ L_v} (d_v(x) + 1) > β_v · ((1 + ε) · 2)^{⌈log₄ C⌉}`,
into the condition `∑_{x ∈ L_v} (d_v(x) + 1) ≥ 3 · √C · β_v` of Theorem 1.2.

For `λ = Λ = 4` we have `p = ⌈√4⌉ = 2` and Theorem 1.1's factor is
`κ(4) = (1 + ε) · max(p, 4 / p) = 2 (1 + ε)`; hence Lemma 3.5 requires slack
`κ(4)^{⌈log₄ C⌉} = (2 (1 + 1/(3m)))^m` with `m = ⌈log₄ C⌉ = Nat.clog 4 C`.

* `FK24.kappa_pow_lt_three_sqrt`: `(2 (1 + 1/(3m)))^m < 3 √C` for every `C ≥ 1`
  (proof p. 15 of the arXiv version: `(1 + 1/(3m))^m ≤ e^{1/3}`, `2^m < 2 √C`,
  `2 e^{1/3} < 3`).
* `FK24.theorem12_slack`: the slack condition of Theorem 1.2 implies eq. (8).

## Round complexity (not formalized; remark)

Theorem 1.1 with `p = 2` and `ε = 1/(3m)` runs in
`T(4) = O((p/ε)²) + O(log* q) = O(log² C + log* q)`
rounds. Lemma 3.5 gives time `O(T(λ) · ⌈log_λ C⌉)`, so the paper's argument *as written* gives
`O((log² C + log* q) · log C) = O(log³ C + log C · log* q)` rather than the claimed
`O(log³ C + log* q)` (this is not formalized): the algorithm of Theorem 1.1 recomputes the defective colouring of Lemma 3.4
(cost `O(log* q)`) in each of the `⌈log₄ C⌉` levels of the recursion, because the out-degrees
(and hence the defective colouring needed) change from level to level. The paper's accounting
silently drops the factor `log C` on the `log* q` term.

Further minor points (see `differencies.md`): for `C = 1` the paper's `ε = 1/(3⌈log₄ C⌉)` divides by
zero (here `1/0 = 0`, harmless); Lemma 3.5 asks for `≥ β_v κ(Λ)` while Theorem 1.1 only solves
instances with strict `>`, which is again harmless because the final inequality is strict.
-/

namespace FK24

open Real

/-- `(1 + 1/(3m))^m ≤ e^{1/3}` (for `m = 0` the left side is `1`). -/
theorem one_add_inv_three_mul_pow_le (m : ℕ) : (1 + 1 / (3 * (m : ℝ))) ^ m ≤ exp (1 / 3) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    calc (1 + 1 / (3 * (m : ℝ))) ^ m ≤ (exp (1 / (3 * m))) ^ m := by
          gcongr
          have := add_one_le_exp (1 / (3 * (m : ℝ))); linarith
      _ = exp (1 / 3) := by
          rw [← exp_nat_mul]; congr 1; field_simp

/-- `2 e^{1/3} < 3`, via `e < 27/8`. -/
theorem two_mul_exp_third_lt_three : 2 * exp (1 / 3) < 3 := by
  have h3 : exp (1 / 3) ^ 3 = exp 1 := by rw [← exp_nat_mul]; norm_num
  have he : exp 1 < (3 / 2) ^ 3 := by
    have := exp_one_lt_d9; norm_num at this ⊢; linarith
  have : exp (1 / 3) < 3 / 2 :=
    lt_of_pow_lt_pow_left₀ 3 (by norm_num) (by rw [h3]; exact he)
  linarith

/-- `2^{⌈log₄ C⌉} < 2 √C` for `C ≥ 2`. -/
theorem two_pow_clog_four_lt {C : ℕ} (hC : 2 ≤ C) :
    (2 : ℝ) ^ Nat.clog 4 C < 2 * √(C : ℝ) := by
  have hm : 0 < Nat.clog 4 C := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 4 ^ (Nat.clog 4 C).pred < C := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 4 C = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
  rw [hk] at hlt ⊢
  simp only [Nat.pred_succ] at hlt
  have hlt' : ((2 : ℝ) ^ k) ^ 2 < C := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num; exact_mod_cast hlt
  have : (2 : ℝ) ^ k < √(C : ℝ) := (lt_sqrt (by positivity)).2 hlt'
  rw [pow_succ]; linarith

/-- The arithmetic of the proof of Theorem 1.2 of [FK24] (p. 15 of arXiv:2405.04648):
with `m = ⌈log₄ C⌉`, the slack `κ(4)^m = (2 (1 + 1/(3m)))^m` required by Lemma 3.5 applied to
Theorem 1.1 (`λ = 4`, `p = 2`, `ε = 1/(3m)`) is less than `3 √C`. -/
theorem kappa_pow_lt_three_sqrt {C : ℕ} (hC : 1 ≤ C) :
    (2 * (1 + 1 / (3 * (Nat.clog 4 C : ℝ)))) ^ Nat.clog 4 C < 3 * √(C : ℝ) := by
  rcases Nat.lt_or_ge C 2 with h1 | h2
  · obtain rfl : C = 1 := by omega
    simp
  · set m := Nat.clog 4 C
    have hs : 0 < √(C : ℝ) := sqrt_pos.2 (by exact_mod_cast (by omega : 0 < C))
    have ha := one_add_inv_three_mul_pow_le m
    have hb := two_pow_clog_four_lt h2
    have hc := two_mul_exp_third_lt_three
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    rw [mul_pow]
    calc (2 : ℝ) ^ m * (1 + 1 / (3 * (m : ℝ))) ^ m ≤ 2 ^ m * exp (1 / 3) := by gcongr
      _ < (2 * √(C : ℝ)) * exp (1 / 3) := by gcongr
      _ = (2 * exp (1 / 3)) * √(C : ℝ) := by ring
      _ < 3 * √(C : ℝ) := by gcongr

/-- Theorem 1.2 of [FK24], combinatorial part: an oriented list defective colouring instance with
`∑_{x ∈ L_v} (d_v(x) + 1) ≥ 3 √C · β_v` satisfies the slack condition (8) of the algorithm obtained
from Theorem 1.1 and Lemma 3.5 (with `λ = 4`, `p = 2`, `ε = 1/(3⌈log₄ C⌉)`), namely
`∑_{x ∈ L_v} (d_v(x) + 1) > β_v · (2 (1 + ε))^{⌈log₄ C⌉}`.

Here `β_v = max 1 (outdegree)` (`FK24.beta`, the convention of Section 2 of the paper; with the
literal outdegree an isolated node with an empty list would satisfy the hypothesis of Theorem 1.2).
Round complexity is not formalized; the paper's argument as written gives
`O(log³ C + log C · log* q)` (see the module docstring) rather than the claimed
`O(log³ C + log* q)`. -/
theorem theorem12_slack {V α : Type*} {C : ℕ} (hC : 1 ≤ C) (I : ListInstance V α)
    (out : V → Finset V)
    (h : ∀ v, 3 * √(C : ℝ) * (beta out v : ℝ) ≤ (I.weight v : ℝ)) (v : V) :
    (beta out v : ℝ) * (2 * (1 + 1 / (3 * (Nat.clog 4 C : ℝ)))) ^ Nat.clog 4 C <
      (I.weight v : ℝ) := by
  have hb : (0 : ℝ) < beta out v := by exact_mod_cast one_le_beta out v
  have := kappa_pow_lt_three_sqrt hC
  calc (beta out v : ℝ) * (2 * (1 + 1 / (3 * (Nat.clog 4 C : ℝ)))) ^ Nat.clog 4 C
      < (beta out v : ℝ) * (3 * √(C : ℝ)) := by gcongr
    _ = 3 * √(C : ℝ) * (beta out v : ℝ) := by ring
    _ ≤ _ := h v

end FK24
