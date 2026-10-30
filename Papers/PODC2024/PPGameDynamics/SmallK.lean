import Papers.PODC2024.PPGameDynamics.Ehrenfest

/-!
# The cases `k = 2` and `k = 3` (Appendix A.1, A.2) and the explicit PMF (Appendix A.3)

* `multinomialPMF_ehrParam`: the PMF of Appendix A.3,
  `π(x) = λ^{(k-1)x_k + ⋯ + x_2} / (1 + λ + ⋯ + λ^{k-1})^m · (m choose x_1, …, x_k)`;
* `proposition_A_1`: `k = 2`, `π(i, m - i) = λ^{m-i} / (1+λ)^m · (m choose i)`;
* `proposition_A_3`: `k = 3`,
  `π(i, j, m-i-j) = λ^{2(m-i-j)} λ^j / (1+λ+λ²)^m · m! / (i! j! (m-i-j)!)`.

Here `π` is any stationary distribution of the Ehrenfest process (it is unique, Theorem 2.4).
-/

open Finset Matrix Cslib.Probability.Markov

namespace Podc.PPGameDynamics

variable {k m : ℕ}

/-- The PMF of Appendix A.3: `π(x) = λ^{∑_j (j-1) x_j} · multinomial(x) / (∑_i λ^{i-1})^m`. -/
theorem multinomialPMF_ehrParam (lam : ℝ) (x : Simplex k m) :
    multinomialPMF (ehrParam k lam) x =
      lam ^ (∑ j : Fin k, j.val * x.1 j) * (Nat.multinomial univ x.1 : ℝ) /
        (∑ i : Fin k, lam ^ i.val) ^ m := by
  unfold multinomialPMF ehrParam
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, x.2]
  ring

/-- **Proposition A.1** (`k = 2`). For the `(2, a, b, m)`-Ehrenfest process with stationary
distribution `π`, and `λ = a / b`: `π(i, m - i) = λ^{m-i} / (1 + λ)^m · (m choose i)`. -/
theorem proposition_A_1 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (π : Simplex 2 m → ℝ) (hπ : IsDistribution π) (hstat : IsStationary (ehrenfest 2 a b m) π)
    (i : ℕ) (hi : i ≤ m) :
    π ⟨![i, m - i], by simp [Fin.sum_univ_two]; omega⟩ =
      (a / b) ^ (m - i) / (1 + a / b) ^ m * (m.choose i : ℝ) := by
  rw [ehrenfest_stationary_unique (by norm_num) ha hb hab π hπ hstat, multinomialPMF_eq]
  simp only [ehrParam, Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [Nat.cast_choose ℝ hi]
  have hL : 0 < a / b := div_pos ha hb
  generalize a / b = L at hL ⊢
  have h1 : (0 : ℝ) < 1 + L := by positivity
  have e : (1 + L) ^ m = (1 + L) ^ i * (1 + L) ^ (m - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [div_pow, div_pow, one_pow, e]
  field_simp

/-- **Proposition A.3** (`k = 3`). For the `(3, a, b, m)`-Ehrenfest process with stationary
distribution `π`, and `λ = a / b`:
`π(i, j, m-i-j) = λ^{2(m-i-j)} λ^j / (1+λ+λ²)^m · m! / (i! j! (m-i-j)!)`. -/
theorem proposition_A_3 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (π : Simplex 3 m → ℝ) (hπ : IsDistribution π) (hstat : IsStationary (ehrenfest 3 a b m) π)
    (i j : ℕ) (hij : i + j ≤ m) :
    π ⟨![i, j, m - i - j], by simp [Fin.sum_univ_three]; omega⟩ =
      (a / b) ^ (2 * (m - i - j)) * (a / b) ^ j / (1 + a / b + (a / b) ^ 2) ^ m *
        ((m.factorial : ℝ) / (i.factorial * j.factorial * (m - i - j).factorial)) := by
  rw [ehrenfest_stationary_unique (by norm_num) ha hb hab π hπ hstat, multinomialPMF_eq]
  simp only [ehrParam, Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, Matrix.tail_cons, Matrix.head_cons]
  have hL : 0 < a / b := div_pos ha hb
  generalize a / b = L at hL ⊢
  have h1 : (0 : ℝ) < 1 + L + L ^ 2 := by positivity
  have e : (1 + L + L ^ 2) ^ m =
      (1 + L + L ^ 2) ^ i * (1 + L + L ^ 2) ^ j * (1 + L + L ^ 2) ^ (m - i - j) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [div_pow, div_pow, div_pow, one_pow, e, ← pow_mul, mul_comm 2 (m - i - j)]
  field_simp

end Podc.PPGameDynamics
