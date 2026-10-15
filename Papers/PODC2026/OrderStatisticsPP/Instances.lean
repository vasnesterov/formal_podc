import Papers.PODC2026.OrderStatisticsPP.OrderBased
import Papers.PODC2026.OrderStatisticsPP.SelfExcluding

/-!
# The clique dynamics are Order-Based, with the paper's `f_k`, `h_k`

The three clique dynamics are instances of the intended reading of Definition 4.2 (`OrderBased`), with
exactly the coefficients the paper computes:
* Copy-or-Max (Lemma 4.2): `f_k = p (n-k+1)(k-1)/n²`, `h_k = k(n-k)/n²`;
* Biased-Median (proof of Theorem 2, from Lemma 4.8):
  `f_k = p/(1-p) · (n-k+1)(k-1)²/n³`, `h_k = k(n-k)²/n³`;
* Self-Excluding Median (proof of Theorem 8, from Lemma 4.9):
  `f_k = (n-k+1)(k-1)²(3n-2k+2)/n⁴`, `h_k = k(n-k)²(n+2k)/n⁴`.
(The full version's Lemma 4.9 and proof of Theorem 8 divide by `n³` instead of `n⁴`; the
proceedings version's `n⁴` is the correct one. Ratios — and hence the laws — are unaffected.)
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α]

/-- The median is one of the three opinions. -/
lemma med3_choice (a b c : α) : med3 a b c = a ∨ med3 a b c = b ∨ med3 a b c = c := by
  unfold med3
  rcases max_choice (min a b) (min (max a b) c) with h | h <;> rw [h]
  · rcases min_choice a b with h' | h' <;> rw [h'] <;> simp
  · rcases min_choice (max a b) c with h' | h' <;> rw [h']
    · rcases max_choice a b with h'' | h'' <;> rw [h''] <;> simp
    · simp

lemma sum_mul_sum_fin (f g : Fin n → ℝ) : ∑ u, ∑ v, f u * g v = (∑ u, f u) * (∑ v, g v) := by
  rw [Finset.sum_mul_sum]

/-- Copy-or-Max coefficients (Lemma 4.2). -/
noncomputable def cmF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := p * ((n : ℝ) - k + 1) * ((k : ℝ) - 1) / n ^ 2
noncomputable def cmH (n : ℕ) (k : ℕ) : ℝ := (k : ℝ) * ((n : ℝ) - k) / n ^ 2

/-- **Lemma 4.2** (threshold form): Copy-or-Max on the clique is Order-Based with
`f_k = p (n-k+1)(k-1)/n²` and `h_k = k(n-k)/n²`. -/
theorem copyOrMax_orderBased (hn : 0 < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    OrderBased (n := n) (α := α) (comμ (fun _ _ => (1 : ℝ)) p) (fun ω _ => ω.1)
      (fun ω c => comNew c ω) (cmF n p) (cmH n) where
  nonneg := comμ_nonneg (fun _ _ => zero_le_one) (clique_W_pos hn) hp0 hp1
  sum_one := comμ_sum (clique_W_pos hn)
  adopt ω c := by
    unfold comNew
    split_ifs
    · exact ⟨_, rfl⟩
    · rcases max_choice (c ω.1) (c ω.2.1) with h | h
      · exact ⟨ω.1, h⟩
      · exact ⟨ω.2.1, h⟩
  up D hD c := by
    rw [com_upMass hD]
    simp only [one_mul]
    rw [sum_mul_sum_fin (fun u => 1 - ind D (c u)) (fun v => ind D (c v)), sum_one_sub_ind,
      ← cnt_eq_sum]
    simp only [cmF, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; ring
  down D hD c := by
    rw [com_downMass hD]
    simp only [one_mul]
    rw [sum_mul_sum_fin (fun u => ind D (c u)) (fun v => 1 - ind D (c v)), sum_one_sub_ind,
      ← cnt_eq_sum]
    simp only [cmH, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring

/-- Biased-Median coefficients (proof of Theorem 2). -/
noncomputable def bmF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  p / (1 - p) * ((n : ℝ) - k + 1) * ((k : ℝ) - 1) ^ 2 / n ^ 3
noncomputable def bmH (n : ℕ) (k : ℕ) : ℝ := (k : ℝ) * ((n : ℝ) - k) ^ 2 / n ^ 3

/-- Biased-Median on the clique is Order-Based with the coefficients of the proof of
Theorem 2. -/
theorem biasedMedian_orderBased (hn : 0 < n) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    OrderBased (n := n) (α := α) (bmμ n p) (fun ω _ => ω.1) (fun ω c => bmNew c ω)
      (bmF n p) (bmH n) where
  nonneg := bmμ_nonneg hp0 hp
  sum_one := bmμ_sum hn
  adopt ω c := by
    unfold bmNew
    split_ifs
    · rcases med3_choice (c ω.1) (c ω.2.1) (c ω.2.2.1) with h | h | h <;> exact ⟨_, h⟩
    · exact ⟨_, rfl⟩
  up D hD c := by rw [bm_upMass hD, bmF]; push_cast; ring
  down D hD c := by rw [bm_downMass hD, bmH]; ring

/-- Self-Excluding Median coefficients (proof of Theorem 8). -/
noncomputable def sxF (n : ℕ) (k : ℕ) : ℝ :=
  ((n : ℝ) - k + 1) * ((k : ℝ) - 1) ^ 2 * (3 * n - 2 * k + 2) / n ^ 4
noncomputable def sxH (n : ℕ) (k : ℕ) : ℝ := (k : ℝ) * ((n : ℝ) - k) ^ 2 * (n + 2 * k) / n ^ 4

/-- Self-Excluding Median on the clique is Order-Based with the coefficients of the proof of
Theorem 8. -/
theorem selfExcludingMedian_orderBased (hn : 0 < n) :
    OrderBased (n := n) (α := α) (sxμ n) (fun ω _ => ω.1)
      (fun ω c => med3 (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2)) (sxF n) (sxH n) where
  nonneg _ := by unfold sxμ; positivity
  sum_one := sxμ_sum hn
  adopt ω c := by
    rcases med3_choice (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2) with h | h | h <;> exact ⟨_, h⟩
  up D hD c := by rw [sx_upMass hD, sxF]; push_cast; ring
  down D hD c := by rw [sx_downMass hD, sxH]; ring

/-- **Lemma 4.5** (detailed balance): `π_{k+1} f_{k+1} = π_k h_k` for the geometric law and the
Copy-or-Max coefficients, `k < n`; i.e. `π` is a (reversible) stationary distribution of the
rank chain `Pᵀ`. -/
theorem lemma45_detailed_balance {p : ℝ} {k : ℕ} (hkn : k + 1 ≤ n) :
    geomLaw n p (k + 1) * cmF n p (k + 1) = geomLaw n p k * cmH n k := by
  rw [← geomLaw_succ_mul hkn]
  unfold cmF cmH
  push_cast
  ring

/-- **Lemma 4.5** (aperiodicity bound): `g_k = 1 - f_k - h_k ≥ (n² + 1) / (2n²)` for
`p ≤ 1` and `1 ≤ k ≤ n`. -/
theorem lemma45_diag_bound (hn : 0 < n) {p : ℝ} (hp1 : p ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) ^ 2 + 1) / (2 * n ^ 2) ≤ 1 - cmF n p k - cmH n k := by
  unfold cmF cmH
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  rw [div_le_iff₀ (by positivity)]
  have e : (1 - p * ((n : ℝ) - k + 1) * ((k : ℝ) - 1) / n ^ 2 - (k : ℝ) * ((n : ℝ) - k) / n ^ 2) *
      (2 * n ^ 2) = 2 * n ^ 2 - 2 * p * ((n : ℝ) - k + 1) * ((k : ℝ) - 1) -
        2 * (k : ℝ) * ((n : ℝ) - k) := by
    field_simp
  rw [e]
  have h1 : 0 ≤ ((n : ℝ) - k + 1) * ((k : ℝ) - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hp1 h1, sq_nonneg ((n : ℝ) + 1 - 2 * k)]

end OrderStatisticsPP
