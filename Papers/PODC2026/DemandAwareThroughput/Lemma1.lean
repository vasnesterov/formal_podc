import Papers.PODC2026.DemandAwareThroughput.DependentRounding
import Papers.PODC2026.DemandAwareThroughput.Weak

/-!
# Lemma 1 and Theorem 6

Bentert, Avin, Schmid, PODC 2026, §4, Lemma 1: a matrix `x` with entries in `[0, 1]` and integer
row and column sums can be rounded to a `0/1` matrix `b` with the same line sums such that
`∑ x_ij b_ij ≥ X²/n²`, where `X = ∑ x_ij`.

As in the paper we move along a cycle direction (`exists_circulation`), in the sign that does not
decrease `∑ a_ij c_ij`, until a new entry becomes integral; this proves `∑ a·b ≥ ∑ a·x` for any
fixed weights `a` (`exists_rounding_ge`). With `a = x` and Cauchy–Schwarz,
`∑ x² ≥ X²/n²`. Theorem 6 then follows (`theorem_6`).
-/

namespace Podc.DemandAwareThroughput

open Finset DepRound

variable {n : ℕ}

-- CSLib candidate
/-- Rounding without decreasing a linear objective: for weights `a` and `c ∈ [0,1]^{n×n}` with
integer line sums there is a `0/1` matrix `b` with the same line sums and
`∑ a_ij b_ij ≥ ∑ a_ij c_ij`. -/
theorem exists_rounding_ge (a : Fin n → Fin n → ℝ) :
    ∀ (k : ℕ) (c : Fin n → Fin n → ℝ), (frac c).card = k → (∀ i j, 0 ≤ c i j ∧ c i j ≤ 1) →
      (∀ i, ∃ s : ℤ, ∑ j, c i j = s) → (∀ j, ∃ t : ℤ, ∑ i, c i j = t) →
      ∃ b : Fin n → Fin n → Bool,
        (∀ i, ∑ j, bval (b i j) = ∑ j, c i j) ∧ (∀ j, ∑ i, bval (b i j) = ∑ i, c i j) ∧
        ∑ i, ∑ j, a i j * c i j ≤ ∑ i, ∑ j, a i j * bval (b i j) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hk h01 hr hc
  have hnonint : ∀ i j, (¬ ∃ z : ℤ, c i j = z) ↔ (0 < c i j ∧ c i j < 1) := by
    intro i j
    constructor
    · intro h
      exact ⟨lt_of_le_of_ne (h01 i j).1 fun h0 => h ⟨0, by simp [h0]⟩,
        lt_of_le_of_ne (h01 i j).2 fun h1 => h ⟨1, by simp [h1]⟩⟩
    · rintro ⟨h0, h1⟩ ⟨z, hz⟩
      rw [hz] at h0 h1
      have h0' : (0 : ℤ) < z := by exact_mod_cast h0
      have h1' : z < (1 : ℤ) := by exact_mod_cast h1
      omega
  by_cases hF : ∃ i j, 0 < c i j ∧ c i j < 1
  · obtain ⟨i₀, j₀, hij₀⟩ := hF
    obtain ⟨Δ, hΔne, hΔfr, hΔr, hΔc⟩ :=
      exists_circulation c hr hc ⟨i₀, j₀, (hnonint i₀ j₀).2 hij₀⟩
    -- choose the sign of the direction that does not decrease the objective
    obtain ⟨D, hDfr, hDr, hDc, hDobj, hDne⟩ : ∃ D : Fin n → Fin n → ℝ,
        (∀ i j, D i j ≠ 0 → 0 < c i j ∧ c i j < 1) ∧ (∀ i, ∑ j, D i j = 0) ∧
        (∀ j, ∑ i, D i j = 0) ∧ 0 ≤ ∑ i, ∑ j, a i j * D i j ∧ ∃ i j, D i j ≠ 0 := by
      have hex : ∃ i j, Δ i j ≠ 0 := by
        by_contra h0; push Not at h0; exact hΔne (funext fun i => funext fun j => h0 i j)
      rcases le_total 0 (∑ i, ∑ j, a i j * Δ i j) with h | h
      · exact ⟨Δ, fun i j hh => (hnonint i j).1 (hΔfr i j hh), hΔr, hΔc, h, hex⟩
      · refine ⟨fun i j => -Δ i j, fun i j hh => (hnonint i j).1 (hΔfr i j (neg_ne_zero.1 hh)),
          fun i => by simp [sum_neg_distrib, hΔr i], fun j => by simp [sum_neg_distrib, hΔc j],
          ?_, let ⟨i, j, hh⟩ := hex; ⟨i, j, neg_ne_zero.2 hh⟩⟩
        simp only [mul_neg, sum_neg_distrib]; linarith
    obtain ⟨t, ht, ht01, i', j', hD', hend⟩ := exists_step c D h01 hDfr hDne
    set c' : Fin n → Fin n → ℝ := fun i j => c i j + t * D i j with hc'
    have hlt : (frac c').card < k := by
      rw [← hk]
      refine card_lt_card ((ssubset_iff_of_subset ?_).2 ⟨(i', j'), ?_, ?_⟩)
      · intro p hp
        rw [mem_frac] at hp ⊢
        by_cases hDp : D p.1 p.2 = 0
        · simpa [c', hDp] using hp
        · exact hDfr _ _ hDp
      · exact mem_frac.2 (hDfr _ _ hD')
      · rw [mem_frac]; rcases hend with h | h <;> simp [c', h]
    have hrow' : ∀ i, ∑ j, c' i j = ∑ j, c i j := fun i => by
      simp only [c', sum_add_distrib, ← mul_sum, hDr i, mul_zero, add_zero]
    have hcol' : ∀ j, ∑ i, c' i j = ∑ i, c i j := fun j => by
      simp only [c', sum_add_distrib, ← mul_sum, hDc j, mul_zero, add_zero]
    obtain ⟨b, hbr, hbc, hbo⟩ := ih _ hlt c' rfl ht01
      (fun i => by rw [hrow' i]; exact hr i) (fun j => by rw [hcol' j]; exact hc j)
    refine ⟨b, fun i => by rw [hbr i, hrow' i], fun j => by rw [hbc j, hcol' j], le_trans ?_ hbo⟩
    have : ∑ i, ∑ j, a i j * c' i j =
        ∑ i, ∑ j, a i j * c i j + t * ∑ i, ∑ j, a i j * D i j := by
      simp only [c', mul_add, sum_add_distrib, mul_sum]
      congr 1
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [this]
    nlinarith
  · -- `c` is a `0/1` matrix
    push Not at hF
    have h01' : ∀ i j, c i j = 0 ∨ c i j = 1 := by
      intro i j
      rcases eq_or_lt_of_le (h01 i j).1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (le_antisymm (h01 i j).2 (not_lt.1 fun h' => absurd (hF i j h) (not_le.2 h')))
    refine ⟨fun i j => decide (c i j = 1), ?_, ?_, le_of_eq ?_⟩
    all_goals
      have e : ∀ i j, bval (decide (c i j = 1)) = c i j := by
        intro i j; unfold bval
        rcases h01' i j with h | h <;> simp [h]
    · intro i; simp only [e]
    · intro j; simp only [e]
    · simp only [e]

/-- **Lemma 1** of the paper. -/
theorem lemma_1 (n : ℕ) : Lemma1 n := by
  intro x hx hr hc
  obtain ⟨b, hbr, hbc, hbo⟩ := exists_rounding_ge x _ x rfl hx hr hc
  refine ⟨b, hbr, hbc, le_trans ?_ hbo⟩
  -- Cauchy–Schwarz: `(∑ x)² ≤ n² ∑ x²`
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hn2]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n × Fin n))
    (fun p => x p.1 p.2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at cs
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product] at cs
  push_cast at cs
  simp only [← sq]
  nlinarith [cs]

/-- **Theorem 6.** For `n ≥ 1`, `κ ≤ (7n-4)/(8n-4)` and every doubly stochastic `n × n` matrix
`M`, `(M, κ)` is a yes-instance of Demand-Aware Weak Direct Throughput. -/
theorem theorem_6 (hn : 1 ≤ n) {κ : ℝ} (hκ : κ ≤ (7 * n - 4) / (8 * n - 4))
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    DAWeakDirectThroughput M κ :=
  theorem_6_of_lemma1 (lemma_1 n) hn hκ hM

end Podc.DemandAwareThroughput
