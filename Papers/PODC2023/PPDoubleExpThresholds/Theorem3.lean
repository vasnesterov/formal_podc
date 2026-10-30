import Papers.PODC2023.PPDoubleExpThresholds.WellFormed

/-!
# Theorem 3: a succinct population program for `x ≥ k`, `k ≥ 2^(2^(n-1))`
-/

namespace Podc.PPDoubleExpThresholds

open Program Finset

/-- The program with `n` levels decides `x ≥ k` for `k = 2 ∑ᵢ₌₁ⁿ Nᵢ` (proof of Theorem 3, from
Lemma 4 and the existence of good configurations of every size). -/
theorem prog_decides (n : ℕ) : (prog n).Decides fun m => decide (S n ≤ m) := by
  refine decides_of_restart (wellFormed n) _ (fun m OF => ?_) (fun C OF s hs hnr => ?_)
  · obtain ⟨C, hC, h | ⟨-, J, hJ, hJn, hL, hE⟩⟩ := exists_good (n := n) m
    · exact ⟨C, hC, (lemma_4b h.2 OF).1⟩
    · exact ⟨C, hC, (lemma_4a hJ hJn hL hE OF).1⟩
  · by_cases hg : Good n C
    · rcases hg with hP | ⟨J, hJ, hJn, hL, hE⟩
      · obtain ⟨s', h1, h2⟩ := (lemma_4b hP OF).2 s hs hnr
        exact ⟨s', h1, fun s'' h => by rw [h2 s'' h, decide_eq_true (S_le_total hP)]⟩
      · obtain ⟨s', h1, h2⟩ := (lemma_4a hJ hJn hL hE OF).2 s hs
        exact ⟨s', h1, fun s'' h => by
          rw [h2 s'' h, decide_eq_false (Nat.not_le.2 (total_lt_S hJ hJn hL hE))]⟩
    · exact absurd (lemma_4c hg OF s hs) hnr

theorem N_ge {i : ℕ} (hi : 1 ≤ i) : 2 ^ 2 ^ (i - 1) ≤ N i + 1 := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi'
    · simp [N]
    · have := ih hi'
      rw [N_succ, show i + 1 - 1 = (i - 1) + 1 by omega, pow_succ, pow_mul, sq]
      have := Nat.mul_le_mul this this
      nlinarith

/-- The threshold is doubly exponential: `k ≥ 2^(2^(n-1))` for `n ≥ 1`. -/
theorem S_ge {n : ℕ} (hn : 1 ≤ n) : 2 ^ 2 ^ (n - 1) ≤ S n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := N_ge (i := m + 1) (by omega)
  have h2 := N_pos (i := m + 1) (by omega)
  rw [S_succ]; omega

/-- **Theorem 3** of [Czerner, PODC 2023]: for every `n ≥ 1`, the population program of Section 6
(with `4n + 1` registers) is well formed, has size `O(n)` and decides `x ≥ k` for some
`k ≥ 2^(2^(n-1))`. -/
theorem theorem_3 (n : ℕ) (hn : 1 ≤ n) : ∃ k, 2 ^ 2 ^ (n - 1) ≤ k ∧
    (prog n).WellFormed ∧ (prog n).Decides (fun m => decide (k ≤ m)) ∧
    Fintype.card (Reg n) = 4 * n + 1 ∧ (prog n).size ≤ 363 * n + 108 :=
  ⟨S n, S_ge hn, wellFormed n, prog_decides n, card_reg n, size_le⟩

/-- The proof of Theorem 3 claims `k = 2 ∑ᵢ Nᵢ ≥ 2^(2^n)`; this is false (e.g. `k = 2 < 4` for
`n = 1`, `k = 10 < 16` for `n = 2`). The statement's bound `2^(2^(n-1))` holds (`S_ge`). -/
theorem S_lt_claim : S 1 < 2 ^ 2 ^ 1 ∧ S 2 < 2 ^ 2 ^ 2 ∧ S 3 < 2 ^ 2 ^ 3 := by
  simp [S, Finset.sum_range_succ, N]

end Podc.PPDoubleExpThresholds
