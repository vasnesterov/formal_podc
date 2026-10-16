import Mathlib

/-!
# Staircase sums for the one-shot lower bound

`stair K s = ∑_{c=1}^{s} (K - c)` (truncated subtraction) is the number of cells below the
"stepped diagonal" of height `K - 1` in the first `s` columns of the grid of Section 4 of the
paper. A family of counts in which every nonempty set `S` contains an element `r` with
`f r + |S| ≤ K` (a *sparse* family, i.e. no `|S|` columns all reach the diagonal) has
`∑_{r ∈ S} f r ≤ stair K |S|` (`sum_le_stair`).
-/

namespace Cslib.SharedMemory.Timestamp

/-- `stair K s = ∑_{c=1}^{s} (K - c)`. -/
def stair (K s : ℕ) : ℕ := ∑ c ∈ Finset.range s, (K - (c + 1))

@[simp] lemma stair_zero (K : ℕ) : stair K 0 = 0 := by simp [stair]

lemma stair_succ (K s : ℕ) : stair K (s + 1) = stair K s + (K - (s + 1)) := by
  simp [stair, Finset.sum_range_succ]

lemma stair_add (m j k : ℕ) : stair m (j + k) = stair m j + stair (m - j) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, stair_succ, ih, stair_succ]
    have : m - (j + k + 1) = m - j - (k + 1) := by omega
    rw [this]; ring

lemma stair_mono_left {K K' : ℕ} (h : K ≤ K') (s : ℕ) : stair K s ≤ stair K' s :=
  Finset.sum_le_sum fun c _ => by omega

lemma stair_mono_right (K : ℕ) {s s' : ℕ} (h : s ≤ s') : stair K s ≤ stair K s' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [stair_add]; omega

lemma stair_pred_add_one {T s : ℕ} (hT : 2 ≤ T) (hs : 1 ≤ s) : stair (T - 1) s + 1 ≤ stair T s := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with rfl | hs'
    · simp [stair_succ]; omega
    · have := ih hs'
      rw [stair_succ, stair_succ]; omega

lemma stair_pred_lt (M : ℕ) (hM : 2 ≤ M) : stair (M - 1) M < stair M M := by
  have := stair_pred_add_one (T := M) (s := M) hM (by omega); omega

lemma two_mul_stair_self (m : ℕ) : 2 * stair m m = m * (m - 1) := by
  have key : ∀ k, k ≤ m → 2 * stair m k + (m - k) * (m - k - 1) = m * (m - 1) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have := ih (by omega)
      rw [stair_succ]
      obtain ⟨d, hd⟩ : ∃ d, m = k + 1 + d := ⟨m - (k + 1), by omega⟩
      subst hd
      have e1 : k + 1 + d - k = d + 1 := by omega
      have e2 : k + 1 + d - (k + 1) = d := by omega
      rw [e1] at this; rw [e2]
      simp only [Nat.add_sub_cancel] at this ⊢
      cases d with
      | zero => simp at this ⊢; linarith
      | succ d =>
        simp only [Nat.add_sub_cancel] at this ⊢
        nlinarith
  simpa using key m le_rfl

/-- `⌊√(2n)⌋(⌊√(2n)⌋ - 1)/2 + 2 ≤ n` for `n ≥ 3`. -/
lemma stair_sqrt_le (n : ℕ) (hn : 3 ≤ n) : stair (Nat.sqrt (2 * n)) (Nat.sqrt (2 * n)) + 2 ≤ n := by
  set m := Nat.sqrt (2 * n)
  have h1 : m * m ≤ 2 * n := Nat.sqrt_le (2 * n)
  have h2 := two_mul_stair_self m
  have hm2 : 2 ≤ m := by
    rw [Nat.le_sqrt]; omega
  rcases Nat.lt_or_ge m 4 with h | h
  · interval_cases m
    · simp [stair, Finset.sum_range_succ]; omega
    · simp [stair, Finset.sum_range_succ]; omega
  · have : m * (m - 1) + 4 ≤ 2 * n := by
      obtain ⟨k, hk⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [hk] at h1 ⊢
      have : k + 4 - 1 = k + 3 := by omega
      rw [this]; nlinarith
    omega

/-- **Sparse families are bounded by the staircase.** -/
lemma sum_le_stair {α : Type*} [DecidableEq α] (D : Finset α) (f : α → ℕ) (K : ℕ)
    (h : ∀ S ⊆ D, S.Nonempty → ∃ r ∈ S, f r + S.card ≤ K) :
    ∀ S ⊆ D, ∑ r ∈ S, f r ≤ stair K S.card := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨r, hr, hfr⟩ := h S hS hne
      have hlt : S.erase r ⊂ S := Finset.erase_ssubset hr
      have h1 := ih _ hlt ((Finset.erase_subset r S).trans hS)
      have hc : (S.erase r).card + 1 = S.card := Finset.card_erase_add_one hr
      rw [← Finset.add_sum_erase S f hr, ← hc, stair_succ]
      omega

end Cslib.SharedMemory.Timestamp
