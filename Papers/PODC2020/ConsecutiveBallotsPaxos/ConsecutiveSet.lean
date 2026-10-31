import Mathlib

/-!
# Consecutive ballots and consecutive sets (Definitions 1–2)

Goldweber, Zhang, Kapritsos, *On the Significance of Consecutive Ballots in Paxos*, PODC 2020
(arXiv:2006.01885).

Ballots are natural numbers. `Consecutive m n` (Definition 1) and `ConsecutiveSet S` (Definition 2)
are stated literally; the main fact used later is that a finite consecutive set contains every
natural number between two of its elements (`ConsecutiveSet.mem_of_le_of_le`), i.e. it is an
interval.
-/

namespace Podc.ConsecutiveBallotsPaxos

/-- Definition 1 of [paper] (Consecutive Pair): `m ≤ n` and no ballot lies strictly between. -/
def Consecutive (m n : ℕ) : Prop := m ≤ n ∧ ¬ ∃ m' : ℕ, m < m' ∧ m' < n

/-- Definition 2 of [paper] (Consecutive Set): every element is the minimum or has a smaller
consecutive element in the set. -/
def ConsecutiveSet (S : Set ℕ) : Prop :=
  ∀ n ∈ S, IsLeast S n ∨ ∃ m ∈ S, m < n ∧ Consecutive m n

lemma consecutive_iff_of_lt {m n : ℕ} (h : m < n) : Consecutive m n ↔ n = m + 1 := by
  constructor
  · rintro ⟨-, h2⟩
    by_contra hne
    exact h2 ⟨m + 1, by omega, by omega⟩
  · rintro rfl
    exact ⟨by omega, fun ⟨m', h1, h2⟩ => by omega⟩

/-- A consecutive set of naturals that is bounded above contains every number between two of its
elements: it is an interval. -/
lemma ConsecutiveSet.mem_of_le_of_le {S : Set ℕ} (hS : ConsecutiveSet S) (hfin : S.Finite)
    {lo hi k : ℕ} (hlo : lo ∈ S) (hhi : hi ∈ S) (h1 : lo ≤ k) (h2 : k ≤ hi) : k ∈ S := by
  by_contra hk
  -- the smallest element of `S` above `k`
  have hne : ({n ∈ hfin.toFinset | k < n}).Nonempty :=
    ⟨hi, by simp only [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hhi, by
      rcases h2.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hhi) hk⟩⟩
  set n := ({n ∈ hfin.toFinset | k < n}).min' hne with hn
  have hnmem := Finset.min'_mem _ hne
  rw [← hn] at hnmem
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hnmem
  have hlo_k : lo < k := lt_of_le_of_ne h1 (by rintro rfl; exact hk hlo)
  rcases hS n hnmem.1 with hl | ⟨m, hm, hmn, hcons⟩
  · have := hl.2 hlo; omega
  · rw [consecutive_iff_of_lt hmn] at hcons
    have hmk : m ≤ k := by
      by_contra hmk
      have : n ≤ m := by
        rw [hn]
        exact Finset.min'_le _ _ (by simp only [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hm, by omega⟩)
      omega
    have : m = k := by omega
    exact hk (this ▸ hm)

/-- A singleton is a consecutive set. -/
lemma consecutiveSet_singleton (i : ℕ) : ConsecutiveSet {i} := by
  intro n hn
  left
  simp only [Set.mem_singleton_iff] at hn
  subst hn
  exact ⟨rfl, fun _ h => le_of_eq h.symm⟩

/-- An integer interval is a consecutive set. -/
lemma consecutiveSet_Icc (a b : ℕ) : ConsecutiveSet (Set.Icc a b) := by
  intro n hn
  by_cases h : n = a
  · subst h; exact Or.inl ⟨hn, fun _ hx => hx.1⟩
  · right
    refine ⟨n - 1, ⟨by simp at hn; omega, by simp at hn; omega⟩, by simp at hn; omega, ?_⟩
    rw [consecutive_iff_of_lt (by simp at hn; omega)]
    simp at hn; omega

/-- The set `{7, 9, 10}` (Table 1) is not consecutive. -/
lemma not_consecutiveSet_7_9_10 : ¬ ConsecutiveSet {7, 9, 10} := by
  intro h
  have := h.mem_of_le_of_le (Set.toFinite _) (lo := 7) (hi := 9) (k := 8) (by simp) (by simp)
    (by norm_num) (by norm_num)
  simp at this

end Podc.ConsecutiveBallotsPaxos
