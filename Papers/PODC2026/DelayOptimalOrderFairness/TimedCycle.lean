import Papers.PODC2026.DelayOptimalOrderFairness.Defs

/-!
# Theorem 3.1: timed-cycle weakness of vote-only fairness

Cai, Goharshady. *Brief Announcement: Delay-Optimal Transaction Order Fairness.* PODC 2026, §3.

All `n` nodes are honest and `Δ`-synchronous. With `g = Δ/(n-1)`, node `i` stamps transaction
`j` at `((i + j) mod n) · g - j g/2`. On every step `j → j+1` all nodes but one move forward by
`g/2` (a strict `(n-1)/n`-majority) while the honest receive window drifts left by `g/2`. After `r`
steps the window has moved left by more than `Δ + D`, so every node received `tx_A = r` at least `D`
before `tx_B = 0`, although vote edges lead from `tx_B` back to `tx_A`.

The construction needs `n ≥ 1/(1-φ)` nodes; for a fixed `n` and `φ > 1 - 1/n` no vote cycle exists
at all (`theorem_3_1_fixed_n_false`).
-/

namespace Podc.DelayOptimalOrderFairness

open Finset Relation

private theorem succ_mod_of_ne {a M : ℕ} (hM : 0 < M) (h : (a + 1) % M ≠ 0) :
    (a + 1) % M = a % M + 1 := by
  rw [← Nat.mod_add_mod] at h ⊢
  have := Nat.mod_lt a hM
  rcases Nat.lt_or_ge (a % M + 1) M with h' | h'
  · exact Nat.mod_eq_of_lt h'
  · exfalso; apply h; rw [show a % M + 1 = M by omega, Nat.mod_self]

/-- The drifting rotation profile of Theorem 3.1. -/
noncomputable def driftProfile (n : ℕ) (Δ : ℝ) : Profile (Fin n) ℕ := fun i j =>
  (((i.val + j) % n : ℕ) : ℝ) * (Δ / (n - 1)) - j * (Δ / (n - 1) / 2)

/-- **Theorem 3.1 (Timed-cycle weakness).** For any threshold `φ < 1` (the paper: `φ ∈ (1/2, 1)`),
any time gap `D > 0` and any `Δ_sync > 0`, for all sufficiently many nodes there is a
`Δ_sync`-synchronous arrival profile (all nodes honest) in which every node receives `tx_A` at least
`D` before `tx_B`, yet transactions form a chain of pairwise `φ`-majority (receive-order) edges from
`tx_B` back to `tx_A`; with the unanimous edge `tx_A → tx_B` this is a `φ`-majority cycle. -/
theorem theorem_3_1 {φ D Δ : ℝ} (hφ : φ < 1) (hD : 0 < D) (hΔ : 0 < Δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ (ts : Profile (Fin n) ℕ) (A B : ℕ),
      Synchronous univ Δ ts ∧ (∀ i, ts i A + D ≤ ts i B) ∧
      VotePrec ts φ A B ∧ TransGen (VotePrec ts φ) B A := by
  classical
  refine ⟨max 2 ⌈1 / (1 - φ)⌉₊, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hnφ : φ * n ≤ n - 1 := by
    have h1 : 1 / (1 - φ) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
    rw [div_le_iff₀ (by linarith)] at h1
    linarith
  set g := Δ / (n - 1) with hg
  have hg0 : 0 < g := div_pos hΔ (by linarith)
  have hgn : ((n : ℝ) - 1) * g = Δ := by
    have : (n : ℝ) - 1 ≠ 0 := by linarith
    rw [hg]; field_simp
  set r := ⌈2 * (Δ + D) / g⌉₊ + 1 with hr
  have hrg : Δ + D ≤ r * (g / 2) := by
    have h1 : 2 * (Δ + D) / g ≤ r := by
      rw [hr]; push_cast; linarith [Nat.le_ceil (2 * (Δ + D) / g)]
    rw [div_le_iff₀ hg0] at h1
    linarith
  -- bounds on the rotating offset
  have hoff : ∀ (i : Fin n) (j : ℕ), (0 : ℝ) ≤ (((i.val + j) % n : ℕ) : ℝ) * g ∧
      (((i.val + j) % n : ℕ) : ℝ) * g ≤ Δ := by
    intro i j
    refine ⟨by positivity, ?_⟩
    have : (((i.val + j) % n : ℕ) : ℝ) ≤ n - 1 := by
      have := Nat.mod_lt (i.val + j) (by omega : 0 < n)
      have h' : (i.val + j) % n ≤ n - 1 := by omega
      have := (Nat.cast_le (α := ℝ)).2 h'
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
    rw [← hgn]; exact mul_le_mul_of_nonneg_right this hg0.le
  -- vote edges along the chain
  have hedge : ∀ j : ℕ, VotePrec (driftProfile n Δ) φ j (j + 1) := by
    intro j
    have hsub : univ \ (univ.filter fun i : Fin n => driftProfile n Δ i j < driftProfile n Δ i (j + 1))
        ⊆ univ.filter fun i : Fin n => (i.val + j + 1) % n = 0 := by
      intro i hi
      simp only [mem_sdiff, mem_univ, true_and, mem_filter] at hi ⊢
      by_contra hne
      apply hi
      have := succ_mod_of_ne (a := i.val + j) (by omega) hne
      simp only [driftProfile, ← add_assoc, this]
      push_cast; linarith
    have hone : (univ.filter fun i : Fin n => (i.val + j + 1) % n = 0).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      have : a.val + (j + 1) ≡ b.val + (j + 1) [MOD n] := by
        unfold Nat.ModEq; rw [← add_assoc, ← add_assoc, ha, hb]
      have := Nat.ModEq.add_right_cancel' _ this
      exact Fin.ext (by
        unfold Nat.ModEq at this
        rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this)
    have := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at this
    have hle := card_le_univ (univ.filter fun i : Fin n =>
      driftProfile n Δ i j < driftProfile n Δ i (j + 1))
    rw [Fintype.card_fin] at hle
    have hc : n ≤ (univ.filter fun i : Fin n =>
        driftProfile n Δ i j < driftProfile n Δ i (j + 1)).card + 1 := by omega
    have hc' : (n : ℝ) ≤ (univ.filter fun i : Fin n =>
        driftProfile n Δ i j < driftProfile n Δ i (j + 1)).card + 1 := by exact_mod_cast hc
    show φ * Fintype.card (Fin n) ≤ _
    rw [Fintype.card_fin]; linarith
  have hgap : ∀ i, driftProfile n Δ i r + D ≤ driftProfile n Δ i 0 := by
    intro i
    have h1 := (hoff i r).2
    have h2 := (hoff i 0).1
    simp only [driftProfile, ← hg]
    push_cast
    nlinarith
  refine ⟨driftProfile n Δ, r, 0, ?_, hgap, ?_, ?_⟩
  · intro i _ i' _ j
    have h1 := (hoff i j).2
    have h2 := (hoff i' j).1
    simp only [driftProfile, ← hg]
    linarith
  · have : (univ.filter fun i : Fin n => driftProfile n Δ i r < driftProfile n Δ i 0) = univ :=
      filter_true_of_mem fun i _ => by linarith [hgap i]
    show φ * Fintype.card (Fin n) ≤ _
    rw [this, card_univ]
    nlinarith [(Fintype.card (Fin n)).cast_nonneg (α := ℝ)]
  · have key : ∀ m, TransGen (VotePrec (driftProfile n Δ) φ) 0 (m + 1) := by
      intro m
      induction m with
      | zero => exact .single (hedge 0)
      | succ m ih => exact ih.tail (hedge _)
    exact key _

/-- The vote-only relation is acyclic as soon as every edge needs all `n ≥ 1` nodes. -/
theorem vote_acyclic_of_gt {Node Tx : Type*} [Fintype Node] [Nonempty Node] {φ : ℝ}
    (hφ : (Fintype.card Node : ℝ) - 1 < φ * Fintype.card Node) (ts : Profile Node Tx) :
    ¬ HasCycle (VotePrec ts φ) := by
  classical
  let i₀ : Node := Classical.arbitrary _
  refine not_hasCycle_of_lt (ts i₀) fun x y hxy => ?_
  have hxy' : φ * Fintype.card Node ≤ (univ.filter fun i => ts i x < ts i y).card := by
    simpa [VotePrec] using hxy
  have hall : (univ.filter fun i => ts i x < ts i y) = univ := by
    apply eq_univ_of_card
    have h1 := card_le_univ (univ.filter fun i => ts i x < ts i y)
    have h2 : (Fintype.card Node : ℝ) - 1 < (univ.filter fun i => ts i x < ts i y).card := by
      linarith
    have h3' : (Fintype.card Node : ℝ) < ((univ.filter fun i => ts i x < ts i y).card : ℝ) + 1 := by
      linarith
    have h3 : Fintype.card Node < (univ.filter fun i => ts i x < ts i y).card + 1 := by
      exact_mod_cast h3'
    omega
  have : i₀ ∈ univ.filter fun i => ts i x < ts i y := by rw [hall]; exact mem_univ _
  exact (mem_filter.1 this).2

/-- **Theorem 3.1 needs a growing number of nodes.** For every fixed `n ≥ 1` there is a threshold
`φ ∈ (1/2, 1)` such that no profile whatsoever (synchronous or not) has a cycle of pairwise
`φ`-majority edges. So the theorem's "there is a profile" must include the choice of `n`. -/
theorem theorem_3_1_fixed_n_false (n : ℕ) (hn : 1 ≤ n) (Tx : Type*) :
    ∃ φ : ℝ, 1 / 2 < φ ∧ φ < 1 ∧ ∀ ts : Profile (Fin n) Tx, ¬ HasCycle (VotePrec ts φ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨1 - 1 / (2 * (n + 1)), ?_, ?_, fun ts => vote_acyclic_of_gt ?_ ts⟩
  · have : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  · have : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith
  · rw [Fintype.card_fin]
    have : (n : ℝ) * (1 / (2 * (n + 1))) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; linarith
    nlinarith

end Podc.DelayOptimalOrderFairness
