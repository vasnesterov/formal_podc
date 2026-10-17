import Mathlib

/-!
# The non-square case in the proof of Theorem 3.7

For `n` not a perfect square the paper (proof of Theorem 3.7) uses, with `s = ⌊√n⌋`,
`V₁ = {1, …, s²}`, `V₂ = {n - s² + 1, …, n}`, `V₃ = {1, …, n - s²} ∪ {s² + 1, …, n}`,
and claims:

1. every message whose sender and receiver are neither both in `V₁` nor both in `V₂` goes from
   `V₁ ∩ V₃` to `V₂ ∩ V₃` or vice versa;
2. Corollary 3.4 applies to `W = V₁ ∩ V₃` and `W = V₂ ∩ V₃` (it requires `|W| ≤ √n` and that
   every node of `W` holds exactly `f|W|` messages, `f = ⌊n/|W|⌋`).

Claim 1 fails (only) for `n = 3`; the size condition of Corollary 3.4 fails e.g. for `n = 8`, and the
load condition fails e.g. for `n = 7`. These are gaps in the proof only: `theorem_3_7` proves the
theorem for all `n` by a different reduction (simulation of a virtual square clique).
-/

namespace CongestedCliqueRouting.PaperGaps

open Finset

/-- `⌊√n⌋`, by bounded search (kernel-computable). -/
def s (n : ℕ) : ℕ := ((List.range (n + 1)).filter fun k => k * k ≤ n).length - 1

lemma s_eq_sqrt (n : ℕ) (hn : n ≤ 40) : s n = Nat.sqrt n := by
  interval_cases n <;> decide +kernel

def V1 (n : ℕ) : Finset ℕ := Icc 1 (s n ^ 2)
def V2 (n : ℕ) : Finset ℕ := Icc (n - s n ^ 2 + 1) n
def V3 (n : ℕ) : Finset ℕ := Icc 1 (n - s n ^ 2) ∪ Icc (s n ^ 2 + 1) n

/-- Claim 1 of the non-square case, for a given `n`. -/
def CoverClaim (n : ℕ) : Prop :=
  ∀ i ∈ Icc 1 n, ∀ k ∈ Icc 1 n, ¬ (i ∈ V1 n ∧ k ∈ V1 n) → ¬ (i ∈ V2 n ∧ k ∈ V2 n) →
    (i ∈ V1 n ∩ V3 n ∧ k ∈ V2 n ∩ V3 n) ∨ (i ∈ V2 n ∩ V3 n ∧ k ∈ V1 n ∩ V3 n)

instance (n : ℕ) : Decidable (CoverClaim n) := by unfold CoverClaim; infer_instance

/-- For `n = 3` the message from node `2` to itself is handled by none of the three
sub-procedures. -/
theorem coverClaim_false_three : ¬ CoverClaim 3 := by decide +kernel

/-- The claim does hold for the other small `n` (checked up to 40). -/
theorem coverClaim_small : ∀ n ∈ Icc 1 40, n ≠ 3 → CoverClaim n := by decide +kernel

/-- For `n = 8`, `W = V₁ ∩ V₃` has `4` nodes but `4² > 8`, so Corollary 3.4 (`|W| ≤ √n`) does
not apply. -/
theorem cor34_size_fails_eight : (V1 8 ∩ V3 8).card = 4 ∧ 8 < 4 ^ 2 := by decide +kernel

/-- For `n = 7`, `W = V₂ ∩ V₃ = {5, 6, 7}`: if these three nodes send all their `7` messages to
`V₁ ∩ V₃ = {1, 2, 3}` (each node of which then receives `7` messages, as allowed), the `21`
messages cannot be spread over `|W| = 3` nodes with at most `f |W| = ⌊7/3⌋ · 3 = 6` each, as
Corollary 3.4 requires. -/
theorem cor34_load_fails_seven :
    V1 7 ∩ V3 7 = {1, 2, 3} ∧ V2 7 ∩ V3 7 = {5, 6, 7} ∧ 3 * (7 / 3 * 3) < 3 * 7 := by
  decide +kernel

end CongestedCliqueRouting.PaperGaps
