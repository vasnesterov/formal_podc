import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Finite distributions, dependent rounding (Theorem 3) and the Chernoff bound (Theorem 4)

Bentert, Avin, Schmid, PODC 2026, §3.1. The proof of Theorem 5 uses two results from the
literature:

* **Theorem 3** (dependent rounding, Gandhi–Khuller–Parthasarathy–Srinivasan, JACM 2006,
  Thm 2.3): a matrix with entries in `[0, 1]` and integer row and column sums can be rounded to a
  random `0/1` matrix with the same marginals, the same row/column sums with probability `1`, and
  negatively correlated zeros within every row and every column. We state it as the proposition
  `DependentRounding n`; it is proved in `DependentRounding.lean` (`dependentRounding`).
* **Theorem 4** (Panconesi–Srinivasan, in the form of Gandhi et al., Thm 3.1): the Chernoff lower
  tail `P(∑ aᵢXᵢ ≤ μ(1-δ)) ≤ exp(-μδ²/2)` for `0/1` variables whose zeros are negatively
  correlated. Stated as `NegCorrChernoff`; proved in `Chernoff.lean` (`negCorrChernoff`).

All randomness lives on finite sample spaces, so a distribution is a non-negative weight function
summing to `1` (`FinDist`) and probabilities are finite sums.
-/

namespace Podc.DemandAwareThroughput

open Finset

/-- A probability distribution on a finite type, as a weight function. -/
-- CSLib candidate (with `prob`, `NegCorrChernoff`, `DependentRounding`)
structure FinDist (Ω : Type) [Fintype Ω] where
  /-- The probability of each outcome. -/
  w : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ w ω
  sum_eq_one : ∑ ω, w ω = 1

namespace FinDist

variable {Ω : Type} [Fintype Ω] (μ : FinDist Ω)

/-- The probability of an event. -/
noncomputable def prob (E : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if E ω then μ.w ω else 0

end FinDist

/-- The `0/1` value of a Boolean as a real number. -/
def bval (b : Bool) : ℝ := if b then 1 else 0

/-- **Theorem 3** of the paper (dependent rounding, [Gandhi et al., Theorem 2.3], special case of
`n × n` matrices with integer row and column sums). Proved as `dependentRounding`. -/
def DependentRounding (n : ℕ) : Prop :=
  ∀ α : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ α i j ∧ α i j ≤ 1) →
    (∀ i, ∃ s : ℤ, ∑ j, α i j = s) → (∀ j, ∃ t : ℤ, ∑ i, α i j = t) →
    ∃ μ : FinDist (Fin n → Fin n → Bool),
      -- (1) `β i j = 1` with probability exactly `α i j`
      (∀ i j, μ.prob (fun β => β i j = true) = α i j) ∧
      -- (2) row and column sums are preserved with probability `1`
      (∀ β, μ.w β ≠ 0 →
        (∀ i, ∑ j, bval (β i j) = ∑ j, α i j) ∧ (∀ j, ∑ i, bval (β i j) = ∑ i, α i j)) ∧
      -- (3) negative correlation of zeros within a row
      (∀ i (S : Finset (Fin n)),
        μ.prob (fun β => ∀ j ∈ S, β i j = false) ≤ ∏ j ∈ S, (1 - α i j)) ∧
      -- (4) negative correlation of zeros within a column
      (∀ j (S : Finset (Fin n)),
        μ.prob (fun β => ∀ i ∈ S, β i j = false) ≤ ∏ i ∈ S, (1 - α i j))

/-- **Theorem 4** of the paper (Chernoff lower tail under negative correlation of zeros,
[Panconesi–Srinivasan], [Gandhi et al., Theorem 3.1]). The index set `[t]` of the paper is an
arbitrary finite type `ι`. -/
def NegCorrChernoff : Prop :=
  ∀ (Ω ι : Type) [Fintype Ω] [Fintype ι] (μ : FinDist Ω) (X : ι → Ω → Bool) (a x : ι → ℝ),
    (∀ k, 0 ≤ a k ∧ a k ≤ 1) → (∀ k, 0 ≤ x k ∧ x k ≤ 1) →
    (∀ k, μ.prob (fun ω => X k ω = true) = x k) →
    (∀ S : Finset ι, μ.prob (fun ω => ∀ k ∈ S, X k ω = false) ≤ ∏ k ∈ S, (1 - x k)) →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      μ.prob (fun ω => ∑ k, a k * bval (X k ω) ≤ (∑ k, a k * x k) * (1 - δ)) ≤
        Real.exp (-((∑ k, a k * x k) * δ ^ 2 / 2))

end Podc.DemandAwareThroughput
