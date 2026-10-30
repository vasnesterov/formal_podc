import Mathlib

/-!
# Set-sequences and sequence-number functions (Sections 2 and 4.2)

For a running-time bound `f : ℕ^ℓ → ℝ` (vectors of guesses are functions `Fin ℓ → ℕ`, ordered
coordinatewise: `y ≤ x` means "`x` dominates `y`"):

* `ModeratelySlow s`: `s` is non-decreasing and `s (2 i) ≤ α s i` for all `i ≠ 1`, for some positive
  integer `α` (Section 2).
* `SetSeq f`: a set-sequence for `f`: finite sets `S i` of guess vectors such that every `y` with
  `f y ≤ i` is dominated by some `x ∈ S i`.
* `SetSeq.Bounded S c`: `c > 0` and `f x ≤ c i` for every `x ∈ S i`.
* `IsSeqNumber f s`: `s` is a sequence-number function for `f`: `s` is moderately slow and there is a
  bounded set-sequence with `|S i| ≤ s i`.
-/

namespace Podc.UniformLocalAlgorithms

/-- A function `s : ℕ → ℕ` is *moderately slow* if it is non-decreasing and there is a positive
integer `α` with `α · s(i) ≥ s(2i)` for every `i ≠ 1` (Section 2). -/
def ModeratelySlow (s : ℕ → ℕ) : Prop :=
  Monotone s ∧ ∃ a : ℕ, 0 < a ∧ ∀ i, i ≠ 1 → s (2 * i) ≤ a * s i

/-- A set-sequence for `f` (Section 4.2): for every `i`, a finite set `S i` of vectors such that
every vector `y` with `f y ≤ i` is dominated by a vector of `S i`. -/
structure SetSeq {ℓ : ℕ} (f : (Fin ℓ → ℕ) → ℝ) where
  /-- The sets. -/
  S : ℕ → Finset (Fin ℓ → ℕ)
  /-- Domination. -/
  dom : ∀ (i : ℕ) (y : Fin ℓ → ℕ), f y ≤ i → ∃ x ∈ S i, y ≤ x

/-- The set-sequence is bounded with bounding constant `c`: `f x ≤ c · i` for all `x ∈ S i`. -/
def SetSeq.Bounded {ℓ : ℕ} {f : (Fin ℓ → ℕ) → ℝ} (S : SetSeq f) (c : ℝ) : Prop :=
  0 < c ∧ ∀ (i : ℕ), ∀ x ∈ S.S i, f x ≤ c * i

/-- `s` is a sequence-number function for `f` (Section 4.2): `s` is moderately slow, and some
bounded set-sequence for `f` satisfies `|S i| ≤ s i` for all `i`. -/
def IsSeqNumber {ℓ : ℕ} (f : (Fin ℓ → ℕ) → ℝ) (s : ℕ → ℕ) : Prop :=
  ModeratelySlow s ∧ ∃ (S : SetSeq f) (c : ℝ), S.Bounded c ∧ ∀ i, (S.S i).card ≤ s i

end Podc.UniformLocalAlgorithms
