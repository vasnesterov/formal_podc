import Mathlib

/-!
# The complexity recurrence in the proof of Lemma 3.5 does not give `O(R i)`

The proof of Lemma 3.5 bounds the commitment round `T_i` of level `i` by
`T_i ≤ max(O(R·i), T_{i-1}) + O(R·i)` and concludes "by induction, `T_i ∈ O(R·i)`". This inference
is invalid: `T_i = i (i + 1) / 2` (take `R = 1` and both constants `1`) satisfies the recurrence
with equality and is not `O(i)`. The statement of Lemma 3.5 is nevertheless true; see `ESColor.lean`
for the repaired colouring step and `Lemma35.lean` for the proof.
-/

namespace Podc.RendezvousLabeledLine

/-- `T i = 0 + 1 + ⋯ + i`. -/
def recT : ℕ → ℕ
  | 0 => 0
  | i + 1 => recT i + (i + 1)

lemma two_mul_recT (i : ℕ) : 2 * recT i = i * (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [recT]; rw [mul_add, ih]; ring

/-- The recurrence of the proof of Lemma 3.5 has superlinear solutions. -/
theorem lemma_3_5_recurrence_gap :
    (∀ i, recT (i + 1) ≤ max (i + 1) (recT i) + (i + 1)) ∧ ¬ ∃ C, ∀ i, recT i ≤ C * i := by
  refine ⟨fun i => by simp only [recT]; omega, ?_⟩
  rintro ⟨C, hC⟩
  have h1 := hC (2 * C + 1)
  have h2 := two_mul_recT (2 * C + 1)
  nlinarith

end Podc.RendezvousLabeledLine
