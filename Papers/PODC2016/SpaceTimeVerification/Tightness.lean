import Papers.PODC2016.SpaceTimeVerification.LowerBound
import Papers.PODC2016.SpaceTimeVerification.AcyclicUpper

/-!
# Theorems 7 and 8 together: the tradeoff for acyclicity is tight

For every `t ≥ 2`, `t`-round verification of acyclicity on connected graphs needs and admits labels
of `Θ(log n / t)` bits: Theorem 8 gives `5 + ⌈⌈log₂ n⌉ / t⌉` bits, and Theorem 7 shows that any
label-length bound `L n` satisfies `log₂(⌊n/(2t+2)⌋ - 1) < (2t+2)(L n + 1)`.
-/

namespace Podc.SpaceTimeVerification

/-- Theorems 7 and 8 of [OPR]: tight space-time tradeoff for `acyclic`. -/
theorem acyclic_tradeoff (t : ℕ) (ht : 2 ≤ t) :
    (∃ S : TPLS Unit (List Bool) ConnF AcycP t,
        S.CostLE List.length fun n => 5 + (Nat.clog 2 n + t - 1) / t) ∧
      ∀ (S : TPLS Unit (List Bool) ConnF AcycP t) (L : ℕ → ℕ), S.CostLE List.length L →
        ∀ n, Nat.log 2 (n / (2 * t + 2) - 1) < (2 * t + 2) * (L n + 1) :=
  ⟨theorem8_bits t ht, fun S L hS n => (theorem_7 (by omega) S L hS n).2⟩

end Podc.SpaceTimeVerification
