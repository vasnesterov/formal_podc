import Papers.PODC2023.ValidityConsensus.LowerBound
import Papers.PODC2023.ValidityConsensus.Similarity
import Cslib.Computability.Distributed.Byzantine.PartialSync.BinaryConsensus

/-!
# Non-vacuity of Theorems 3 and 4 for `t ≥ 1`

The hypotheses of Theorems 3 and 4 (an algorithm solving consensus with a non-trivial validity
property) are satisfiable with `t ≥ 1`: the verified protocol `Cslib.Byzantine.PartialSync.Binary.algo`
solves binary consensus with strong validity in the partially synchronous model whenever
`n ≥ 7t + 1`. Consequently Theorem 4 applies to it, and Theorem 3 gives `C_S` for strong validity.
-/

namespace ValidityConsensus

open Cslib.Byzantine.PartialSync Cslib.Byzantine.PartialSync.Binary

variable {P : Type} [Fintype P] [DecidableEq P] {t : ℕ}

/-- Theorem 4 applied to a concrete protocol: for `n ≥ 7t + 1`, `t ≥ 1`, the verified binary
consensus protocol has a valid synchronous run in which correct processes send at least
`⌈t/2⌉(⌈t/2⌉+1)` messages to other processes. -/
theorem binary_message_lower_bound (ht : 0 < t) (hn : 7 * t + 1 ≤ Fintype.card P) (δ : ℕ) :
    ∃ R : Run P (ℕ × Bool) Bool, R.Valid t δ ∧ R.gst = 0 ∧ ∃ N,
      ((t + 1) / 2) * ((t + 1) / 2 + 1) ≤
        R.msgsUpTo ((algo t (rotLeader (by omega))).compile (δ + 1)) N :=
  message_lower_bound (solvesConsensus hn (rotLeader_surj (by omega)) δ)
    strongValidity_not_trivial ht (by omega)

/-- The hypotheses of Theorem 4 are satisfiable with `t ≥ 1`: some non-trivial validity property
is solvable (binary strong validity, `n ≥ 7t + 1`). -/
theorem exists_nontrivial_solvable (hn : 7 * t + 1 ≤ Fintype.card P) (δ : ℕ) :
    ∃ val : ValidityProperty P Bool Bool, ¬ val.Trivial t ∧ val.Solvable t δ :=
  ⟨strongValidity, strongValidity_not_trivial, strongValidity_solvable hn δ⟩

/-- Theorem 3 for binary strong validity (`n ≥ 7t + 1`). -/
theorem strongValidity_similarityCondition (hn : 7 * t + 1 ≤ Fintype.card P) (δ : ℕ) :
    SimilarityCondition t (strongValidity (P := P)) :=
  similarityCondition_of_solvable (strongValidity_solvable hn δ) (by omega)

end ValidityConsensus
