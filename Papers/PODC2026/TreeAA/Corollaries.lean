import Papers.PODC2026.TreeAA.Protocol
import Papers.PODC2026.TreeAA.Gradecast

/-!
# Theorem 5 with the verified 3-round gradecast (towards Corollary 2)

Instantiating the gradecast black box of Theorem 5 with the Ben-Or–Dolev–Hoch gradecast
(`bdhGradecast`, Theorem 4, verified in `Gradecast.lean`): for `t < n/3`, `TreeAA` achieves AA on any
tree within `3 + R_RealAA(D(T), 1)` rounds, given only a RealAA black box (unauthenticated setting).
With Theorem 2's bound on `R_RealAA` (whose contraction Lemma 16 is cited) this is Corollary 2.
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

variable {P V : Type} [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
  {T : SimpleGraph V} (hT : T.IsTree) (r : V) {M₂ : Type}

/-- **Theorem 5 + Theorem 4.** For `3t < n`, `TreeAA` built from the BDH gradecast and any RealAA
protocol (Definition 1, `ε = 1`, within `R` rounds for `D(T)`-close inputs) achieves AA on the tree
`T` within `3 + R` rounds against `t` Byzantine parties, without signatures. -/
theorem treeAA_bdh_solves {t R : ℕ} (ht : 3 * t < Fintype.card P) (realAA : Protocol P ℝ M₂ ℝ)
    (hreal : SolvesAuthWithin ⊤ realAA (Auth.none P M₂) (atMost t) (Close (T.diam : ℝ))
      (RealAA 1) R) :
    SolvesAuthWithin ⊤ (treeAA hT r t 3 (bdhGradecast (W := List V) t) realAA)
      (treeAuth (Auth.none P (List V)) (Auth.none P M₂)) (atMost t) noPre (GraphAA T) (3 + R) :=
  (treeAA_solves hT r (by omega) _ _ (fun _ => Protocol.unforging_none _)
    (fun s => bdhGradecast_solves ht s) _ _ (Protocol.unforging_none _) hreal).2

end TreeAA
