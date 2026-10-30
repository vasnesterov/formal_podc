import Papers.PODC2022.BindingCrusaderAgreement.BCAByz
import Papers.PODC2022.BindingCrusaderAgreement.GBCAByz
import Papers.PODC2022.BindingCrusaderAgreement.GBCACrash

/-!
# Non-vacuity

Fair executions exist for each of the four protocols (`Cslib.Byzantine.AsyncBroadcast.exists_fair`,
a round robin without corruptions), and in them every party decides. In particular the
hypotheses of the binding theorems (a reachable state with a decision) are satisfiable, and the
fairness assumption of the termination theorems is not contradictory.
-/

namespace Podc.BindingCrusaderAgreement

open Cslib.Byzantine.AsyncBroadcast

variable {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} (x : P → Bool)

theorem Alg4.exists_fair_all_decide (ht : 3 * t < Fintype.card P) :
    ∃ E : Exec (Alg4.alg (P := P) t) x .byzantine t, E.Fair ∧ ∀ q, ∃ i, (E.σ i).dec q ≠ none :=
  let ⟨E, hF, hb⟩ := exists_fair (Alg4.alg (P := P) t) x .byzantine t
  ⟨E, hF, fun q => Alg4.termination E hF ht (E.correct_of_bad_empty hb q)⟩

theorem Alg6.exists_fair_all_decide (ht : 3 * t < Fintype.card P) :
    ∃ E : Exec (Alg6.alg (P := P) t) x .byzantine t, E.Fair ∧ ∀ q, ∃ i, (E.σ i).dec q ≠ none :=
  let ⟨E, hF, hb⟩ := exists_fair (Alg6.alg (P := P) t) x .byzantine t
  ⟨E, hF, fun q => Alg6.termination E hF ht (E.correct_of_bad_empty hb q)⟩

theorem Alg3.exists_fair_all_decide (ht : 2 * t < Fintype.card P) :
    ∃ E : Exec (Alg3.alg (P := P) t) x .crash t, E.Fair ∧ ∀ q, ∃ i, (E.σ i).dec q ≠ none :=
  let ⟨E, hF, hb⟩ := exists_fair (Alg3.alg (P := P) t) x .crash t
  ⟨E, hF, fun q => Alg3.termination E hF ht (E.correct_of_bad_empty hb q)⟩

theorem Alg5.exists_fair_all_decide (ht : 2 * t < Fintype.card P) :
    ∃ E : Exec (Alg5.alg (P := P) t) x .crash t, E.Fair ∧ ∀ q, ∃ i, (E.σ i).dec q ≠ none :=
  let ⟨E, hF, hb⟩ := exists_fair (Alg5.alg (P := P) t) x .crash t
  ⟨E, hF, fun q => Alg5.termination E hF ht (E.correct_of_bad_empty hb q)⟩

end Podc.BindingCrusaderAgreement
