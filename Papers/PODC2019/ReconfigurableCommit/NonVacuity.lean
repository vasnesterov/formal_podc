/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Main
import Papers.PODC2019.ReconfigurableCommit.Counterexample

/-!
# Non-vacuity of Theorem 4.1

The hypotheses of `theorem_4_1` are satisfiable (serializability for one object, one shard with
two replicas), and the corrected protocol does commit transactions.
-/

namespace Podc.ReconfigurableCommit

namespace NonVacuity

open Line56

/-- The corrected protocol on the instance of `Line56`. -/
def PaFix : Params (Fin 2) Bool Unit (Fin 4) := { Line56.Pa with fixNewConfig := true }

/-- `b` certifies `t₁`; leader `a` prepares it, `b` accepts it, `t₁` commits. -/
def acts : List (Action (Fin 2) Bool Unit (Fin 4)) :=
  [ .certify 1 0 true, .deliver 1 0 0, .deliver 0 1 0, .deliver 1 1 0, .deliver 1 1 0,
    .decide 1 0 (fun _ => 1) (fun _ => .commit) ]

theorem run_hist : (run PaFix (initState PaFix) acts).map State.hist =
    some [.certify 0 true, .decide 0 .commit] := by decide

/-- All hypotheses of `theorem_4_1` hold for `PaFix`, and some reachable state has a committed
transaction. -/
theorem theorem_4_1_nonvacuous :
    PaFix.fixNewConfig = true ∧ ValidInit PaFix ∧ (∀ t, (PaFix.σ.shards t).Nonempty) ∧
    Matching PaFix.σ f PaFix.fs PaFix.gs ∧ EpsNeutral PaFix.σ PaFix.fs ∧
    ∃ st, Reachable PaFix st ∧ Committed st.hist 0 := by
  refine ⟨rfl, fun s => by cases s; decide, fun t => ⟨(), by simp [PaFix, Line56.Pa, σ]⟩,
    matching, epsNeutral, ?_⟩
  obtain ⟨st, hst, hh⟩ := Option.map_eq_some_iff.1 run_hist
  exact ⟨st, reachable_of_run PaFix Relation.ReflTransGen.refl hst, by
    simp [Committed, hh]⟩

end NonVacuity

end Podc.ReconfigurableCommit
