import Papers.PODC2020.RecoverableMutexRMR.Model

/-!
# Properties of recoverable mutual exclusion (Section 2 of the paper)

Executions are schedules `e : ℕ → Ev P` (see `Model.lean`).

* A schedule has *finitely many crashes* if after some time no crash event occurs.
* A schedule is *fair* if every process that is outside the remainder section at some time takes
  a step at that time or later ("all processes that have pending method calls or that are in the
  critical section keep taking steps"). A step of a process in the critical section is its call
  of `Exit()`; processes in the remainder section need not take steps (if they do, they call
  `Enter()`).
-/

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P]

/-- Only finitely many crash events. -/
def FinCrashes (e : ℕ → Ev P) : Prop := ∃ T₀, ∀ t, T₀ ≤ t → ∀ p, e t ≠ .crash p

/-- Fairness: processes outside the remainder section keep taking steps. -/
def Fair (e : ℕ → Ev P) : Prop :=
  ∀ p t, (exec e t).pc p ≠ .rem → ∃ t', t ≤ t' ∧ e t' = .step p

/-- Non-vacuity of the liveness hypotheses: the crash-free round-robin schedule of two
processes is fair. -/
example : Fair (fun t => Ev.step (decide (t % 2 = 0))) ∧
    FinCrashes (fun t => Ev.step (decide (t % 2 = 0))) := by
  refine ⟨fun p t _ => ?_, ⟨0, fun t _ q h => by cases h⟩⟩
  by_cases h : decide (t % 2 = 0) = p
  · exact ⟨t, le_rfl, by simp only [h]⟩
  · refine ⟨t + 1, by omega, ?_⟩
    cases p <;> simp_all <;> omega

end Podc.RecoverableMutexRMR
