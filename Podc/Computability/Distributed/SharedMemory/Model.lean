import Cslib.Computability.Distributed.SharedMemory.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Model.lean (append to the
-- "Pending operations" part of the step and run API)

/-!
# Runs: idle and pending processes

Additions to `Cslib/Computability/Distributed/SharedMemory/Model.lean`: consequences of the
counting invariant `Impl.run_counts` that are re-derived in many invariant proofs.

## Main statements

* `Impl.run_resps_le_ops`: a process has returned at most as often as it has invoked.
* `Impl.run_idle_counts`, `Impl.not_invoked_curOp_of_idle`: an idle process has as many
  responses as invocations, so its current instance has not been invoked;
  `Impl.run_pend_counts`: a pending process has one more invocation than responses.
* `Impl.opsOf_ne_nil_of_pend`, `Impl.respsOf_ne_nil_of_idle`: a pending process has invoked
  something; an idle process that has invoked something has returned something.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] {I : Impl A B P L} {α : List (Label P A)}
  {C : Config A B P L} {p : P}

/-- In an execution, a process has returned at most as often as it has invoked. -/
lemma run_resps_le_ops (h : I.run α = some C) (p : P) :
    (respsOf α p).length ≤ (opsOf α p).length := by
  rcases I.run_counts h p with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-- An idle process has as many responses as invocations. -/
lemma run_idle_counts (h : I.run α = some C) (hp : C.pend p = none) :
    (opsOf α p).length = (respsOf α p).length := by
  rcases I.run_counts h p with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd hp h1

/-- A pending process has one more invocation than responses. -/
lemma run_pend_counts (h : I.run α = some C) (hp : C.pend p ≠ none) :
    (opsOf α p).length = (respsOf α p).length + 1 := by
  rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 hp
  · exact h2

/-- The current instance of an idle process has not been invoked. -/
lemma not_invoked_curOp_of_idle (h : I.run α = some C) (hp : C.pend p = none) :
    ¬ Invoked α (curOp α p) := by
  simp [Invoked, I.run_idle_counts h hp]

/-- A pending process has invoked an operation. -/
lemma opsOf_ne_nil_of_pend (h : I.run α = some C) (hp : C.pend p ≠ none) : opsOf α p ≠ [] :=
  fun h0 => hp (I.pend_none_of_opsOf_nil h h0)

/-- An idle process that has invoked an operation has returned. -/
lemma respsOf_ne_nil_of_idle (h : I.run α = some C) (hp : C.pend p = none)
    (hops : opsOf α p ≠ []) : respsOf α p ≠ [] := by
  intro h0
  have := I.run_idle_counts h hp
  rw [h0] at this
  exact hops (List.eq_nil_of_length_eq_zero (by simpa using this))

end Impl

end Cslib.SharedMemory
