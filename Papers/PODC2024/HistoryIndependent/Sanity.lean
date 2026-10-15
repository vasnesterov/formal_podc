import Papers.PODC2024.HistoryIndependent.ClassC
import Cslib.Computability.Distributed.SharedMemory.Atomic
import Mathlib

/-!
# Non-vacuity and tightness

The notions used in the impossibility results are satisfiable: the trivial atomic implementation
of any object from one base object of its own type is linearizable, wait-free and perfectly
history independent (`Cslib.SharedMemory.Atomic.perfectHI`, `Cslib.SharedMemory.Atomic.waitFree`).

In particular the bound of Theorem 17 / Corollary 18 is tight: a `t`-valued register *does*
have a wait-free (even perfect) history-independent implementation from a base object with `t`
states (the "large base objects" regime of Section 6 of the paper).
-/

namespace Cslib.SharedMemory

/-- Tightness of Theorem 17 for registers: a `t`-valued register has a wait-free, perfect (hence
state-quiescent) HI implementation from one base object with exactly `t` states, for any set of
processes and with all operations allowed to everybody. -/
theorem register_tight (t : ℕ) (v₀ : Fin t) (P : Type) [DecidableEq P] :
    (atomicImpl (register (Fin t) v₀) v₀ P).WaitFree ∧
    (atomicImpl (register (Fin t) v₀) v₀ P).PerfectHI ∧
    (atomicImpl (register (Fin t) v₀) v₀ P).StateQuiescentHI ∧
    ∀ j : Unit, Nat.card ((fun _ : Unit => register (Fin t) v₀) j).State = t :=
  ⟨Atomic.waitFree, Atomic.perfectHI, Impl.PerfectHI.stateQuiescentHI _ Atomic.perfectHI,
    fun _ => by simp⟩

end Cslib.SharedMemory
