import Papers.PODC2016.OhRAMAtomicMemory.Model

/-!
# Statements: atomicity and termination

* `Atomic Pr`: every history of a reachable configuration has a linearization (CSLib
  `IsLinearization` for `register V v₀`); this is the paper's atomicity (A1–A3), extended to
  executions with pending operations in the standard way.
* `Live Pr f`: in every fair execution (CSLib `Exec.Fair`: every enabled reception by a correct
  process eventually happens = reliable channels) in which at most `f` *servers* crash (any number
  of readers and writers may crash), every operation of a correct client returns.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- At most `f` servers are crashed at any time of `e`. -/
def ServerResilient {L M Act : Type} {A : ObjSpec} [DecidableEq M]
    {Pr : Protocol (Node W R S) A L M Act} (e : Pr.Exec) (f : ℕ) : Prop :=
  ∀ t, (Finset.univ.filter (fun s : S => Node.sv s ∈ (e.cfg t).crashed)).card ≤ f

/-- Termination with at most `f` server crashes. -/
def Live {L M Act : Type} {A : ObjSpec} [DecidableEq M]
    (Pr : Protocol (Node W R S) A L M Act) (f : ℕ) : Prop :=
  ∀ e : Pr.Exec, e.Fair → ServerResilient e f → e.OpsTerminate

end Podc.OhRAM
