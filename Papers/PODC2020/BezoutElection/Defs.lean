import Cslib.Computability.Distributed.SharedMemory.Anonymous
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Computability.Distributed.SharedMemory.Progress
import Podc.SharedMemory.Progress
import Podc.SharedMemory.Objects.Iface

/-!
# Election in anonymous memory: problem definitions

Godard, Imbs, Raynal, Taubenfeld, *From Bezout's Identity to Space-Optimal Election in Anonymous
Memory Systems*, PODC 2020 (DOI 10.1145/3382734.3405727), Section 1.

* The election "object" `elecObj R` has a single operation `elect()` (`Unit`) whose response is
  of type `R`: a bit ("am I elected?", the output used in the paper's impossibility proof,
  Section 2), or an identifier / a set of identifiers for the algorithms.
* **Model** (Section 1.2): all `n` processes participate, i.e. each one invokes `elect()` exactly
  once; no process fails; the system is asynchronous. *Termination* (`Terminates`): in every
  fair (`InfExec.IsFair`) infinite execution in which every process invokes `elect()` once, every
  process returns.
  (Equivalently, there is no such infinite execution: all fair executions are finite.)
* **d-election** (`DElection d`, bit outputs): in every finite execution where all processes
  have returned, the number of processes that returned `true` is between `1` and `d`.
  **Exact d-election** (`ExactElection d`): it is exactly `d`.
  The paper's d-election additionally asks every process to output the set of elected identifiers;
  for the impossibility results the bit version is weaker, hence the theorems are stronger.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

/-- The election object: one operation `elect()`, response of type `R` (no sequential
semantics; the problem is a task, specified on executions). -/
abbrev elecObj (R : Type) [Inhabited R] : ObjSpec := ObjSpec.iface Unit R

section Generic

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
  {I : Impl A B P L}

/-- Every process invokes at most one operation. -/
def IsOneShot (e : I.InfExec) : Prop := ∀ t, OneShot (e.lbls t)

/-- Every process invokes an operation (all processes participate). -/
def AllInvoke (e : I.InfExec) : Prop := ∀ p, ∃ t o, e.lbl t = .inv p o

end Generic

section Election

variable {R : Type} [Inhabited R] {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type}
  [DecidableEq P]

/-- **Termination** (all processes participate, no failures, asynchrony): in every fair one-shot
infinite execution in which every process invokes `elect()`, every process returns. -/
def Terminates (I : Impl (elecObj R) B P L) : Prop :=
  ∀ e : I.InfExec, IsOneShot e → AllInvoke e → e.IsFair → ∀ p, ∃ t r, e.lbl t = .ret p r

/-- All processes have returned in the finite execution `α`. -/
def AllReturned (α : List (Label P (elecObj R))) : Prop := ∀ p, outputs α p ≠ none

variable [Fintype P]

/-- The processes that returned `true` ("I am elected"). -/
def elected (α : List (Label P (elecObj Bool))) : Finset P :=
  Finset.univ.filter (fun p => outputs α p = some true)

/-- **d-election** (safety, bit outputs): in every finite one-shot execution in which all
processes returned, at least one and at most `d` processes are elected. -/
def DElection (d : ℕ) (I : Impl (elecObj Bool) B P L) : Prop :=
  ∀ α, I.Valid α → OneShot α → AllReturned α → 1 ≤ (elected α).card ∧ (elected α).card ≤ d

/-- **Exact d-election** (safety, bit outputs): in every finite one-shot execution in which all
processes returned, exactly `d` processes are elected. -/
def ExactElection (d : ℕ) (I : Impl (elecObj Bool) B P L) : Prop :=
  ∀ α, I.Valid α → OneShot α → AllReturned α → (elected α).card = d

end Election

end BezoutElection
