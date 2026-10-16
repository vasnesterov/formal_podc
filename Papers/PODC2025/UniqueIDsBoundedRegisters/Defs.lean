import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Covering

/-!
# Unique identifiers from bounded registers: definitions

Model of Anoprenko–Kuznetsov–Aksenov, *Brief Announcement: Optimal Construction of Unique
Identifiers from Bounded Registers*, PODC 2025.

* **Base objects.** `k` registers, each storing a value of `Fin m` (`m = 2^w` for `w`-bit
  registers), with atomic `read`, `write v` and cyclic `fetch-and-increment` (`bReg m`; `fai`
  returns the old value and sets the register to `old + 1 mod m`).
* **Implemented object.** `uidObj`: one operation `get()` (argument `Unit`) returning a natural
  number. Its sequential specification ("all outputs are distinct") is not deterministic, so it
  is not expressed through `ObjSpec.δ` (the dummy `δ` of `uidObj` is never used); instead
  `UniqueResp α` says that distinct completed operations of `α` returned distinct values. For
  this specification linearizability is equivalent to `UniqueResp` (any order of the operations
  is a legal sequential history when the outputs are distinct).
* **Bounded number of calls.** `invCount α` is the number of invocations in `α`;
  `CorrectUpTo I B`: every execution with at most `B` invocations satisfies `UniqueResp`.
* **Anonymity.** `Anonymous I`: all processes run the same automaton from the same initial
  state (`locInit`, `invoke`, `act` do not depend on the process).
* **Progress.** `Impl.ObstructionFree`/`Impl.WaitFree` from CSLib; `WaitFreeUpTo I B`:
  wait-freedom restricted to infinite executions with at most `B` invocations.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

/-- Primitives of a bounded register: `read`, `write v`, `fetch-and-increment`. -/
inductive BOp (m : ℕ) where
  /-- `read()`. -/
  | read
  /-- `write(v)`. -/
  | write (v : Fin m)
  /-- `FAI()`: returns the old value, increments modulo `m`. -/
  | fai
  deriving DecidableEq

/-- A register with values in `Fin m` (a `w`-bit register for `m = 2^w`), initially `0`, with
atomic read, write and cyclic fetch-and-increment (FAI applied to `m - 1` gives `0`). The
response of a write is the written value (a dummy). -/
abbrev bReg (m : ℕ) [NeZero m] : ObjSpec where
  State := Fin m
  Op := BOp m
  Resp := Fin m
  init := 0
  δ s o := match o with
    | .read => (s, s)
    | .write v => (v, v)
    | .fai => (s + 1, s)

/-- The unique-identifier object: a single operation `get()` returning a natural number.
The transition function is a dummy (never used): the specification "distinct outputs" is
`UniqueResp`. -/
abbrev uidObj : ObjSpec where
  State := Unit
  Op := Unit
  Resp := ℕ
  init := ()
  δ _ _ := ((), 0)

variable {P : Type} {A : ObjSpec}

/-- The label is an invocation. -/
def isInv : Label P A → Bool
  | .inv _ _ => true
  | _ => false

/-- Number of invocations (calls of `get()`) in an execution. -/
def invCount (α : List (Label P A)) : ℕ := α.countP isInv

@[simp] lemma invCount_nil : invCount ([] : List (Label P A)) = 0 := rfl

@[simp] lemma invCount_append (α β : List (Label P A)) :
    invCount (α ++ β) = invCount α + invCount β := List.countP_append ..

@[simp] lemma invCount_cons (ℓ : Label P A) (α : List (Label P A)) :
    invCount (ℓ :: α) = invCount α + if isInv ℓ then 1 else 0 := by
  simp [invCount, List.countP_cons]

/-- Distinct completed `get()` operations returned distinct identifiers. -/
def UniqueResp [DecidableEq P] (α : List (Label P uidObj)) : Prop :=
  ∀ x y : OpId P, Completed α x → Completed α y → x ≠ y → respOf α x ≠ respOf α y

variable {ι : Type} {B : ι → ObjSpec} {L : Type}

/-- The implementation is a correct unique-identifier object as long as `get()` is called at
most `N` times: every execution with at most `N` invocations has distinct outputs. -/
def CorrectUpTo [DecidableEq P] [DecidableEq ι] (I : Impl uidObj B P L) (N : ℕ) : Prop :=
  ∀ α, I.Valid α → invCount α ≤ N → UniqueResp α

/-- Anonymity: every process runs the same deterministic automaton from the same initial
state. -/
structure Anonymous (I : Impl A B P L) : Prop where
  locInit : ∀ p q, I.locInit p = I.locInit q
  invoke : ∀ p q, I.invoke p = I.invoke q
  act : ∀ p q, I.act p = I.act q

/-- Wait-freedom in infinite executions with at most `N` invocations. -/
def WaitFreeUpTo [DecidableEq P] [DecidableEq ι] (I : Impl A B P L) (N : ℕ) : Prop :=
  ∀ e : I.InfExec, (∀ T, invCount ((List.range T).map e.lbl) ≤ N) →
    ∀ (p : P) (n : ℕ), (∀ t ≥ n, (e.cfg t).pend p ≠ none) → ∃ T, ∀ t ≥ T, e.lbl t ≠ .tau p

lemma WaitFree.waitFreeUpTo [DecidableEq P] [DecidableEq ι] {I : Impl A B P L}
    (h : I.WaitFree) (N : ℕ) : WaitFreeUpTo I N :=
  fun e _ p n hp => h e p n hp

end Cslib.SharedMemory.UniqueIDs
