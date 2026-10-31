import Mathlib

/-!
# The model: asynchronous read/write shared memory, DSM remote memory references

Golab, *A complexity separation between the cache-coherent and distributed shared memory
models*, PODC 2011 (arXiv 1109.5153), Section 2 and Section 4.

* `N` processes `Fin N`; shared variables `V` holding values `Val`; each variable lives in the
  memory module of one process (`Algorithm.home`, the DSM placement chosen by the algorithm).
* Each process runs a deterministic program (`Algorithm`, the same shape as
  `Cslib.SharedMemory.Impl` specialised to read/write registers): local state `S`, an
  invocation handler `invoke` and a next-action function `act` (`read v` with a continuation,
  `write v x`, or `ret b` = return the Boolean response of the current call).
* The procedures are `Poll()` and `Signal()` (`Proc`). Which procedure an idle process calls next
  (if any) is chosen by the environment.
* An execution (history) is a list of *events* `Ev` that record the process and what it did
  (`inv o`, `read v x` with the value read, `write v x`, `ret b`). `Valid` says that every event
  is a legal step of its process (given the process' own previous events) and that every read
  returns the value of the most recent write (or the initial value). Since processes are
  deterministic, an event list determines the execution.
* A step of `p` that reads or writes a variable whose home is not `p` is a remote memory reference
  in the DSM model (`Ev.remote`, `rmr`).

Termination of a process is modelled by the process staying idle forever (see `SoloTerminating`).
-/

namespace Podc.CCvsDSMSeparation

/-- The two procedures of the signaling problem with polling semantics. -/
inductive Proc
  | poll
  | signal
  deriving DecidableEq

/-- What a process executing a procedure does next. -/
inductive Action (V Val S : Type*) where
  /-- read `v` and continue in local state `k x`, where `x` is the value read -/
  | read (v : V) (k : Val → S)
  /-- write `x` to `v` and continue in local state `s` -/
  | write (v : V) (x : Val) (s : S)
  /-- return response `b` to the caller and become idle in local state `s` -/
  | ret (b : Bool) (s : S)

/-- A deterministic shared-memory algorithm for `N` processes using atomic reads and writes of the
variables `V`. For `Signal()` the returned Boolean is meaningless. -/
structure Algorithm (N : ℕ) (V Val S : Type*) where
  /-- DSM placement: the process whose memory module holds `v` -/
  home : V → Fin N
  /-- initial values of the shared variables -/
  memInit : V → Val
  /-- initial local states -/
  locInit : Fin N → S
  /-- local state at the beginning of a call -/
  invoke : Fin N → S → Proc → S
  /-- next action of a process that is executing a call -/
  act : Fin N → S → Action V Val S

/-- What happened in one step. -/
inductive Op (V Val : Type*) where
  | inv (o : Proc)
  | read (v : V) (x : Val)
  | write (v : V) (x : Val)
  | ret (b : Bool)

/-- An event: process `p` performed `op`. -/
structure Ev (N : ℕ) (V Val : Type*) where
  p : Fin N
  op : Op V Val

variable {N : ℕ} {V Val S : Type*}

namespace Op

/-- The variable accessed by a step (if any). -/
def var : Op V Val → Option V
  | .read v _ => some v
  | .write v _ => some v
  | _ => none

/-- The variable written by a step (if any) and the value written. -/
def written : Op V Val → Option (V × Val)
  | .write v x => some (v, x)
  | _ => none

/-- Invocation of `Signal()`. -/
def isSigInv : Op V Val → Bool
  | .inv .signal => true
  | _ => false

/-- Any invocation. -/
def isInv : Op V Val → Bool
  | .inv _ => true
  | _ => false

/-- A memory access (read or write). -/
def isAccess : Op V Val → Bool
  | .read _ _ => true
  | .write _ _ => true
  | _ => false

lemma isInv_eq_false_of_isAccess {op : Op V Val} (h : op.isAccess = true) :
    op.isInv = false := by cases op <;> simp_all [isAccess, isInv]

lemma isSigInv_eq_false_of_isAccess {op : Op V Val} (h : op.isAccess = true) :
    op.isSigInv = false := by cases op <;> simp_all [isAccess, isSigInv]

lemma isSigInv_eq_false_of_isInv {op : Op V Val} (h : op.isInv = false) :
    op.isSigInv = false := by
  rcases op with o | _ | _ | _ <;> simp_all [isInv, isSigInv]

end Op

/-- The DSM model: an access of `p` to a variable outside `p`'s memory module is a remote memory
reference. -/
def Op.remoteFor (home : V → Fin N) (p : Fin N) (op : Op V Val) : Bool :=
  match op.var with
  | some v => decide (home v ≠ p)
  | none => false

/-- The DSM model: the step `e` is a remote memory reference. -/
def Ev.remote (home : V → Fin N) (e : Ev N V Val) : Bool := e.op.remoteFor home e.p

/-- Status of a process: `none` = idle (between calls), `some o` = executing procedure `o`. -/
abbrev LState (S : Type*) := S × Option Proc

/-- The events of process `p`, in order. -/
def proj (τ : List (Ev N V Val)) (p : Fin N) : List (Op V Val) :=
  (τ.filter (fun e => e.p = p)).map Ev.op

/-- The participants (processes taking at least one step, invocations included). -/
def par (τ : List (Ev N V Val)) : Finset (Fin N) := (τ.map Ev.p).toFinset

/-- Number of invocations of `Signal()`. -/
def signals (τ : List (Ev N V Val)) : ℕ := τ.countP (fun e => e.op.isSigInv)

open Classical in
/-- The last write (writer, value) to `v` in `τ`. -/
noncomputable def lastWrite (v : V) (τ : List (Ev N V Val)) : Option (Fin N × Val) :=
  τ.foldl (fun acc e => match e.op.written with
    | some (u, x) => if u = v then some (e.p, x) else acc
    | none => acc) none

/-- The process that wrote `v` last. -/
noncomputable def writer (v : V) (τ : List (Ev N V Val)) : Option (Fin N) :=
  (lastWrite v τ).map Prod.fst

/-- "Every event satisfies `P` relative to the prefix before it", starting after `ρ`. -/
def StepsFrom {α : Type*} (P : List α → α → Prop) : List α → List α → Prop
  | _, [] => True
  | ρ, e :: σ => P ρ e ∧ StepsFrom P (ρ ++ [e]) σ

/-- "Every event satisfies `P` relative to the prefix before it". -/
def Steps {α : Type*} (P : List α → α → Prop) (τ : List α) : Prop := StepsFrom P [] τ

namespace Algorithm

variable (A : Algorithm N V Val S)

open Classical in
/-- One local step of process `p` (`none` if the step is not legal). -/
noncomputable def lstep (p : Fin N) : LState S → Op V Val → Option (LState S)
  | (s, none), .inv o => some (A.invoke p s o, some o)
  | (s, some o), op =>
    match A.act p s, op with
    | .read v k, .read v' x => if v = v' then some (k x, some o) else none
    | .write v x s', .write v' x' => if v = v' ∧ x = x' then some (s', some o) else none
    | .ret b s', .ret b' => if b = b' then some (s', none) else none
    | _, _ => none
  | _, _ => none

/-- Local run of process `p` on its own events. -/
noncomputable def lrun (p : Fin N) (l : List (Op V Val)) : Option (LState S) :=
  l.foldl (fun acc op => acc.bind fun c => A.lstep p c op) (some (A.locInit p, none))

/-- Local state of `p` after `τ`. -/
noncomputable def state (τ : List (Ev N V Val)) (p : Fin N) : Option (LState S) :=
  A.lrun p (proj τ p)

/-- Value of `v` after `τ`. -/
noncomputable def memVal (τ : List (Ev N V Val)) (v : V) : Val :=
  match lastWrite v τ with
  | some (_, x) => x
  | none => A.memInit v

/-- `e` is a legal next step after `τ`. -/
def StepOK (τ : List (Ev N V Val)) (e : Ev N V Val) : Prop :=
  (A.lrun e.p (proj τ e.p ++ [e.op])).isSome ∧ ∀ v x, e.op = .read v x → x = A.memVal τ v

/-- `τ` is a (finite) execution of the algorithm. -/
def Valid (τ : List (Ev N V Val)) : Prop := Steps A.StepOK τ

/-- `p` is idle (between calls) after `τ`. -/
def Idle (τ : List (Ev N V Val)) (p : Fin N) : Prop := ∃ s, A.state τ p = some (s, none)

/-- `p` is executing procedure `o` after `τ`. -/
def Busy (τ : List (Ev N V Val)) (p : Fin N) (o : Proc) : Prop :=
  ∃ s, A.state τ p = some (s, some o)

/-- Total number of RMRs in the DSM model. -/
noncomputable def rmr (τ : List (Ev N V Val)) : ℕ := τ.countP (Ev.remote A.home)

/-- **Specification 4.1** (signaling, polling semantics), required in every execution with at
most one invocation of `Signal()` (one signaler):
* if a call to `Poll()` returns `true`, some call to `Signal()` has already begun;
* if a call to `Poll()` returns `false`, no call to `Signal()` completed before this call to
  `Poll()` began.
Stated for the return step `⟨p, ret b⟩` appended to the execution `τ`. -/
def Solves : Prop :=
  ∀ (τ : List (Ev N V Val)) (p : Fin N) (b : Bool),
    A.Valid (τ ++ [⟨p, .ret b⟩]) → signals τ ≤ 1 → A.Busy τ p .poll →
      (b = true → ∃ e ∈ τ, e.op.isSigInv) ∧
      (b = false → ¬ ∃ (τ₁ : List (Ev N V Val)) (s : Fin N) (b' : Bool) (τ₂ τ₃ : List (Ev N V Val)),
        τ = τ₁ ++ ⟨s, .ret b'⟩ :: (τ₂ ++ ⟨p, .inv .poll⟩ :: τ₃) ∧ A.Busy τ₁ s .signal ∧
        ∀ e ∈ τ₃, e.p = p → e.op.isInv = false)

/-- Termination, in the (weak) form used by the lower bound: if every process other than `p` is
idle (has terminated) and `p` runs solo, `p`'s current call completes after finitely many steps.
This is implied by the paper's "terminating" (Section 2), see `Terminating.soloTerminating`. -/
def SoloTerminating : Prop :=
  ∀ (τ : List (Ev N V Val)) (p : Fin N) (o : Proc), A.Valid τ → signals τ ≤ 1 →
    (∀ q, q ≠ p → A.Idle τ q) → A.Busy τ p o →
    ∃ (σ : List (Ev N V Val)) (b : Bool), (∀ e ∈ σ, e.p = p ∧ e.op.isAccess = true) ∧
      A.Valid (τ ++ σ ++ [⟨p, .ret b⟩])

/-- `σ` is a solo run of `p` in which `p` only calls `Poll()`. -/
def SoloPoll (p : Fin N) (σ : List (Ev N V Val)) : Prop :=
  ∀ e ∈ σ, e.p = p ∧ e.op.isSigInv = false

/-- **Definition 6.8**: `p` is *stable* after `τ` if running `p` solo (calling `Poll()`
repeatedly) incurs no RMR. -/
def Stable (τ : List (Ev N V Val)) (p : Fin N) : Prop :=
  ∀ σ, SoloPoll p σ → A.Valid (τ ++ σ) → A.rmr σ = 0

end Algorithm

end Podc.CCvsDSMSeparation
