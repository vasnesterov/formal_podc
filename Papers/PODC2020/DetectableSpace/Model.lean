import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Recoverable implementations with system-wide crashes (Ben-Baruch–Hendler–Rusanovsky, PODC 2020)

A self-contained model of Section 2 of *Upper and Lower Bounds on the Space Complexity of
Detectable Objects*: asynchronous processes `P`, non-volatile memory, system-wide crashes, and
recoverable operations with recovery functions.

* The implemented object is given by a deterministic sequential specification
  `O : Cslib.SharedMemory.ObjSpec`.
* An implementation `A : RImpl O P` has non-volatile **shared** memory `A.Sh`, a non-volatile
  **private** memory `A.Pv` per process, and volatile local states `A.L`. A step of a process
  either applies an arbitrary atomic transformation to the *whole* shared memory
  (`Act.sh`: any primitive operations, even multi-word ones), or accesses only its own private
  non-volatile memory (`Act.pv`), or returns (`Act.ret r`, `r = none` is the special value `fail`).
  Steps never access both kinds of memory at once.
* Invoking operation `o` at an idle process `p` sets its local state to `A.start p o` and lets
  the *system / caller* modify `p`'s private non-volatile memory by `A.aux p o` (this is how
  auxiliary state is provided "via NVM", e.g. `Ann_p.CP := 0`; Definition 1). Invocations never
  touch shared memory.
* A system-wide crash resets the local state of every process that is in the middle of an
  operation `o` to the initial state `A.recov p o` of the recovery function `o.Recover`
  (called with the same arguments); idle processes stay idle; memory is unaffected.
* Each invocation gets a fresh identifier (the counter `cnt`); the history of an execution is the
  list of invocation, response and crash events (`HEv`).

Correctness is durable linearizability together with detectability (`DLin`, `DurLinDet`): there is
a sequential order of a subset of the invoked operations which contains every operation that
returned a value (with that value as its sequential response), contains no operation whose
recovery returned `fail`, may contain pending operations, and respects real-time order. An
operation can only return `fail` from its recovery function.

Progress: `ObstructionFree` (from every reachable configuration a process running solo without
crashes completes its operation / recovery function) and `WeakOF` (Definition 2: the same, but
only from configurations where all other processes are idle).
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

/-- One step of a process: an atomic access to the shared memory, an access to its private
non-volatile memory, or returning (`none` = `fail`). -/
inductive Act (Sh Pv L R : Type) where
  | sh (f : Sh → L × Sh)
  | pv (f : Pv → L × Pv)
  | ret (r : Option R)

/-- A recoverable implementation of the object `O` for processes `P`. -/
structure RImpl (O : ObjSpec) (P : Type) where
  /-- Non-volatile shared memory. -/
  Sh : Type
  /-- Non-volatile private memory of a process. -/
  Pv : Type
  /-- Volatile local state. -/
  L : Type
  sh₀ : Sh
  pv₀ : P → Pv
  /-- Local state of `p` when it invokes `o`. -/
  start : P → O.Op → L
  /-- Local state of `p` when it starts `o.Recover` after a crash. -/
  recov : P → O.Op → L
  /-- What the system / caller writes to `p`'s private NVM when `p` invokes `o`
  (auxiliary state provided via NVM; `id` if there is none). -/
  aux : P → O.Op → Pv → Pv
  /-- The next step in local state `l`. -/
  act : P → L → Act Sh Pv L O.Resp

/-- State of a process: idle, or executing operation instance `a` (operation `o`), in
recovery (`rec = true`) or not, with local state `l`. -/
inductive PSt (Op L : Type) where
  | idle
  | run (a : ℕ) (o : Op) (rec : Bool) (l : L)

/-- Schedule events. -/
inductive Ev (P Op : Type) where
  | inv (p : P) (o : Op)
  | step (p : P)
  | crash

/-- History events. `res a r rec`: operation instance `a` returned `r` (`none` = `fail`),
`rec` tells whether it returned from its recovery function. -/
inductive HEv (P Op R : Type) where
  | inv (a : ℕ) (p : P) (o : Op)
  | res (a : ℕ) (r : Option R) (rec : Bool)
  | crash

variable {O : ObjSpec} {P : Type}

namespace RImpl

variable (A : RImpl O P)

/-- Configurations. -/
structure Cfg where
  sh : A.Sh
  pv : P → A.Pv
  ps : P → PSt O.Op A.L
  cnt : ℕ

/-- The initial configuration. -/
def init : A.Cfg := ⟨A.sh₀, A.pv₀, fun _ => .idle, 0⟩

/-- Effect of a system-wide crash on a process. -/
def crashPS (p : P) : PSt O.Op A.L → PSt O.Op A.L
  | .idle => .idle
  | .run a o _ _ => .run a o true (A.recov p o)

variable [DecidableEq P]

/-- One event. -/
def step1 (C : A.Cfg) : Ev P O.Op → A.Cfg × List (HEv P O.Op O.Resp)
  | .inv p o =>
    match C.ps p with
    | .idle => (⟨C.sh, Function.update C.pv p (A.aux p o (C.pv p)),
        Function.update C.ps p (.run C.cnt o false (A.start p o)), C.cnt + 1⟩, [.inv C.cnt p o])
    | .run .. => (C, [])
  | .step p =>
    match C.ps p with
    | .idle => (C, [])
    | .run a o b l =>
      match A.act p l with
      | .sh f => (⟨(f C.sh).2, C.pv, Function.update C.ps p (.run a o b (f C.sh).1), C.cnt⟩, [])
      | .pv f => (⟨C.sh, Function.update C.pv p (f (C.pv p)).2,
          Function.update C.ps p (.run a o b (f (C.pv p)).1), C.cnt⟩, [])
      | .ret r => (⟨C.sh, C.pv, Function.update C.ps p .idle, C.cnt⟩, [.res a r b])
  | .crash => (⟨C.sh, C.pv, fun p => A.crashPS p (C.ps p), C.cnt⟩, [.crash])

/-- Execution of a schedule: final configuration and history. -/
def exec (C : A.Cfg) : List (Ev P O.Op) → A.Cfg × List (HEv P O.Op O.Resp)
  | [] => (C, [])
  | e :: es => ((exec (A.step1 C e).1 es).1, (A.step1 C e).2 ++ (exec (A.step1 C e).1 es).2)

@[simp] lemma exec_nil (C : A.Cfg) : A.exec C [] = (C, []) := rfl

lemma exec_cons (C : A.Cfg) (e : Ev P O.Op) (es : List (Ev P O.Op)) :
    A.exec C (e :: es) =
      ((A.exec (A.step1 C e).1 es).1, (A.step1 C e).2 ++ (A.exec (A.step1 C e).1 es).2) := rfl

lemma exec_append (C : A.Cfg) (es fs : List (Ev P O.Op)) :
    A.exec C (es ++ fs) =
      ((A.exec (A.exec C es).1 fs).1, (A.exec C es).2 ++ (A.exec (A.exec C es).1 fs).2) := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih => simp [exec_cons, ih]

/-- Reachable configurations (executions may contain crashes). -/
def Reachable (C : A.Cfg) : Prop := ∃ es, (A.exec A.init es).1 = C

/-- `p` runs solo for `k` steps. -/
abbrev solo (p : P) (k : ℕ) : List (Ev P O.Op) := List.replicate k (.step p)

/-- **Obstruction-freedom**: from every reachable configuration, a process running solo
(without crashes) completes its operation or recovery function. -/
def ObstructionFree : Prop :=
  ∀ C, A.Reachable C → ∀ p, ∃ k, (A.exec C (solo p k)).1.ps p = .idle

/-- **Weak obstruction-freedom** (Definition 2): as `ObstructionFree`, but only from reachable
configurations in which all processes other than `p` are idle. -/
def WeakOF : Prop :=
  ∀ C, A.Reachable C → ∀ p, (∀ q, q ≠ p → C.ps q = .idle) →
    ∃ k, (A.exec C (solo p k)).1.ps p = .idle

lemma ObstructionFree.weakOF (h : A.ObstructionFree) : A.WeakOF :=
  fun C hC p _ => h C hC p

/-- **Wait-freedom (syntactic certificate)**: a measure on local states that strictly decreases
at every memory step of a process, whatever the memory contents. Then every operation and
every recovery function completes within `μ (A.start p o)` (resp. `μ (A.recov p o)`) of its own
steps, whatever the other processes do, if no crash occurs. -/
def BoundedSteps (μ : A.L → ℕ) : Prop :=
  ∀ p l, match A.act p l with
    | .sh f => ∀ s, μ (f s).1 < μ l
    | .pv f => ∀ v, μ (f v).1 < μ l
    | .ret _ => True

end RImpl

/-! ## Durable linearizability and detectability -/

section Lin

variable {P : Type} {Op R : Type}

/-- Real-time order: operation `a` returned before operation `b` was invoked. -/
def Prec (h : List (HEv P Op R)) (a b : ℕ) : Prop :=
  ∃ h₁ h₂, h = h₁ ++ h₂ ∧ (∃ r c, HEv.res a r c ∈ h₁) ∧ ∃ p o, HEv.inv b p o ∈ h₂

variable (O : ObjSpec)

/-- Legality of a sequential order `L` of operation instances from state `σ`: every operation
that returned a value returned the response prescribed by the specification. -/
def Legal (h : List (HEv P O.Op O.Resp)) : O.State → List (ℕ × O.Op) → Prop
  | _, [] => True
  | σ, (a, o) :: L =>
    (∀ r c, HEv.res a (some r) c ∈ h → r = (O.δ σ o).2) ∧ Legal h (O.δ σ o).1 L

/-- `L` is a *durable, detectable linearization* of the history `h` from state `σ`. -/
structure DLin (h : List (HEv P O.Op O.Resp)) (σ : O.State) (L : List (ℕ × O.Op)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  inv_of_mem : ∀ x ∈ L, ∃ p, HEv.inv x.1 p x.2 ∈ h
  mem_of_res : ∀ a r c, HEv.res a (some r) c ∈ h → a ∈ L.map Prod.fst
  not_mem_of_fail : ∀ a c, HEv.res a none c ∈ h → a ∉ L.map Prod.fst
  rt : L.Pairwise (fun x y => ¬ Prec h y.1 x.1)
  legal : Legal O h σ L

end Lin

namespace RImpl

variable [DecidableEq P] (A : RImpl O P)

/-- **Durable linearizability + detectability** (the correctness condition of the paper):
every finite execution from the initial configuration has a durable detectable linearization,
and `fail` is only returned by recovery functions. -/
def DurLinDet : Prop :=
  ∀ es, (∃ L, DLin O (A.exec A.init es).2 O.init L) ∧
    ∀ a, HEv.res a none false ∉ (A.exec A.init es).2

end RImpl

end Papers.PODC2020.DetectableSpace
