import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/TransactionalMemory/Model.lean

/-!
# On the Liveness of Transactional Memory (PODC 2012): the model

Bushkov, Guerraoui, Kapałka. *On the liveness of transactional memory.* PODC 2012.

This file fixes the model:

* **Histories.** Transactional operations (`x.read`, `x.write v`, `tryC`) and their responses
  (a value, `ok`, a commit event `C`, an abort event `A`), §2.2 of the paper. A history is a list
  of invocation and response events (`Ev`). A response event records the invocation it answers
  (in a well-formed history this is determined by the history, so no information is added).
* **Transactions.** The `j`-th transaction of process `k` is `(k, j)`: the events of `k` after its
  `j`-th commit/abort event and up to its `j+1`-st. `info h` computes, by one left-to-right pass,
  everything we need about the transactions of `h`: how many transactions of each process are
  complete, which transactions have begun, the successful reads/writes of every transaction, which
  transactions committed, the pending invocation of every process, and the number of complete
  transactions of every process when a transaction began (used for the real-time order).
* **Executions.** A TM implementation is modelled as an arbitrary (nondeterministic) agent that,
  each time a process with a pending invocation is scheduled, decides — knowing the whole execution
  so far — whether that step of the process returns a response (and which one) or is an internal
  step of the implementation (`tau`). Any implementation from base objects induces such an agent,
  so impossibility results in this model hold for all implementations. The environment (processes
  and scheduler) decides which process takes the next step and, for an idle process, which
  operation it invokes. This is the step-based model of the chapter version (§2.2 of
  Bushkov–Guerraoui, *Liveness in Transactional Memory*), which distinguishes a process that keeps
  taking steps inside an operation that never returns from a crashed process.
* **Faults** (§2.3): a process crashes in an infinite execution if it takes finitely many steps; it is
  parasitic if from some point on it keeps invoking operations but is never aborted and never
  invokes `tryC`; it is correct if it neither crashes nor is parasitic. It makes progress if it is
  returned infinitely many commit events.
* **TM-liveness properties** (§3) are predicates on infinite executions containing local progress.
  **Fault-prone systems** (§2.3): crashes and parasitic processes allowed; only crashes
  (parasitic-free); only parasitic processes (crash-free).
-/

namespace Podc.TMLiveness

/-! ### Operations, events, histories -/

/-- Invocation events (§2.2): `x.read`, `x.write(v)`, and the commit request `tryC`. -/
inductive Inv (X V : Type*) where
  | read (x : X)
  | write (x : X) (v : V)
  | tryC
  deriving DecidableEq

/-- Response events (§2.2): a value read, `ok`, a commit event `C`, or an abort event `A`. -/
inductive Res (V : Type*) where
  | val (v : V)
  | ok
  | commit
  | abort
  deriving DecidableEq

variable {P X V : Type*}

/-- `r` is a legal response to the invocation `i`: every operation may be aborted, a read
returns a value, a write returns `ok`, and `tryC` returns a commit event. -/
def Res.Fits : Inv X V → Res V → Prop
  | .read _, r => r = .abort ∨ ∃ v, r = .val v
  | .write _ _, r => r = .abort ∨ r = .ok
  | .tryC, r => r = .abort ∨ r = .commit

/-- Whether a response ends the transaction (commit or abort event). -/
def Res.isEnd : Res V → Bool
  | .commit => true
  | .abort => true
  | _ => false

/-- Whether a response is a commit event. -/
def Res.isCommit : Res V → Bool
  | .commit => true
  | _ => false

/-- History events: invocations and responses of process `k`. A response records the invocation
it answers. -/
inductive Ev (P X V : Type*) where
  | inv (k : P) (i : Inv X V)
  | res (k : P) (i : Inv X V) (r : Res V)

/-- The process of an event. -/
def Ev.proc : Ev P X V → P
  | .inv k _ => k
  | .res k _ _ => k

/-- A successfully completed read or write (`x.read → v` or `x.write(v) → ok`). -/
inductive Op (X V : Type*) where
  | read (x : X) (v : V)
  | write (x : X) (v : V)
  deriving DecidableEq

/-- The completed read/write operation formed by an invocation and its response, if any. -/
def opOf : Inv X V → Res V → Option (Op X V)
  | .read x, .val v => some (.read x v)
  | .write x v, .ok => some (.write x v)
  | _, _ => none

/-! ### Transactions of a history -/

/-- Transaction identifiers: `(k, j)` is the `j`-th transaction of process `k` (from `0`). -/
abbrev TxId (P : Type*) := P × ℕ

/-- Everything we need about the transactions of a history, computed in one pass. -/
structure HInfo (P X V : Type*) where
  /-- Number of complete (committed or aborted) transactions of each process. -/
  cnt : P → ℕ
  /-- Whether the transaction has at least one event. -/
  began : TxId P → Bool
  /-- For a begun transaction: `cnt` at its first event (which transactions of every process were
  complete when it began). -/
  snap : TxId P → P → ℕ
  /-- Successful reads and writes of the transaction, in order. -/
  ops : TxId P → List (Op X V)
  /-- Whether the transaction is committed. -/
  committed : TxId P → Bool
  /-- The pending invocation of each process (`none` if the process is idle). -/
  pend : P → Option (Inv X V)

variable [DecidableEq P]

/-- The empty history. -/
def HInfo.init : HInfo P X V :=
  ⟨fun _ => 0, fun _ => false, fun _ _ => 0, fun _ => [], fun _ => false, fun _ => none⟩

/-- Processing one more event. Events of process `k` belong to transaction `(k, cnt k)`. -/
def HInfo.step (s : HInfo P X V) : Ev P X V → HInfo P X V
  | .inv k i =>
    { s with
      began := fun t => s.began t || decide (t = (k, s.cnt k))
      snap := fun t => if t = (k, s.cnt k) ∧ s.began t = false then s.cnt else s.snap t
      pend := Function.update s.pend k (some i) }
  | .res k i r =>
    { s with
      cnt := if r.isEnd then Function.update s.cnt k (s.cnt k + 1) else s.cnt
      ops := fun t => if t = (k, s.cnt k) then s.ops t ++ (opOf i r).toList else s.ops t
      committed := fun t => s.committed t || (decide (t = (k, s.cnt k)) && r.isCommit)
      pend := Function.update s.pend k none }

/-- The transaction information of a history. -/
def info (h : List (Ev P X V)) : HInfo P X V := h.foldl HInfo.step HInfo.init

/-- Transaction `t` has at least one event in `h`. -/
def Started (h : List (Ev P X V)) (t : TxId P) : Prop := (info h).began t = true

/-- Transaction `t` is complete (its commit or abort event is in `h`). -/
def Complete (h : List (Ev P X V)) (t : TxId P) : Prop := t.2 < (info h).cnt t.1

/-- Transaction `t` is committed in `h`. -/
def Committed (h : List (Ev P X V)) (t : TxId P) : Prop := (info h).committed t = true

/-- Transaction `t` is commit-pending in `h`: it ends with a commit request `tryC`. -/
def CommitPending (h : List (Ev P X V)) (t : TxId P) : Prop :=
  t.2 = (info h).cnt t.1 ∧ (info h).pend t.1 = some .tryC

/-- The successful reads and writes of transaction `t`. -/
def txOps (h : List (Ev P X V)) (t : TxId P) : List (Op X V) := (info h).ops t

/-- Real-time order (§2.2): `t₁ <_h t₂` iff `t₁` is complete and its last event precedes the
first event of `t₂`, i.e. some prefix of `h` contains all of `t₁` and nothing of `t₂`. -/
def Prec (h : List (Ev P X V)) (t₁ t₂ : TxId P) : Prop :=
  ∃ u v, h = u ++ v ∧ Complete u t₁ ∧ ¬ Started u t₂ ∧ Started h t₂

/-! ### Executions -/

/-- Steps of an execution: an invocation or response event, or an internal step of the TM
implementation taken by a process inside a pending operation. -/
inductive Step (P X V : Type*) where
  | ev (e : Ev P X V)
  | tau (k : P)

/-- The process taking a step. -/
def Step.proc : Step P X V → P
  | .ev e => e.proc
  | .tau k => k

/-- The event of a step, if any. -/
def Step.ev? : Step P X V → Option (Ev P X V)
  | .ev e => some e
  | .tau _ => none

/-- The history of a finite execution: its invocation and response events. -/
def hist (h : List (Step P X V)) : List (Ev P X V) := h.filterMap Step.ev?

/-- The pending invocation of `k` after the finite execution `h`. -/
def pending (h : List (Step P X V)) (k : P) : Option (Inv X V) := (info (hist h)).pend k

/-- A TM implementation. When process `k`, with a pending invocation, takes a step after the
finite execution `h`, the implementation decides (nondeterministically, with full knowledge of
`h`) whether the step is a response `some r` or an internal step `none`. It always has some
choice, and its responses fit the pending invocation. -/
structure TM (P X V : Type*) [DecidableEq P] where
  /-- Possible outcomes of a step of `k` after `h`. -/
  next : List (Step P X V) → P → Set (Option (Res V))
  next_nonempty : ∀ h k, (next h k).Nonempty
  next_fits : ∀ h k i r, pending h k = some i → some r ∈ next h k → r.Fits i

/-- Steps that may follow the finite execution `h`. An idle process invokes any operation (the
environment's choice); a process with a pending invocation takes a step decided by the TM. -/
def ValidStep (M : TM P X V) (h : List (Step P X V)) : Step P X V → Prop
  | .ev (.inv k _) => pending h k = none
  | .ev (.res k i r) => pending h k = some i ∧ some r ∈ M.next h k
  | .tau k => (pending h k).isSome ∧ none ∈ M.next h k

/-- Finite executions of `M`. -/
inductive Reachable (M : TM P X V) : List (Step P X V) → Prop
  | nil : Reachable M []
  | snoc {h s} : Reachable M h → ValidStep M h s → Reachable M (h ++ [s])

/-- The first `t` steps of an infinite sequence of steps. -/
def prefixOf (α : ℕ → Step P X V) : ℕ → List (Step P X V)
  | 0 => []
  | t + 1 => prefixOf α t ++ [α t]

/-- Infinite executions of `M`. -/
def IsExec (M : TM P X V) (α : ℕ → Step P X V) : Prop :=
  ∀ t, ValidStep M (prefixOf α t) (α t)

/-! ### Faults and progress (§2.3, §3.1) -/

/-- Process `k` crashes in `α`: it takes finitely many steps. -/
def Crashes (α : ℕ → Step P X V) (k : P) : Prop := {t | (α t).proc = k}.Finite

/-- Process `k` is parasitic in `α`: it invokes infinitely many operations, but invokes `tryC`
and is returned an abort event only finitely often. -/
def Parasitic (α : ℕ → Step P X V) (k : P) : Prop :=
  {t | ∃ i, α t = .ev (.inv k i)}.Infinite ∧ {t | α t = .ev (.inv k .tryC)}.Finite ∧
    {t | ∃ i, α t = .ev (.res k i .abort)}.Finite

/-- Process `k` is correct in `α`: it neither crashes nor is parasitic. -/
def Correct (α : ℕ → Step P X V) (k : P) : Prop := ¬ Crashes α k ∧ ¬ Parasitic α k

/-- Process `k` makes progress in `α`: it is returned infinitely many commit events. -/
def Progress (α : ℕ → Step P X V) (k : P) : Prop :=
  {t | ∃ i, α t = .ev (.res k i .commit)}.Infinite

/-! ### TM-liveness properties (§3, §5.1) -/

/-- Local progress: every correct process makes progress. -/
def LocalProgress (α : ℕ → Step P X V) : Prop := ∀ k, Correct α k → Progress α k

/-- A TM-liveness property: a property of infinite executions implied by local progress
(Definition 1). Our properties are sets of executions rather than of fair histories; every set of
fair histories induces one, so the impossibility results below cover the paper's properties. -/
def IsTMLiveness (L : (ℕ → Step P X V) → Prop) : Prop := ∀ α, LocalProgress α → L α

/-- Process `k` runs alone in `α` (§3.2.3 of the PODC paper): `k` is correct and no other process
is correct. -/
def RunsAlone (α : ℕ → Step P X V) (k : P) : Prop := Correct α k ∧ ∀ k', k' ≠ k → ¬ Correct α k'

/-- Solo progress: a process that runs alone makes progress. -/
def SoloProgress (α : ℕ → Step P X V) : Prop := ∀ k, RunsAlone α k → Progress α k

/-- Global progress: if some process is correct, some correct process makes progress. -/
def GlobalProgress (α : ℕ → Step P X V) : Prop :=
  (∃ k, Correct α k) → ∃ k, Correct α k ∧ Progress α k

/-- Definition 4: a TM-liveness property is nonblocking if in each of its executions a process that
runs alone makes progress. -/
def NonBlocking (L : (ℕ → Step P X V) → Prop) : Prop := ∀ α, L α → SoloProgress α

/-- Definition 5: a TM-liveness property is biprogressing if in each of its executions with at
least two correct processes at least two processes make progress. -/
def Biprogressing (L : (ℕ → Step P X V) → Prop) : Prop :=
  ∀ α, L α → (∃ k₁ k₂, k₁ ≠ k₂ ∧ Correct α k₁ ∧ Correct α k₂) →
    ∃ k₁ k₂, k₁ ≠ k₂ ∧ Progress α k₁ ∧ Progress α k₂

/-! ### Fault-prone systems and what a TM ensures -/

/-- The three fault-prone systems of §2.3: any number of processes may crash or be parasitic;
processes may crash but no process is parasitic (parasitic-free); processes may be parasitic but
no process crashes (crash-free). -/
inductive FaultProne where
  | crashOrParasitic
  | parasiticFree
  | crashFree

/-- The executions a fault-prone system admits. -/
def FaultProne.Admissible : FaultProne → (ℕ → Step P X V) → Prop
  | .crashOrParasitic, _ => True
  | .parasiticFree, α => ∀ k, ¬ Parasitic α k
  | .crashFree, α => ∀ k, ¬ Crashes α k

/-- `M` ensures the TM-liveness property `L` in the system `sys`: every infinite execution of `M`
admitted by `sys` satisfies `L`. -/
def EnsuresLiveness (M : TM P X V) (sys : FaultProne) (L : (ℕ → Step P X V) → Prop) : Prop :=
  ∀ α, IsExec M α → sys.Admissible α → L α

/-- `M` ensures the safety property `S`: the history of every finite execution satisfies `S`. -/
def EnsuresSafety (M : TM P X V) (S : List (Ev P X V) → Prop) : Prop :=
  ∀ h, Reachable M h → S (hist h)

end Podc.TMLiveness
