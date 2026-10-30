import Mathlib

/-!
# Shared memory with static permissions and split operations (model for Theorem 6.1)

Aguilera, Ben-David, Guerraoui, Marathe, Zablotchi, *The Impact of RDMA on Agreement*, PODC 2019
(arXiv:1905.12143v2), Section 3 and Section 6.

The model of Theorem 6.1: processes `P` access registers `R` (holding values `W`) of a memory that
never fails. Permissions are static: `canRead p r`, `canWrite p r` are fixed by the algorithm. A
read without permission returns `nak`; a write without permission returns `nak` and has no effect.

Every operation is *split*: a process invokes it (it becomes *pending*), later it takes effect
atomically at the memory (*linearization*, event `lin`), and its response is delivered to the
process later still. A process may have any number of pending operations, linearized in any order
(the paper allows one outstanding operation per object; algorithms obeying that restriction are a
special case). Processes are deterministic automata that act only in their own steps: a step
receives the oldest `k` undelivered responses (possibly none), updates the local state and invokes
a finite list of new operations. Initially every process invokes the operations given by `init`.

All event lists are executions (a `lin` of an operation that is not pending is a no-op, a `step`
with `k` larger than the number of available responses receives all of them): the set of
reachable configurations is that of the usual partial semantics. Crashes need no event: a crashed
process simply takes no more steps. Safety properties quantify over all executions.

*Synchronous runs* (`syncRun`) model the paper's common-case executions with the delay metric of
§3: an operation invoked at time `t` takes effect at time `t + 1` and its response is received at
time `t + 2`; computation is instantaneous. In round `t + 1` all operations invoked at time `t`
take effect, all reads before all writes (ties between simultaneous operations are broken
*read-first*), and then every non-crashed process takes one step receiving exactly the responses
that became available in round `t` (those of the operations it invoked at time `t - 1`). A set `C`
of processes is crashed from the start.
-/

namespace Podc.RDMAAgreement.LowerBound

/-- A memory operation: read register `r` or write `w` to register `r`. -/
inductive Op (R W : Type*) where
  | read (r : R)
  | write (r : R) (w : W)
  deriving DecidableEq

/-- Whether an operation is a read. -/
def Op.isRead {R W : Type*} : Op R W → Bool
  | .read _ => true
  | .write _ _ => false

/-- A response: the value read, an acknowledgement of a write, or a negative acknowledgement
(missing permission). -/
inductive Resp (W : Type*) where
  | val (w : W)
  | ack
  | nak
  deriving DecidableEq

/-- An algorithm with static permissions. `V` is the type of consensus inputs/decisions, `S` the
type of local states. -/
structure Alg (P V R W S : Type*) where
  /-- Initial content of the registers. -/
  mem0 : R → W
  /-- Static read permissions. -/
  canRead : P → R → Bool
  /-- Static write permissions. -/
  canWrite : P → R → Bool
  /-- Initial local state and initial invocations of a process with a given input. -/
  init : P → V → S × List (Op R W)
  /-- A step: given the local state and the delivered responses, the new local state and the new
  invocations. -/
  step : P → S → List (Op R W × Resp W) → S × List (Op R W)
  /-- The decision recorded in a local state, if any. -/
  decision : S → Option V

/-- Configurations: local states, memory, pending (invoked, not yet linearized) operations and
undelivered responses (in linearization order). -/
structure Cfg (P R W S : Type*) where
  st : P → S
  mem : R → W
  pend : P → List (Op R W)
  ready : P → List (Op R W × Resp W)

/-- Events: an operation of `p` takes effect, or `p` takes a step receiving `k` responses. -/
inductive Event (P R W : Type*) where
  | lin (p : P) (o : Op R W)
  | step (p : P) (k : ℕ)

/-- The process of an event. -/
def Event.proc {P R W : Type*} : Event P R W → P
  | .lin p _ => p
  | .step p _ => p

variable {P V R W S : Type*} [DecidableEq P] [DecidableEq R] [DecidableEq W]

namespace Alg

variable (A : Alg P V R W S)

/-- The effect of operation `o` of process `p` on memory `m`: new memory and response. -/
def access (p : P) (m : R → W) : Op R W → (R → W) × Resp W
  | .read r => (m, if A.canRead p r then .val (m r) else .nak)
  | .write r w => if A.canWrite p r then (Function.update m r w, .ack) else (m, .nak)

/-- One event. -/
def exec (c : Cfg P R W S) : Event P R W → Cfg P R W S
  | .lin p o =>
    if o ∈ c.pend p then
      { c with
        mem := (A.access p c.mem o).1
        pend := Function.update c.pend p ((c.pend p).erase o)
        ready := Function.update c.ready p (c.ready p ++ [(o, (A.access p c.mem o).2)]) }
    else c
  | .step p k =>
    { c with
      st := Function.update c.st p (A.step p (c.st p) ((c.ready p).take k)).1
      ready := Function.update c.ready p ((c.ready p).drop k)
      pend := Function.update c.pend p (c.pend p ++ (A.step p (c.st p) ((c.ready p).take k)).2) }

/-- Running a list of events. -/
def run (c : Cfg P R W S) (es : List (Event P R W)) : Cfg P R W S := es.foldl A.exec c

/-- The initial configuration for inputs `x`, where the processes in `C` never start (crashed from
the start); all other processes have invoked their initial operations. -/
def initCfg (x : P → V) (C : Finset P) : Cfg P R W S where
  st p := (A.init p (x p)).1
  mem := A.mem0
  pend p := if p ∈ C then [] else (A.init p (x p)).2
  ready _ := []

/-- `p` decides `v` in the execution `es` from inputs `x`: at some point of the execution the local
state of `p` records decision `v`. -/
def Decides (x : P → V) (es : List (Event P R W)) (p : P) (v : V) : Prop :=
  ∃ j, A.decision ((A.run (A.initCfg x ∅) (es.take j)).st p) = some v

/-- Uniform agreement in every (asynchronous) execution: any two decisions are equal (this also
makes decisions irrevocable). -/
def Agreement : Prop :=
  ∀ x es p q v w, A.Decides x es p v → A.Decides x es q w → v = w

/-- Validity in every (asynchronous) execution: a decided value is the input of some process. -/
def Validity : Prop :=
  ∀ x es p v, A.Decides x es p v → ∃ q, x q = v

section Sync

variable [Fintype P]

/-- The events of one synchronous round from configuration `c`: all pending operations take
effect, reads first (process by process), then writes; then every process outside `C` takes one
step receiving the responses that were available at the start of the round. -/
noncomputable def _root_.Podc.RDMAAgreement.LowerBound.roundEvs (C : Finset P) (c : Cfg P R W S) :
    List (Event P R W) :=
  ((Finset.univ : Finset P).toList.flatMap fun q =>
      ((c.pend q).filter Op.isRead).map (Event.lin q)) ++
    ((Finset.univ : Finset P).toList.flatMap fun q =>
      ((c.pend q).filter fun o => !o.isRead).map (Event.lin q)) ++
    (((Finset.univ : Finset P).toList.filter fun q => q ∉ C).map fun q =>
      Event.step q (c.ready q).length)

/-- The configuration at time `t` of the synchronous run with inputs `x` in which the processes of
`C` are crashed from the start (read-first tie breaking). -/
noncomputable def syncRun (x : P → V) (C : Finset P) : ℕ → Cfg P R W S
  | 0 => A.initCfg x C
  | t + 1 => A.run (syncRun x C t) (roundEvs C (syncRun x C t))

/-- The events of the first `t` rounds of `syncRun`. -/
noncomputable def syncEvs (x : P → V) (C : Finset P) : ℕ → List (Event P R W)
  | 0 => []
  | t + 1 => syncEvs x C t ++ roundEvs C (A.syncRun x C t)

/-- Termination in synchronous runs in which at most `f` processes are crashed (from the start):
every other process eventually decides. This is implied by termination under partial synchrony
(a synchronous run is a partially synchronous run with GST = 0), so assuming only this makes the
impossibility stronger. -/
def SyncTermination (f : ℕ) : Prop :=
  ∀ (x : P → V) (C : Finset P), C.card ≤ f → ∀ p ∉ C,
    ∃ t, (A.decision ((A.syncRun x C t).st p)).isSome

/-- The algorithm is *2-deciding* on inputs `x`: in the failure-free synchronous run, some process
has decided by time 2 (i.e. within two delays; a memory operation takes two delays). -/
def TwoDecidingOn (x : P → V) : Prop :=
  ∃ p, ∃ t ≤ 2, (A.decision ((A.syncRun x ∅ t).st p)).isSome

end Sync

end Alg

end Podc.RDMAAgreement.LowerBound
