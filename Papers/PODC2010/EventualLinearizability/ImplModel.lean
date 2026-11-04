import Papers.PODC2010.EventualLinearizability.Layer
import Papers.PODC2010.EventualLinearizability.Defs

/-!
# Implementations on top of a consistency layer (Section 4.1, Appendix B)

A general model of shared-object implementations that use *only* a consistency layer, as in
Theorems 2 and 3 of the paper.

* Every process runs a deterministic automaton (`Impl`). Its inputs are high-level invocations,
  deliveries of the consistency layer (sequences of submitted items) and local ticks (local
  computation steps, e.g. "upon periodic tick"). On every input it may change its state,
  submit items (arbitrary messages) to the layer, and return the response of its pending
  operation.
* An item is `(submitter, index of the submission at the submitter, payload)`, so items are
  unique.
* A run is driven by an adversary (`Adversary`): at every time `t + 1` it chooses, as a function
  of the time and the current configuration, an action: nothing, a high-level invocation at a
  process, a delivery of a sequence of items to a process, or a tick of a process. The
  adversary plays both the environment (invocations), the scheduler (asynchrony, crashes) and
  the consistency layer (deliveries); the layer's specification is imposed on the resulting
  `LayerRun` (`Admissible`).
* `hist`: the high-level history of a run; `layerRun`: the consistency-layer run (`S(i, t)` =
  the last sequence delivered to `p_i`; submission times from the log).
* `Admissible spec allowed adv correct`: crashed processes take no step after their crash,
  correct processes tick infinitely often, invocations respect the environment (`allowed`,
  e.g. single writer / single reader) and happen only at processes without a pending
  operation, and the layer run satisfies `spec` (e.g. Eventual Consistency, Eventual
  Consensus) for the set `correct`.
* `Terminates`: every operation invoked by a correct process eventually completes (an implied
  requirement of the paper; without it, an implementation that never responds would be
  eventually linearizable).
* `EventuallyLinearizable`: there is a single time `t_l` such that, in every admissible run,
  every finite prefix of the high-level history is weakly consistent, and, if all processes
  are correct, `t_l`-linearizable (the late operations being those not yet invoked at time
  `t_l`). This is weaker than the paper's Eventual Linearizability, uniform or not, so
  impossibility results for it are stronger.
-/

namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing

/-- An item submitted to the consistency layer: submitter, index of the submission at the
submitter, payload. -/
abbrev Item (P Msg : Type) := P × ℕ × Msg

/-- An implementation of a shared object on top of a consistency layer. -/
structure Impl (P Op Res Msg : Type) where
  /-- Local states. -/
  State : Type
  /-- Initial local states. -/
  init : P → State
  /-- Reaction to a high-level invocation: new state, submitted messages, response (if any). -/
  onInvoke : P → State → Op → State × List Msg × Option Res
  /-- Reaction to a delivery of the consistency layer. -/
  onDeliver : P → State → List (Item P Msg) → State × List Msg × Option Res
  /-- A local computation step. -/
  onTick : P → State → State × List Msg × Option Res

/-- The action at one time unit. -/
inductive Act (P Op Msg : Type) where
  | idle
  | invoke (i : P) (op : Op)
  | deliver (i : P) (s : List (Item P Msg))
  | tick (i : P)

namespace Act

variable {P Op Msg : Type}

/-- The process acting, if any. -/
def proc : Act P Op Msg → Option P
  | idle => none
  | invoke i _ => some i
  | deliver i _ => some i
  | tick i => some i

end Act

variable {P Op Res Msg : Type} [DecidableEq P]

/-- A configuration of a run. -/
structure Cfg (I : Impl P Op Res Msg) where
  /-- Local states. -/
  loc : P → I.State
  /-- Number of items submitted so far by each process. -/
  nsub : P → ℕ
  /-- All submitted items, with their submission times, in submission order. -/
  log : List (Item P Msg × ℕ)
  /-- The high-level history so far. -/
  hist : History P Unit Op Res
  /-- The last sequence delivered to each process. -/
  dlv : P → List (Item P Msg)

namespace Cfg

variable {I : Impl P Op Res Msg}

/-- The initial configuration. -/
def init (I : Impl P Op Res Msg) : Cfg I :=
  ⟨I.init, fun _ => 0, [], [], fun _ => []⟩

/-- Apply the output of a handler of process `i` at time `t`; `pre` are the high-level events
emitted before the response (the invocation, for an invocation). -/
def apply (C : Cfg I) (t : ℕ) (i : P) (out : I.State × List Msg × Option Res)
    (pre : History P Unit Op Res) : Cfg I where
  loc := Function.update C.loc i out.1
  nsub := Function.update C.nsub i (C.nsub i + out.2.1.length)
  log := C.log ++ (out.2.1.zipIdx (C.nsub i)).map fun mk => ((i, mk.2, mk.1), t)
  hist := C.hist ++ pre ++ (out.2.2.map fun r => Event.res i () r).toList
  dlv := C.dlv

/-- One step at time `t`. -/
def step (C : Cfg I) (t : ℕ) : Act P Op Msg → Cfg I
  | .idle => C
  | .invoke i op => C.apply t i (I.onInvoke i (C.loc i) op) [.inv i () op]
  | .deliver i s =>
    { C.apply t i (I.onDeliver i (C.loc i) s) [] with dlv := Function.update C.dlv i s }
  | .tick i => C.apply t i (I.onTick i (C.loc i)) []

end Cfg

/-- An adversary: the action at time `t + 1`, given `t` and the configuration at time `t`. -/
abbrev Adversary (I : Impl P Op Res Msg) := ℕ → Cfg I → Act P Op Msg

/-- The configuration at time `t` of the run driven by `adv`. -/
def run (I : Impl P Op Res Msg) (adv : Adversary I) : ℕ → Cfg I
  | 0 => Cfg.init I
  | t + 1 => (run I adv t).step (t + 1) (adv t (run I adv t))

/-- The action taken at time `t + 1`. -/
def actAt (I : Impl P Op Res Msg) (adv : Adversary I) (t : ℕ) : Act P Op Msg :=
  adv t (run I adv t)

/-- The high-level history at time `t`. -/
def hist (I : Impl P Op Res Msg) (adv : Adversary I) (t : ℕ) : History P Unit Op Res :=
  (run I adv t).hist

open Classical in
/-- The consistency-layer run of an execution, for a set of correct processes. -/
noncomputable def layerRun (I : Impl P Op Res Msg) (adv : Adversary I) (correct : Set P) :
    LayerRun P (Item P Msg) where
  S i t := (run I adv t).dlv i
  sub it := if h : ∃ s t, (it, s) ∈ (run I adv t).log then some (it.1, Nat.find h) else none
  correct := correct

/-- Admissible runs: crashes, fairness, environment, and the specification of the layer. -/
structure Admissible (I : Impl P Op Res Msg) (spec : LayerRun P (Item P Msg) → Prop)
    (allowed : P → Op → Prop) (adv : Adversary I) (correct : Set P) : Prop where
  /-- A faulty process takes no step after its crash. -/
  crash : ∀ i ∉ correct, ∃ tc, ∀ t ≥ tc, (actAt I adv t).proc ≠ some i
  /-- A correct process takes infinitely many local steps. -/
  fair : ∀ i ∈ correct, ∀ t, ∃ t' ≥ t, actAt I adv t' = .tick i
  /-- Invocations are allowed and happen only at processes without a pending operation. -/
  env : ∀ t i op, actAt I adv t = .invoke i op →
    allowed i op ∧ ∃ M, restrictP (hist I adv t) i = seqHist M
  /-- The consistency layer satisfies its specification. -/
  layer : spec (layerRun I adv correct)

/-- Termination: every operation invoked by a correct process eventually completes. -/
def Terminates (I : Impl P Op Res Msg) (spec : LayerRun P (Item P Msg) → Prop)
    (allowed : P → Op → Prop) : Prop :=
  ∀ adv correct, Admissible I spec allowed adv correct → ∀ (a : OpId P Unit) t,
    a.p ∈ correct → Invoked (hist I adv t) a → ∃ t', Completed (hist I adv t') a

/-- Eventual Linearizability of an implementation (weakened, see the module docstring): one
time `t_l` for all admissible runs; every prefix of the history is weakly consistent and, in
runs without crashes, `t_l`-linearizable. -/
def EventuallyLinearizable (I : Impl P Op Res Msg) (spec : LayerRun P (Item P Msg) → Prop)
    (allowed : P → Op → Prop) (objSpec : SeqSpec P Unit Op Res) : Prop :=
  ∃ tl, ∀ adv correct, Admissible I spec allowed adv correct → ∀ t,
    WeaklyConsistent objSpec (hist I adv t) ∧
    (correct = Set.univ →
      TLinearizable objSpec (hist I adv t) {a | ¬ Invoked (hist I adv tl) a})

/-! ### Single-writer single-reader binary register -/

/-- Operations of a binary register. -/
inductive RWOp
  | read
  | write (b : Bool)
  deriving DecidableEq

/-- Transition function: `read` returns `some b`, `write` returns `none`. -/
def rwδ : Bool → RWOp → Bool × Option Bool
  | b, .read => (b, some b)
  | _, .write v => (v, none)

/-- The sequential specification of a binary register, initially `false`. -/
def regSpec : SeqSpec (Fin 2) Unit RWOp (Option Bool) := fun _ => detSpec false rwδ

/-- Single writer `p0`, single reader `p1`. -/
def swsr : Fin 2 → RWOp → Prop
  | 0, .write _ => True
  | 1, .read => True
  | _, _ => False

/-- The layer specification "Eventual Consistency". -/
def ecSpec {Item : Type} : LayerRun (Fin 2) Item → Prop := fun R => R.EventualConsistency

/-- The layer specification "Eventual Consensus" (Eventual Stability in each run). -/
def eConsSpec {Item : Type} : LayerRun (Fin 2) Item → Prop := fun R => R.EventualConsensus

end Podc.EventualLinearizability
