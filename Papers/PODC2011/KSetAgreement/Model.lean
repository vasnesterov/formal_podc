import Mathlib
import Cslib.Computability.Distributed.FLP.Impossibility

/-!
# Asynchronous message passing for k-set agreement

Biely, Robinson, Schmid, *Easy Impossibility Proofs for k-Set Agreement in Message Passing
Systems*, PODC 2011 (arXiv 1103.3671v2).

We reuse the asynchronous crash-prone message-passing model of CSLib's FLP development
(`Cslib.FLP.Algorithm`): a global state is a multiset of in-flight messages plus local states, a
step is the receipt of one in-flight message by its destination (atomically: local transition,
sending, deciding), there is a stuttering step, and every process `p` initially has one in-flight
*wake-up* message `⟨p, inl b⟩`. A process that never receives anything is *initially dead*.

CSLib's algorithms have Boolean inputs (carried by the wake-up messages). For `k`-set agreement we
need inputs in an arbitrary type `V`. A `KAlgorithm` is a deterministic per-process state machine
whose initial state depends on the process id and its input, reacting to *events*: `none` (its
first step, "wake-up") and `some m` (receipt of a message with content `m`). `KAlgorithm.alg`
compiles it to a CSLib algorithm: the input of `p` is `ι p b` where `b` is the bit carried by `p`'s
wake-up message (for the k-set agreement model `ι p _ = x p`; the bit is only used in the reduction
to CSLib's binary consensus), and messages received before the wake-up message are buffered and
processed, in arrival order, right after the wake-up event. Buffering only restricts the schedules
(the first step of a process receives nothing), so impossibility results in this model imply
impossibility in the unbuffered model, and an algorithm for the buffered model is turned into one
for the unbuffered model by doing the buffering itself.

The decision is the `Option V` component of the local state, write-once by construction.
-/

namespace KSetAgreement

open Cslib Cslib.FLP

/-- A deterministic algorithm with inputs and decisions in `V`, messages `M`, internal states `S`.
Events: `none` = wake-up (the first step of the process), `some m` = receipt of content `m`.
Sends are pairs (destination, content). -/
structure KAlgorithm (P M S V : Type*) where
  /-- Initial internal state of process `p` with input `v`. -/
  init : P → V → S
  /-- New internal state after an event. -/
  step : P → Option M → S × Option V → S
  /-- Messages sent in reaction to an event. -/
  send : P → Option M → S × Option V → Multiset (P × M)
  /-- Decision taken in reaction to an event (`none` = no decision); only the first one counts. -/
  out : P → Option M → S × Option V → Option V

/-- Local state of the compiled algorithm: `inl buf` = not woken yet, with the contents received so
far (in arrival order); `inr st` = woken, with internal state and (write-once) decision. -/
abbrev Loc (M S V : Type*) := List M ⊕ (S × Option V)

variable {P M S V : Type*}

namespace KAlgorithm

variable (A : KAlgorithm P M S V)

/-- The local state after processing event `e`; the decision is write-once. -/
def apply (p : P) (e : Option M) (st : S × Option V) : S × Option V :=
  (A.step p e st, st.2.or (A.out p e st))

/-- Process a list of events: final local state and all messages sent. -/
def run (p : P) : List (Option M) → S × Option V → (S × Option V) × Multiset (P × M)
  | [], st => (st, 0)
  | e :: es, st => ((run p es (A.apply p e st)).1, A.send p e st + (run p es (A.apply p e st)).2)

/-- Wrap a (destination, content) pair as a CSLib message. -/
def wrap (qm : P × M) : Message P M := ⟨qm.1, Sum.inr qm.2⟩

/-- The decision recorded in a local state. -/
def decOf : Loc M S V → Option V
  | Sum.inl _ => none
  | Sum.inr st => st.2

/-- The new local state of `p` upon receiving `msg` (with input function `ι`). -/
def nextLoc (ι : P → Bool → V) (p : P) (msg : Bool ⊕ M) (l : Loc M S V) : Loc M S V :=
  match msg, l with
  | Sum.inl b, Sum.inl buf =>
      Sum.inr (A.run p (none :: buf.map some) (A.init p (ι p b), none)).1
  | Sum.inl _, Sum.inr st => Sum.inr st
  | Sum.inr m, Sum.inl buf => Sum.inl (buf ++ [m])
  | Sum.inr m, Sum.inr st => Sum.inr (A.apply p (some m) st)

/-- The messages sent by `p` upon receiving `msg`. -/
def sendLoc (ι : P → Bool → V) (p : P) (msg : Bool ⊕ M) (l : Loc M S V) :
    Multiset (P × M) :=
  match msg, l with
  | Sum.inl b, Sum.inl buf => (A.run p (none :: buf.map some) (A.init p (ι p b), none)).2
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr m, Sum.inr st => A.send p (some m) st

/-- The CSLib algorithm implementing `A`, where `ι p b` is the input of `p` if its wake-up message
carries the bit `b`, and `δ` maps decisions to CSLib's Boolean output field (only relevant for the
reduction to binary consensus). -/
def alg (ι : P → Bool → V) (δ : V → Bool) : Algorithm P M (Loc M S V) where
  init _ := Sum.inl []
  next m ps := A.nextLoc ι m.dest m.msg ps.state
  send m ps := (A.sendLoc ι m.dest m.msg ps.state).map wrap
  out m ps := (decOf (A.nextLoc ι m.dest m.msg ps.state)).map δ

/-- The algorithm with input assignment `x` (wake-up bits ignored). -/
abbrev algX (x : P → V) : Algorithm P M (Loc M S V) := A.alg (fun p _ => x p) (fun _ => false)

end KAlgorithm

/-- The decision of `p` in global state `s`. -/
def dec (s : State P M (Loc M S V)) (p : P) : Option V := KAlgorithm.decOf (s.proc p).state

/-- The set of values decided in `s`. -/
def decVals (s : State P M (Loc M S V)) : Set V := {v | ∃ p, dec s p = some v}

/-! ### Admissible runs -/

/-- Run predicates: which infinite executions of a CSLib algorithm (from the initial state with
wake-up bits `inp`) are admissible. -/
abbrev RunPred (P M L : Type*) :=
  Algorithm P M L → (P → Bool) → ωSequence (State P M L) → ωSequence (Action P M) → Prop

variable [DecidableEq P] [DecidableEq M]

/-- An infinite execution from the initial state. -/
def IsRun [Fintype P] {L : Type*} (a : Algorithm P M L) (inp : P → Bool)
    (ss : ωSequence (State P M L)) (xs : ωSequence (Action P M)) : Prop :=
  ss 0 = a.start inp ∧ a.lts.OmegaExecution ss xs

/-- `p` never takes a step (never receives a message) in the execution. -/
def NeverSteps (p : P) (xs : ωSequence (Action P M)) : Prop :=
  ∀ j m, xs j = some m → m.dest ≠ p

/-- **Initially dead processes** (Section VI): at most `f` processes never take a step, all
others are correct (receive every message sent to them). -/
def InitDead [Fintype P] {L : Type*} (f : ℕ) : RunPred P M L := fun a inp ss xs =>
  IsRun a inp ss xs ∧ ∃ dead : Finset P, dead.card ≤ f ∧ (∀ p ∈ dead, NeverSteps p xs) ∧
    ∀ p ∉ dead, ProcFair p ss xs

/-- **Theorem 2's failure pattern**: at most `f - 1` processes are initially dead and at most one
further process `c` crashes during the execution; everybody else is correct. -/
def OneCrash [Fintype P] {L : Type*} (f : ℕ) : RunPred P M L := fun a inp ss xs =>
  IsRun a inp ss xs ∧ ∃ dead : Finset P, dead.card + 1 ≤ f ∧ (∀ p ∈ dead, NeverSteps p xs) ∧
    ∃ c, (ProcFaulty c ss xs ∨ ProcFair c ss xs) ∧ ∀ p ∉ dead, p ≠ c → ProcFair p ss xs

/-- **Crash failures** (the FLP model `M_ASYNC`, Corollary 5): CSLib's admissible runs with at
most `f` faulty processes. -/
def Crash [Fintype P] {L : Type*} (f : ℕ) : RunPred P M L := fun a inp ss xs =>
  a.AdmissibleRun inp f ss xs

/-! ### k-set agreement -/

/-- Safety of `k`-set agreement: in every reachable state (for every input assignment `x`), at
most `k` different values are decided (**k-Agreement**, binding correct and faulty processes) and
every decided value is some process' input (**Validity**). -/
def KSafe [Fintype P] (A : KAlgorithm P M S V) (k : ℕ) : Prop :=
  ∀ (x : P → V) (inp : P → Bool) (s : State P M (Loc M S V)), (A.algX x).Reachable inp s →
    (decVals s).ncard ≤ k ∧ ∀ p v, dec s p = some v → ∃ q, x q = v

/-- **Termination** in the admissible runs `R`: every process that is not faulty decides. -/
def Terminates [Fintype P] (A : KAlgorithm P M S V) (R : RunPred P M (Loc M S V)) : Prop :=
  ∀ (x : P → V) (inp : P → Bool) ss xs, R (A.algX x) inp ss xs →
    ∀ p, ProcFaulty p ss xs ∨ ∃ j v, dec (ss j) p = some v

/-- `A` solves `k`-set agreement in the model given by the admissible runs `R`. -/
def SolvesKSA [Fintype P] (A : KAlgorithm P M S V) (k : ℕ) (R : RunPred P M (Loc M S V)) :
    Prop :=
  KSafe A k ∧ Terminates A R

end KSetAgreement
