import Mathlib
import Cslib.Computability.Distributed.SharedMemory.History
import Cslib.Foundations.Combinatorics.Digraph.Walk

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Model.lean

/-!
# Asynchronous message passing with process crashes and channel disconnections

The model of Naser-Pastoriza, Chockler, Gotsman, Ryabinin (PODC 2025, §2): processes `P`
(finitely many in applications) communicate over a complete network of unidirectional channels
`(q, p)`; processes may crash and channels may *disconnect* (from some point on, drop every
message). The processes implement an object (or task) given by a CSLib `ObjSpec` `A`; histories
are CSLib `Label`s, so that `Cslib.SharedMemory.IsLinearization` applies directly.

* An algorithm (`Algorithm P A M L`) is deterministic and event driven: `handle p i l` is the
  reaction of process `p` in local state `l` to a local input `i` — an invocation, a spontaneous
  step (`tick c`, where `c` is the reading of the local clock; asynchronous algorithms ignore it)
  or the reception of a message. It returns the new state, the messages sent and possibly a
  response. Transitions are total: a process blocked at a `wait` simply keeps the received
  information in its state.
* Channels are FIFO (`Config.chan q p`, oldest first); `deliver q p` delivers the head of the
  channel `q → p` (a no-op if it is empty). FIFO channels only restrict the adversary.
* Well-formed clients: an invocation at a process with a pending operation is ignored, and a
  response is recorded only for a pending operation (`Config.pend`).
* **Failures are not events.** In an asynchronous system a crashed process is a process that stops
  taking steps, and a disconnected channel is a channel on which the messages from some point on
  are never delivered (with FIFO channels the delivered messages always form a prefix). So the
  semantics of finite executions is failure free, and a *failure pattern* `f = (procs, chans)`
  (processes and channels allowed to fail) only enters the fairness condition `Fair f`: every
  process that is correct (not in `f.procs`, or in `f.procs` but taking infinitely many steps)
  takes infinitely many spontaneous steps, and every channel between correct processes that is not
  in `f.chans` eventually delivers every message. Fair `f`-executions are exactly the
  `f`-compliant fair executions of the paper.
* Liveness (`ObstructionFree f T`, `WaitFree f T`): the `(f, T)`-obstruction-freedom and
  `(f, T)`-wait-freedom of the paper; `PartiallySynchronous` adds the partially synchronous
  timing assumptions (GST, `Δ`, non-drifting clocks after GST) for timed executions.
* Ghost counters `sent q p` / `dlv q p` count the messages ever sent / delivered on a channel.
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

/-- Local inputs of a process. -/
inductive Input (P Op M : Type) where
  /-- Invocation of an operation. -/
  | invoke (o : Op)
  /-- Spontaneous step, with the reading `c` of the local clock. -/
  | tick (c : ℕ)
  /-- Reception of message `m` from `q`. -/
  | recv (q : P) (m : M)

/-- A deterministic message-passing algorithm implementing `A`, with messages `M` and local
states `L`. -/
structure Algorithm (P : Type) (A : ObjSpec) (M L : Type) where
  /-- Initial local states. -/
  init : P → L
  /-- `handle p i l`: new local state, messages sent `(destination, message)`, response. -/
  handle : P → Input P A.Op M → L → L × List (P × M) × Option A.Resp

/-- Global configurations. -/
structure Config (P : Type) (A : ObjSpec) (M L : Type) where
  /-- Local states. -/
  loc : P → L
  /-- The pending operation of each process. -/
  pend : P → Option A.Op
  /-- `chan q p`: messages in transit from `q` to `p`, oldest first. -/
  chan : P → P → List M
  /-- Ghost: number of messages ever sent on `q → p`. -/
  sent : P → P → ℕ
  /-- Ghost: number of messages ever delivered on `q → p`. -/
  dlv : P → P → ℕ

/-- Events (scheduler choices). -/
inductive Event (P : Type) (A : ObjSpec) where
  /-- Process `p` invokes `o`. -/
  | invoke (p : P) (o : A.Op)
  /-- Process `p` takes a spontaneous step, reading `c` on its clock. -/
  | tick (p : P) (c : ℕ)
  /-- The head of the channel `q → p` is delivered to `p`. -/
  | deliver (q p : P)

variable {P : Type} {A : ObjSpec} {M L : Type}

/-- The process taking the step. -/
def Event.owner : Event P A → P
  | .invoke p _ => p
  | .tick p _ => p
  | .deliver _ p => p

@[simp] lemma Event.owner_invoke (p : P) (o : A.Op) : (Event.invoke p o).owner = p := rfl
@[simp] lemma Event.owner_tick (p : P) (c : ℕ) : (Event.tick p c : Event P A).owner = p := rfl
@[simp] lemma Event.owner_deliver (q p : P) : (Event.deliver q p : Event P A).owner = p := rfl

/-- The event is an invocation. -/
def Event.IsInvoke : Event P A → Prop
  | .invoke _ _ => True
  | _ => False

/-- The response label produced by a step of `p` (only for a pending operation). -/
def respOut (p : P) : Option A.Op → Option A.Resp → List (Label P A)
  | some _, some x => [.ret p x]
  | _, _ => []

/-- The pending operation after a step with response `r`. -/
def pendAfter : Option A.Op → Option A.Resp → Option A.Op
  | some _, some _ => none
  | o, _ => o

variable [DecidableEq P]

/-- The messages of `out` addressed to `b`. -/
def msgsTo (out : List (P × M)) (b : P) : List M :=
  (out.filter fun x => decide (x.1 = b)).map Prod.snd

/-- Apply a local transition of `p` (new state, messages sent, response). -/
def Config.apply (C : Config P A M L) (p : P) (r : L × List (P × M) × Option A.Resp) :
    Config P A M L × List (Label P A) :=
  ({ loc := Function.update C.loc p r.1
     pend := Function.update C.pend p (pendAfter (C.pend p) r.2.2)
     chan := fun a b => if a = p then C.chan a b ++ msgsTo r.2.1 b else C.chan a b
     sent := fun a b => if a = p then C.sent a b + (msgsTo r.2.1 b).length else C.sent a b
     dlv := C.dlv }, respOut p (C.pend p) r.2.2)

/-- Remove the head of the channel `q → p` (the rest is `rest`). -/
def Config.pop (C : Config P A M L) (q p : P) (rest : List M) : Config P A M L :=
  { C with
    chan := fun a b => if a = q ∧ b = p then rest else C.chan a b
    dlv := fun a b => if a = q ∧ b = p then C.dlv a b + 1 else C.dlv a b }

namespace Algorithm

variable (Alg : Algorithm P A M L)

/-- The initial configuration. -/
def initCfg : Config P A M L := ⟨Alg.init, fun _ => none, fun _ _ => [], fun _ _ => 0, fun _ _ => 0⟩

/-- One step: the new configuration and the history labels produced. -/
def step (C : Config P A M L) : Event P A → Config P A M L × List (Label P A)
  | .invoke p o =>
    match C.pend p with
    | some _ => (C, [])
    | none =>
      let r := ({ C with pend := Function.update C.pend p (some o) } : Config P A M L).apply p
        (Alg.handle p (.invoke o) (C.loc p))
      (r.1, .inv p o :: r.2)
  | .tick p c => C.apply p (Alg.handle p (.tick c) (C.loc p))
  | .deliver q p =>
    match C.chan q p with
    | [] => (C, [])
    | m :: rest => (C.pop q p rest).apply p (Alg.handle p (.recv q m) (C.loc p))

/-- The configuration after a finite sequence of events. -/
def run (C : Config P A M L) : List (Event P A) → Config P A M L
  | [] => C
  | e :: E => run (Alg.step C e).1 E

/-- The history (invocations and responses) of a finite sequence of events. -/
def hist (C : Config P A M L) : List (Event P A) → List (Label P A)
  | [] => []
  | e :: E => (Alg.step C e).2 ++ hist (Alg.step C e).1 E

@[simp] lemma run_nil (C : Config P A M L) : Alg.run C [] = C := rfl
@[simp] lemma run_cons (C : Config P A M L) (e : Event P A) (E : List (Event P A)) :
    Alg.run C (e :: E) = Alg.run (Alg.step C e).1 E := rfl
@[simp] lemma hist_nil (C : Config P A M L) : Alg.hist C [] = [] := rfl
@[simp] lemma hist_cons (C : Config P A M L) (e : Event P A) (E : List (Event P A)) :
    Alg.hist C (e :: E) = (Alg.step C e).2 ++ Alg.hist (Alg.step C e).1 E := rfl

lemma run_append (C : Config P A M L) (E F : List (Event P A)) :
    Alg.run C (E ++ F) = Alg.run (Alg.run C E) F := by
  induction E generalizing C with
  | nil => rfl
  | cons e E ih => exact ih _

lemma hist_append (C : Config P A M L) (E F : List (Event P A)) :
    Alg.hist C (E ++ F) = Alg.hist C E ++ Alg.hist (Alg.run C E) F := by
  induction E generalizing C with
  | nil => rfl
  | cons e E ih => simp [ih, List.append_assoc]

/-! ### Infinite executions -/

/-- The configuration after the first `t` events of the infinite execution `ev` (from the
initial configuration). -/
def cfgAt (ev : ℕ → Event P A) : ℕ → Config P A M L
  | 0 => Alg.initCfg
  | t + 1 => (Alg.step (cfgAt ev t) (ev t)).1

/-- The labels produced by the event at time `t`. -/
def labAt (ev : ℕ → Event P A) (t : ℕ) : List (Label P A) := (Alg.step (Alg.cfgAt ev t) (ev t)).2

/-- The first `t` events. -/
def pre (ev : ℕ → Event P A) (t : ℕ) : List (Event P A) := (List.range t).map ev

omit [DecidableEq P] in
lemma pre_succ (ev : ℕ → Event P A) (t : ℕ) : pre ev (t + 1) = pre ev t ++ [ev t] := by
  simp [pre, List.range_succ]

lemma cfgAt_eq_run (ev : ℕ → Event P A) (t : ℕ) : Alg.cfgAt ev t = Alg.run Alg.initCfg (pre ev t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [pre_succ, run_append, ← ih]; rfl

end Algorithm

/-! ### Failure patterns and the residual graph -/

/-- A failure pattern: the processes and the channels that may fail. -/
structure FailurePattern (P : Type) where
  /-- Processes that may crash. -/
  procs : Set P
  /-- Channels that may disconnect. -/
  chans : Set (P × P)

namespace FailurePattern

/-- The digraph of channels that do not fail (vertices of `f.procs` are removed by
`ReachableAvoiding`). -/
def residual (f : FailurePattern P) : Digraph P where
  Adj q p := (q, p) ∉ f.chans

/-- `f.Reach q p`: `p` is reachable from `q` in the residual graph `G \ f` (both correct). -/
def Reach (f : FailurePattern P) (q p : P) : Prop := f.residual.ReachableAvoiding f.procs q p

/-- `f.Edge q p`: the channel `q → p` is an edge of `G \ f`. -/
def Edge (f : FailurePattern P) (q p : P) : Prop := q ∉ f.procs ∧ p ∉ f.procs ∧ (q, p) ∉ f.chans

/-- `X` is closed under predecessors in `G \ f` (unreachable from its complement). -/
def Closed (f : FailurePattern P) (X : Set P) : Prop := ∀ q p, f.Edge q p → p ∈ X → q ∈ X

end FailurePattern

namespace Algorithm

variable (Alg : Algorithm P A M L)

/-! ### Fairness and liveness -/

/-- `p` crashes in `ev` (under `f`): it may crash and takes only finitely many steps. -/
def Crashed (f : FailurePattern P) (ev : ℕ → Event P A) (p : P) : Prop :=
  p ∈ f.procs ∧ ∃ T, ∀ t ≥ T, (ev t).owner ≠ p

/-- `ev` is a fair `f`-compliant execution: correct processes take infinitely many spontaneous
steps, and channels between correct processes that are not allowed to fail are reliable (FIFO: a
non-empty channel is eventually served). -/
def Fair (f : FailurePattern P) (ev : ℕ → Event P A) : Prop :=
  (∀ p, ¬ Crashed f ev p → ∀ T, ∃ t ≥ T, ∃ c, ev t = .tick p c) ∧
  ∀ q p, ¬ Crashed f ev q → ¬ Crashed f ev p → (q, p) ∉ f.chans → ∀ T,
    (Alg.cfgAt ev T).chan q p ≠ [] → ∃ t ≥ T, ev t = .deliver q p

/-- `q` invokes an operation at time `t` (an effective invocation). -/
def Invokes (ev : ℕ → Event P A) (t : ℕ) (q : P) : Prop :=
  ∃ o, ev t = .invoke q o ∧ (Alg.cfgAt ev t).pend q = none

/-- The operation invoked by `p` at `t₀` eventually executes solo: from some time on, every
operation concurrent with it (pending then, or invoked later) is invoked by a crashed process. -/
def EventuallySolo (f : FailurePattern P) (ev : ℕ → Event P A) (p : P) (t₀ : ℕ) : Prop :=
  ∃ T₁ > t₀, (∀ t ≥ T₁, ∀ q, Alg.Invokes ev t q → Crashed f ev q) ∧
    ∀ q ≠ p, (Alg.cfgAt ev T₁).pend q ≠ none → Crashed f ev q

/-- The operation invoked by `p` at `t₀` returns. -/
def Returns (ev : ℕ → Event P A) (p : P) (t₀ : ℕ) : Prop :=
  ∃ t ≥ t₀, ∃ r, Label.ret p r ∈ Alg.labAt ev t

/-- `(f, T)`-obstruction-freedom. -/
def ObstructionFree (f : FailurePattern P) (T : Set P) : Prop :=
  ∀ ev, Alg.Fair f ev → ∀ p ∈ T, ∀ t₀ o, ev t₀ = .invoke p o → (Alg.cfgAt ev t₀).pend p = none →
    Alg.EventuallySolo f ev p t₀ → Alg.Returns ev p t₀

/-- `(f, T)`-wait-freedom. -/
def WaitFree (f : FailurePattern P) (T : Set P) : Prop :=
  ∀ ev, Alg.Fair f ev → ∀ p ∈ T, ∀ t₀ o, ev t₀ = .invoke p o → (Alg.cfgAt ev t₀).pend p = none →
    Alg.Returns ev p t₀

/-- `(F, τ)`-obstruction-freedom. -/
def ObstructionFreeOn (F : Set (FailurePattern P)) (τ : FailurePattern P → Set P) : Prop :=
  ∀ f ∈ F, Alg.ObstructionFree f (τ f)

/-- `(F, τ)`-wait-freedom. -/
def WaitFreeOn (F : Set (FailurePattern P)) (τ : FailurePattern P → Set P) : Prop :=
  ∀ f ∈ F, Alg.WaitFree f (τ f)

lemma waitFree_obstructionFree {f : FailurePattern P} {T : Set P} (h : Alg.WaitFree f T) :
    Alg.ObstructionFree f T :=
  fun ev hf p hp t₀ o he hpend _ => h ev hf p hp t₀ o he hpend

/-- Safety: every finite execution has a history satisfying `Spec`. -/
def Satisfies (Spec : List (Label P A) → Prop) : Prop := ∀ E, Spec (Alg.hist Alg.initCfg E)

/-! ### Partial synchrony -/

/-- The timed execution `(ev, time)` (event `t` happens at time `time t`) is partially
synchronous under `f`: time is monotone and unbounded, clock readings are monotone, and there are
`GST` and `Δ` such that after `GST` clocks do not drift, every correct process takes a spontaneous
step at every time unit, and every message in transit on a reliable channel between correct
processes is delivered within `Δ` time units. -/
def PartiallySynchronous (f : FailurePattern P) (ev : ℕ → Event P A) (time : ℕ → ℕ) : Prop :=
  Monotone time ∧ (∀ T, ∃ t, T ≤ time t) ∧
  (∀ p t t' c c', t ≤ t' → ev t = .tick p c → ev t' = .tick p c' → c ≤ c') ∧
  ∃ GST Δ : ℕ,
    (∀ p, ¬ Crashed f ev p → ∃ d, ∀ t c, GST ≤ time t → ev t = .tick p c → c = time t + d) ∧
    (∀ p, ¬ Crashed f ev p → ∀ T ≥ GST, ∃ t, time t = T ∧ ∃ c, ev t = .tick p c) ∧
    (∀ q p, ¬ Crashed f ev q → ¬ Crashed f ev p → (q, p) ∉ f.chans → ∀ i, GST ≤ time i →
      ∃ j, time j ≤ time i + Δ ∧ (Alg.cfgAt ev i).sent q p ≤ (Alg.cfgAt ev j).dlv q p)

/-- `(f, T)`-obstruction-freedom under partial synchrony. -/
def ObstructionFreePS (f : FailurePattern P) (T : Set P) : Prop :=
  ∀ ev time, Alg.Fair f ev → Alg.PartiallySynchronous f ev time → ∀ p ∈ T, ∀ t₀ o,
    ev t₀ = .invoke p o → (Alg.cfgAt ev t₀).pend p = none →
    Alg.EventuallySolo f ev p t₀ → Alg.Returns ev p t₀

/-- `(F, τ)`-obstruction-freedom under partial synchrony. -/
def ObstructionFreePSOn (F : Set (FailurePattern P)) (τ : FailurePattern P → Set P) : Prop :=
  ∀ f ∈ F, Alg.ObstructionFreePS f (τ f)

lemma obstructionFreePS_of_obstructionFree {f : FailurePattern P} {T : Set P}
    (h : Alg.ObstructionFree f T) : Alg.ObstructionFreePS f T :=
  fun ev _ hf _ p hp t₀ o he hpend hs => h ev hf p hp t₀ o he hpend hs

end Algorithm

end Cslib.ChannelFailures
