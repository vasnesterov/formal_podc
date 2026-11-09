import Papers.PODC2015.StabilizingByzStorage.Server

/-!
# Fig. 2: the stabilizing SWSR regular register

Same system as `Atomic.lean` (servers and `ss-broadcast` from `Server.lean`), with the client code of
Fig. 2: no sequence numbers, payload `D = V`.

The state also carries **ghost** variables, which no guard of the algorithm reads; they only record
the history needed to state and prove regularity:
* `vals`: the values of the writes invoked so far (in order), `nDone`: how many of them completed;
* `base`: the value of `nDone` when the current read was invoked (writes `0, …, base - 1` completed
  before it, `base - 1` is the last one);
* per server (`Ghost`): for every pending writer message, the index of the write that broadcast it
  (`none` for the initial contents of the link); for every pending reader message, whether it is the
  `READ(true)` (`some true`) or a `READ(false)` (`some false`) of the current read (`none`: older or
  initial message); the indices of the writes that last set `last_val` and `helping_val`; whether
  the server has delivered the `READ(true)` of the current read (`rtd`).

`Init σ`: arbitrary server states and links (transient failures end at time `0`), both clients
between operations, empty ghost history.
-/

namespace Podc.StabilizingByzStorage.Regular

open Podc.StabilizingByzStorage

/-- Phases of `write(v)` (Fig. 2). -/
inductive WPhase (V : Type) where
  | idle
  /-- line 01 in progress -/
  | bcastWrite (v : V)
  /-- line 02 -/
  | waitAck (v : V)
  /-- line 04 in progress -/
  | bcastHelp
  deriving DecidableEq, Repr

/-- Phases of `read()` (Fig. 2). -/
inductive RPhase where
  | idle
  /-- line 09 in progress -/
  | bcastLoop
  /-- line 11 -/
  | waitLoop
  deriving DecidableEq, Repr

/-- Ghost information about a server (never read by the algorithm). -/
structure Ghost where
  /-- Index of the write that broadcast each pending writer message (`none`: initial garbage). -/
  wtags : List (Option ℕ)
  /-- For each pending reader message: `some true` = `READ(true)` of the current read,
  `some false` = a later `READ(false)` of the current read, `none` = any other message. -/
  rtags : List (Option Bool)
  /-- Index of the write whose `WRITE` set `last_val` (`none`: initial value or garbage). -/
  lastTag : Option ℕ
  /-- Index of the write whose `NEW_HELP_VAL` set `helping_val` (`none` otherwise). -/
  helpTag : Option ℕ
  /-- The server has delivered the `READ(true)` of the current read. -/
  rtd : Bool
  deriving DecidableEq, Repr

/-- Global state. -/
structure State (n : ℕ) (V : Type) where
  srv : Fin n → Server V
  w : WPhase V
  r : RPhase
  /-- ghost -/
  g : Fin n → Ghost
  /-- ghost: values of the writes invoked so far -/
  vals : List V
  /-- ghost: number of completed writes -/
  nDone : ℕ
  /-- ghost: `nDone` at the invocation of the current read -/
  base : ℕ

inductive Label (V : Type) where
  | invWrite (v : V)
  | retWrite
  | invRead
  | retRead (v : V)
  | tau
  deriving DecidableEq, Repr

variable {n : ℕ} {V : Type} [DecidableEq V]

namespace Ghost

/-- Ghost update when the server delivers its oldest writer message `m`. -/
def deliverW (g : Ghost) (isWrite : Bool) : Ghost :=
  match g.wtags with
  | [] => g
  | tg :: rest =>
    if isWrite then { g with wtags := rest, lastTag := tg } else { g with wtags := rest, helpTag := tg }

/-- Ghost update when the server delivers its oldest reader message `READ(b)`. -/
def deliverR (g : Ghost) (b : Bool) : Ghost :=
  match g.rtags with
  | [] => g
  | tg :: rest =>
    { g with rtags := rest, helpTag := if b then none else g.helpTag,
             rtd := if tg = some true then true else g.rtd }

end Ghost

/-- Is the oldest pending writer message a `WRITE`? -/
def headIsWrite (s : Server V) : Bool :=
  match s.wq with
  | .write _ :: _ => true
  | _ => false

/-- The value of the oldest pending reader message. -/
def headR (s : Server V) : Bool := s.rq.headD false

/-- Initial states: arbitrary servers and links, clients between operations, empty ghost history. -/
def Init (σ : State n V) : Prop :=
  σ.w = .idle ∧ σ.r = .idle ∧ σ.vals = [] ∧ σ.nDone = 0 ∧
  ∀ s, (σ.g s).wtags = (σ.srv s).wq.map (fun _ => none) ∧
    (σ.g s).rtags = (σ.srv s).rq.map (fun _ => none) ∧
    (σ.g s).lastTag = none ∧ (σ.g s).helpTag = none

variable (t : ℕ) (B : Finset (Fin n))

/-- One step of the system of Fig. 2. -/
inductive Step : State n V → Label V → State n V → Prop
  /-- A server delivers the oldest message from the writer (lines 19–21). -/
  | delivW (σ : State n V) (s : Fin n) (h : (σ.srv s).wq ≠ []) :
      Step σ .tau { σ with
        srv := Function.update σ.srv s (σ.srv s).deliverW
        g := Function.update σ.g s ((σ.g s).deliverW (headIsWrite (σ.srv s))) }
  /-- A server delivers the oldest message from the reader (lines 22–23). -/
  | delivR (σ : State n V) (s : Fin n) (h : (σ.srv s).rq ≠ []) :
      Step σ .tau { σ with
        srv := Function.update σ.srv s (σ.srv s).deliverR
        g := Function.update σ.g s ((σ.g s).deliverR (headR (σ.srv s))) }
  /-- Line 01: `ss_broadcast WRITE(v)`. -/
  | invWrite (σ : State n V) (v : V) (h : σ.w = .idle) :
      Step σ (.invWrite v) { σ with
        w := .bcastWrite v
        srv := fun s => (σ.srv s).bcastW (.write v)
        g := fun s => { σ.g s with wtags := (σ.g s).wtags ++ [some σ.vals.length] }
        vals := σ.vals ++ [v] }
  /-- End of the broadcast of line 01. -/
  | endWrite (σ : State n V) (v : V) (h : σ.w = .bcastWrite v)
      (hs : n - 2 * t ≤ syncW B σ.srv) :
      Step σ .tau { σ with w := .waitAck v }
  /-- Lines 02–03, 06: `4t + 1` of the `n - t` acks carry the same `w ≠ ⊥`: return. -/
  | ackDone (σ : State n V) (v : V) (h : σ.w = .waitAck v) (Q : Finset (Fin n))
      (acks : Fin n → Option V) (hQ : Q.card = n - t)
      (hacks : ∀ s ∈ Q, s ∉ B → (σ.srv s).wack = some (acks s))
      (hc : ∃ w, 4 * t + 1 ≤ cnt Q acks (some w)) :
      Step σ .retWrite { σ with w := .idle, nDone := σ.nDone + 1 }
  /-- Lines 02–04: otherwise `ss_broadcast NEW_HELP_VAL(v)`. -/
  | ackHelp (σ : State n V) (v : V) (h : σ.w = .waitAck v) (Q : Finset (Fin n))
      (acks : Fin n → Option V) (hQ : Q.card = n - t)
      (hacks : ∀ s ∈ Q, s ∉ B → (σ.srv s).wack = some (acks s))
      (hc : ¬ ∃ w, 4 * t + 1 ≤ cnt Q acks (some w)) :
      Step σ .tau { σ with
        w := .bcastHelp
        srv := fun s => (σ.srv s).bcastW (.newHelp v)
        g := fun s => { σ.g s with wtags := (σ.g s).wtags ++ [some (σ.vals.length - 1)] } }
  /-- End of the broadcast of line 04; return (line 06). -/
  | endHelp (σ : State n V) (h : σ.w = .bcastHelp) (hs : n - 2 * t ≤ syncW B σ.srv) :
      Step σ .retWrite { σ with w := .idle, nDone := σ.nDone + 1 }
  /-- Lines 07–09: `ss_broadcast READ(true)`. -/
  | invRead (σ : State n V) (h : σ.r = .idle) :
      Step σ .invRead { σ with
        r := .bcastLoop
        srv := fun s => (σ.srv s).bcastR true
        g := fun s => { σ.g s with
          rtags := (σ.g s).rtags.map (fun _ => none) ++ [some true], rtd := false }
        base := σ.nDone }
  /-- End of the broadcast of line 09. -/
  | endLoop (σ : State n V) (h : σ.r = .bcastLoop) (hs : n - 2 * t ≤ syncR B σ.srv) :
      Step σ .tau { σ with r := .waitLoop }
  /-- Lines 11–13: a `last_val` `v` has `2t + 1` copies: return it. -/
  | retLast (σ : State n V) (h : σ.r = .waitLoop) (Q : Finset (Fin n))
      (reps : Fin n → V × Option V) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (v : V) (hd : 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) v) :
      Step σ (.retRead v) { σ with r := .idle }
  /-- Lines 11, 14–15: no `last_val` has `2t + 1` copies, a helping value `w ≠ ⊥` has. -/
  | retHelp (σ : State n V) (h : σ.r = .waitLoop) (Q : Finset (Fin n))
      (reps : Fin n → V × Option V) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (hl : ¬ ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) v)
      (v : V) (hd : 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some v)) :
      Step σ (.retRead v) { σ with r := .idle }
  /-- Lines 11–18: neither test succeeds: `ss_broadcast READ(false)`. -/
  | retry (σ : State n V) (h : σ.r = .waitLoop) (Q : Finset (Fin n))
      (reps : Fin n → V × Option V) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (hl : ¬ ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) v)
      (hh : ¬ ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some v)) :
      Step σ .tau { σ with
        r := .bcastLoop
        srv := fun s => (σ.srv s).bcastR false
        g := fun s => { σ.g s with rtags := (σ.g s).rtags ++ [some false] } }

/-- A step of an execution: a step of the system, or a stutter. -/
def Next (σ : State n V) (ℓ : Label V) (σ' : State n V) : Prop :=
  Step t B σ ℓ σ' ∨ (σ' = σ ∧ ℓ = .tau)

/-- States reachable from `σ₀`. -/
inductive Reach (σ₀ : State n V) : State n V → Prop
  | refl : Reach σ₀ σ₀
  | step {σ σ' : State n V} {ℓ : Label V} : Reach σ₀ σ → Step t B σ ℓ σ' → Reach σ₀ σ'

end Podc.StabilizingByzStorage.Regular
