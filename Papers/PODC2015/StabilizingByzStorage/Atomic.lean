import Papers.PODC2015.StabilizingByzStorage.Server

/-!
# Fig. 3: the practically stabilizing SWSR atomic register

The writer, the reader and `n` servers, `B` the set of Byzantine servers (`#B ≤ t`). Sequence numbers
live in `Fin m` (the paper: `m = 2^64 + 1`) and are compared with the clockwise-distance order `>cd`.

The state of every process and every link is arbitrary at time `0` (transient failures end at
`τ_no_tr = 0`); the step relation `Step` is the interleaving of:
* server steps (deliver the head of one link, lines 19–23); Byzantine servers' states are irrelevant;
* writer steps (`prac_at_write`, lines N1, 01M–06);
* reader steps (`prac_at_read`, lines N2–N7, 07–18).
A client step that waits for `n - t` acknowledgments picks a set `Q` of `n - t` servers; correct
members contribute their recorded reply, Byzantine members arbitrary replies (`acks`/`reps` are
arbitrary on `B`). When several values pass a `2t + 1` threshold (lines N4, 12, 14) the pseudo-code
does not say which one is taken ("let `v` be this value"): any of them may be chosen.
-/

namespace Podc.StabilizingByzStorage.Atomic

open Podc.StabilizingByzStorage

/-- `x >cd y`: the clockwise distance from `y` to `x` is smaller than the anticlockwise one
(Section 4; the paper's `x ≥cd y` and `x ≠ y`). -/
def gtcd {m : ℕ} (x y : Fin m) : Prop := (x - y).val < (y - x).val

instance {m : ℕ} (x y : Fin m) : Decidable (gtcd x y) := by unfold gtcd; infer_instance

/-- Phases of `prac_at_write(v)`. -/
inductive WPhase (V : Type) where
  | idle
  /-- line 01M in progress -/
  | bcastWrite (v : V)
  /-- line 02 -/
  | waitAck (v : V)
  /-- line 04M in progress -/
  | bcastHelp
  deriving DecidableEq, Repr

/-- Phases of `prac_at_read()`. -/
inductive RPhase where
  | idle
  /-- line N2 in progress -/
  | bcastPre
  /-- line N3 -/
  | waitPre
  /-- line 09 in progress -/
  | bcastLoop
  /-- line 11 -/
  | waitLoop
  deriving DecidableEq, Repr

structure Writer (m : ℕ) (V : Type) where
  wsn : Fin m
  phase : WPhase V
  deriving DecidableEq, Repr

structure Reader (m : ℕ) (V : Type) where
  pwsn : Fin m
  pv : V
  phase : RPhase
  deriving DecidableEq, Repr

/-- Global state (configuration). -/
structure State (n m : ℕ) (V : Type) where
  srv : Fin n → Server (Fin m × V)
  w : Writer m V
  r : Reader m V

/-- Externally visible events; `tau` for internal steps. -/
inductive Label (V : Type) where
  | invWrite (v : V)
  | retWrite
  | invRead
  | retRead (v : V)
  | tau
  deriving DecidableEq, Repr

variable {n m : ℕ} [NeZero m] {V : Type} [DecidableEq V]

/-- All servers receive the writer's broadcast of `msg`. -/
def State.bcastW (σ : State n m V) (msg : WMsg (Fin m × V)) : Fin n → Server (Fin m × V) :=
  fun s => (σ.srv s).bcastW msg

/-- All servers receive the reader's broadcast of `READ(b)`. -/
def State.bcastR (σ : State n m V) (b : Bool) : Fin n → Server (Fin m × V) :=
  fun s => (σ.srv s).bcastR b

variable (t : ℕ) (B : Finset (Fin n))

/-- One step of the system of Fig. 3. -/
inductive Step : State n m V → Label V → State n m V → Prop
  /-- A server delivers the oldest message from the writer (lines 19–21). -/
  | delivW (σ : State n m V) (s : Fin n) (h : (σ.srv s).wq ≠ []) :
      Step σ .tau { σ with srv := Function.update σ.srv s (σ.srv s).deliverW }
  /-- A server delivers the oldest message from the reader (lines 22–23). -/
  | delivR (σ : State n m V) (s : Fin n) (h : (σ.srv s).rq ≠ []) :
      Step σ .tau { σ with srv := Function.update σ.srv s (σ.srv s).deliverR }
  /-- Lines N1, 01M: `wsn ← wsn + 1`, `ss_broadcast WRITE(wsn, v)`. -/
  | invWrite (σ : State n m V) (v : V) (h : σ.w.phase = .idle) :
      Step σ (.invWrite v)
        { σ with w := ⟨σ.w.wsn + 1, .bcastWrite v⟩, srv := σ.bcastW (.write (σ.w.wsn + 1, v)) }
  /-- End of the broadcast of line 01M (synchronized delivery). -/
  | endWrite (σ : State n m V) (v : V) (h : σ.w.phase = .bcastWrite v)
      (hs : n - 2 * t ≤ syncW B σ.srv) :
      Step σ .tau { σ with w := ⟨σ.w.wsn, .waitAck v⟩ }
  /-- Lines 02–03, 06: `n - t` acks, `4t + 1` of them carry the same `w ≠ ⊥`: return. -/
  | ackDone (σ : State n m V) (v : V) (h : σ.w.phase = .waitAck v) (Q : Finset (Fin n))
      (acks : Fin n → Option (Fin m × V)) (hQ : Q.card = n - t)
      (hacks : ∀ s ∈ Q, s ∉ B → (σ.srv s).wack = some (acks s))
      (hc : ∃ w, 4 * t + 1 ≤ cnt Q acks (some w)) :
      Step σ .retWrite { σ with w := ⟨σ.w.wsn, .idle⟩ }
  /-- Lines 02–04M: otherwise `ss_broadcast NEW_HELP_VAL(wsn, v)`. -/
  | ackHelp (σ : State n m V) (v : V) (h : σ.w.phase = .waitAck v) (Q : Finset (Fin n))
      (acks : Fin n → Option (Fin m × V)) (hQ : Q.card = n - t)
      (hacks : ∀ s ∈ Q, s ∉ B → (σ.srv s).wack = some (acks s))
      (hc : ¬ ∃ w, 4 * t + 1 ≤ cnt Q acks (some w)) :
      Step σ .tau
        { σ with w := ⟨σ.w.wsn, .bcastHelp⟩, srv := σ.bcastW (.newHelp (σ.w.wsn, v)) }
  /-- End of the broadcast of line 04M; return (line 06). -/
  | endHelp (σ : State n m V) (h : σ.w.phase = .bcastHelp) (hs : n - 2 * t ≤ syncW B σ.srv) :
      Step σ .retWrite { σ with w := ⟨σ.w.wsn, .idle⟩ }
  /-- Line N2: `ss_broadcast READ(false)`. -/
  | invRead (σ : State n m V) (h : σ.r.phase = .idle) :
      Step σ .invRead { σ with r := { σ.r with phase := .bcastPre }, srv := σ.bcastR false }
  /-- End of the broadcast of line N2. -/
  | endPre (σ : State n m V) (h : σ.r.phase = .bcastPre) (hs : n - 2 * t ≤ syncR B σ.srv) :
      Step σ .tau { σ with r := { σ.r with phase := .waitPre } }
  /-- Lines N3–N6 (a helping value `d` has `2t + 1` copies: sanity check), then lines 07–09. -/
  | preAdopt (σ : State n m V) (h : σ.r.phase = .waitPre) (Q : Finset (Fin n))
      (reps : Fin n → (Fin m × V) × Option (Fin m × V)) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (d : Fin m × V) (hd : 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some d)) :
      Step σ .tau
        { σ with
          r := if gtcd σ.r.pwsn d.1 then ⟨d.1, d.2, .bcastLoop⟩ else { σ.r with phase := .bcastLoop }
          srv := σ.bcastR true }
  /-- Lines N3–N4 (no helping value has `2t + 1` copies), then lines 07–09. -/
  | preNone (σ : State n m V) (h : σ.r.phase = .waitPre) (Q : Finset (Fin n))
      (reps : Fin n → (Fin m × V) × Option (Fin m × V)) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (hd : ¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some d)) :
      Step σ .tau { σ with r := { σ.r with phase := .bcastLoop }, srv := σ.bcastR true }
  /-- End of the broadcast of line 09. -/
  | endLoop (σ : State n m V) (h : σ.r.phase = .bcastLoop) (hs : n - 2 * t ≤ syncR B σ.srv) :
      Step σ .tau { σ with r := { σ.r with phase := .waitLoop } }
  /-- Lines 11–13M4: a `last_val` `d` has `2t + 1` copies. -/
  | retLast (σ : State n m V) (h : σ.r.phase = .waitLoop) (Q : Finset (Fin n))
      (reps : Fin n → (Fin m × V) × Option (Fin m × V)) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (d : Fin m × V) (hd : 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) d) :
      Step σ (.retRead (if gtcd d.1 σ.r.pwsn then d.2 else σ.r.pv))
        { σ with r := if gtcd d.1 σ.r.pwsn then ⟨d.1, d.2, .idle⟩ else { σ.r with phase := .idle } }
  /-- Lines 11, 14–15M: no `last_val` has `2t + 1` copies, a helping value `d` has. -/
  | retHelp (σ : State n m V) (h : σ.r.phase = .waitLoop) (Q : Finset (Fin n))
      (reps : Fin n → (Fin m × V) × Option (Fin m × V)) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (hl : ¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) d)
      (d : Fin m × V) (hd : 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some d)) :
      Step σ (.retRead d.2) { σ with r := ⟨d.1, d.2, .idle⟩ }
  /-- Lines 11–18: neither test succeeds: next iteration, `ss_broadcast READ(false)`. -/
  | retry (σ : State n m V) (h : σ.r.phase = .waitLoop) (Q : Finset (Fin n))
      (reps : Fin n → (Fin m × V) × Option (Fin m × V)) (hQ : Q.card = n - t)
      (hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s))
      (hl : ¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) d)
      (hh : ¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some d)) :
      Step σ .tau { σ with r := { σ.r with phase := .bcastLoop }, srv := σ.bcastR false }

end Podc.StabilizingByzStorage.Atomic
