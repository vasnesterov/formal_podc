import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/FailureDetectors/Model.lean

/-!
# Asynchronous message passing with crash failures and failure detectors

The model of Chandra–Hadzilacos–Toueg (J. ACM 1996) in the simplified form of Jayanti–Toueg
(PODC 2008), as used by most "weakest failure detector" papers.

* Processes `P`; a discrete global clock `ℕ` that the processes cannot read.
* A **failure pattern** `F : ℕ → Set P` (`F.crashed t` = processes crashed by time `t`) is
  monotone; `F.Correct p` iff `p` never crashes. An **environment** is a set of failure patterns.
* A **failure detector** with range `R` maps every failure pattern to a set of histories
  `H : P → ℕ → R` (`H p t` = output of `p`'s module at time `t`). Example: `Omega`.
* An **algorithm** is a family of deterministic automata. In a step, process `p` (1) receives one
  message, or nothing (`tick`, the empty message `λ`), or accepts an input from its environment
  (the application, or a black-box object it uses); (2) queries its failure-detector module;
  (3) changes state; (4) broadcasts at most one message to every process (itself included) and
  produces outputs (`Algorithm.step`).
* A **run** (`Run`) is a failure pattern, a failure-detector history and a schedule
  `σ : ℕ → Option (P × Choice P I)`: at time `t` either nobody moves or process `p` takes the step
  `σ t`. The message received in a step is designated by its sender and its *sending time*
  (`Choice.recv q s`), so links are reliable but **not FIFO**: any message in transit may be
  received.
* `Admissible`: steps are taken only by non-crashed processes, receptions are of messages
  actually sent earlier and happen at most once, every correct process takes infinitely many
  `tick` steps (local time-outs fire infinitely often), and every message sent to a correct
  process is eventually received. Inputs are unconstrained here: problem-specific assumptions on
  inputs (and on the behaviour of black boxes) are hypotheses of the theorems that need them.

`cfg A r t` is the configuration (local states + messages sent so far, indexed by sending time)
before the step at time `t`; `Out A r p o t` says that the step at time `t` is a step of `p`
producing output `o`.
-/

namespace Cslib.FailureDetectors

/-! ### Failure patterns, failure detectors, `Ω` -/

/-- A failure pattern: `crashed t` is the set of processes crashed by time `t`; crashed processes
never recover. -/
structure FailurePattern (P : Type*) where
  /-- The processes crashed by time `t`. -/
  crashed : ℕ → Set P
  /-- No recovery. -/
  mono : Monotone crashed

namespace FailurePattern

variable {P : Type*} (F : FailurePattern P)

/-- `p` never crashes. -/
def Correct (p : P) : Prop := ∀ t, p ∉ F.crashed t

/-- The failure-free pattern. -/
def noCrash : FailurePattern P := ⟨fun _ => ∅, fun _ _ _ => le_rfl⟩

lemma noCrash_correct (p : P) : (noCrash : FailurePattern P).Correct p := fun _ h => h

lemma not_crashed_of_le {p : P} {t t' : ℕ} (h : t ≤ t') (hp : p ∉ F.crashed t') :
    p ∉ F.crashed t := fun h' => hp (F.mono h h')

/-- A faulty process crashes at some time. -/
lemma exists_crashed_of_not_correct {p : P} (h : ¬ F.Correct p) : ∃ t, p ∈ F.crashed t := by
  simpa [Correct] using h

/-- With finitely many processes, there is a time by which all faulty processes have crashed. -/
lemma exists_crash_bound [Finite P] : ∃ T, ∀ p, ¬ F.Correct p → p ∈ F.crashed T := by
  classical
  haveI := Fintype.ofFinite P
  let c : P → ℕ := fun p => if h : F.Correct p then 0 else (F.exists_crashed_of_not_correct h).choose
  refine ⟨Finset.univ.sup c, fun p hp => F.mono (Finset.le_sup (Finset.mem_univ p)) ?_⟩
  simp only [c, dif_neg hp]
  exact (F.exists_crashed_of_not_correct hp).choose_spec

end FailurePattern

/-- A failure detector with range `R`: the set of histories it may output in each failure
pattern. -/
def FailureDetector (P R : Type*) := FailurePattern P → Set (P → ℕ → R)

/-- The eventual leader failure detector `Ω`: if some process is correct, then there is a time
after which every correct process permanently outputs the same correct process. -/
def Omega (P : Type*) : FailureDetector P P := fun F =>
  {H | (∃ c, F.Correct c) → ∃ ℓ, F.Correct ℓ ∧ ∃ T, ∀ t ≥ T, ∀ p, F.Correct p → H p t = ℓ}

/-- `Ω` outputs nonempty sets of histories: a constant correct leader. -/
lemma const_mem_Omega {P : Type*} (F : FailurePattern P) (ℓ : P) (hℓ : F.Correct ℓ) :
    (fun _ _ => ℓ) ∈ Omega P F :=
  fun _ => ⟨ℓ, hℓ, 0, fun _ _ _ _ => rfl⟩

/-! ### Algorithms and runs -/

/-- What a step of a process consumes: a message `m` from `q`, nothing (`λ`, a local time-out), or
an input `i` from the environment of the process. -/
inductive Event (P M I : Type*) where
  /-- Reception of `m` sent by `q`. -/
  | recv (q : P) (m : M)
  /-- Empty message / local time-out. -/
  | tick
  /-- An input. -/
  | input (i : I)

/-- A deterministic algorithm with failure-detector range `R`, messages `M`, inputs `I`, outputs
`O` and local states `S`. `step p d s e = (s', b, os)`: new state `s'`, broadcast `b` (sent to
every process, itself included) and outputs `os`. -/
structure Algorithm (P R M I O S : Type*) where
  /-- Initial local states. -/
  init : P → S
  /-- One step of `p` with failure-detector value `d`, state `s`, consuming `e`. -/
  step : P → R → S → Event P M I → S × Option M × List O

/-- Scheduler choice for a step: receive the message broadcast by `q` at time `s`, a time-out, or
an input. -/
inductive Choice (P I : Type*) where
  /-- Receive the message broadcast by `q` at time `s`. -/
  | recv (q : P) (s : ℕ)
  /-- Time-out (empty message). -/
  | tick
  /-- Input. -/
  | input (i : I)

/-- A run: failure pattern, failure-detector history and schedule. -/
structure Run (P R I : Type*) where
  /-- The failure pattern. -/
  F : FailurePattern P
  /-- The failure-detector history. -/
  H : P → ℕ → R
  /-- The schedule: the step taken at time `t` (if any). -/
  σ : ℕ → Option (P × Choice P I)

/-- Global configuration: local states and the message broadcast at each past time (with its
sender). -/
structure Config (P M S : Type*) where
  /-- Local states. -/
  loc : P → S
  /-- `msg s = some (q, m)`: `q` broadcast `m` at time `s`. -/
  msg : ℕ → Option (P × M)

namespace Config

variable {P M S I : Type*} [DecidableEq P]

/-- Resolve a scheduler choice into an event (`none` if it designates no message from `q`). -/
def event (C : Config P M S) : Choice P I → Option (Event P M I)
  | .recv q s => match C.msg s with
    | some (q', m) => if q' = q then some (.recv q m) else none
    | none => none
  | .tick => some .tick
  | .input i => some (.input i)

end Config

namespace Algorithm

variable {P R M I O S : Type*} [DecidableEq P] (A : Algorithm P R M I O S)

/-- The initial configuration. -/
def initCfg : Config P M S := ⟨A.init, fun _ => none⟩

/-- The step at time `t` from configuration `C` with history `H`: new configuration and outputs. -/
def next (H : P → ℕ → R) (t : ℕ) (C : Config P M S) :
    Option (P × Choice P I) → Config P M S × List O
  | none => (C, [])
  | some (p, c) =>
    match C.event c with
    | none => (C, [])
    | some e =>
      let r := A.step p (H p t) (C.loc p) e
      (⟨Function.update C.loc p r.1, Function.update C.msg t (r.2.1.map fun m => (p, m))⟩,
        r.2.2)

/-- The configuration before the step at time `t`. -/
def cfg (r : Run P R I) : ℕ → Config P M S
  | 0 => A.initCfg
  | t + 1 => (A.next r.H t (cfg r t) (r.σ t)).1

/-- The outputs of the step at time `t`. -/
def outAt (r : Run P R I) (t : ℕ) : List O := (A.next r.H t (A.cfg r t) (r.σ t)).2

/-- The step at time `t` is a step of `p` producing output `o`. -/
def Out (r : Run P R I) (p : P) (o : O) (t : ℕ) : Prop :=
  (∃ c, r.σ t = some (p, c)) ∧ o ∈ A.outAt r t

/-- The local state of `p` before time `t`. -/
abbrev st (r : Run P R I) (p : P) (t : ℕ) : S := (A.cfg r t).loc p

/-- Admissible runs (for the given failure pattern and history; membership of `r.F` in the
environment and of `r.H` in the failure detector are separate hypotheses). -/
structure Admissible (r : Run P R I) : Prop where
  /-- Crashed processes take no steps. -/
  alive : ∀ t p c, r.σ t = some (p, c) → p ∉ r.F.crashed t
  /-- Only messages broadcast earlier by the designated sender are received. -/
  recv_valid : ∀ t p q s, r.σ t = some (p, .recv q s) → s < t ∧ ∃ m, (A.cfg r t).msg s = some (q, m)
  /-- A message is received at most once by each process. -/
  recv_once : ∀ t t' p q s, r.σ t = some (p, .recv q s) → r.σ t' = some (p, .recv q s) → t = t'
  /-- Correct processes take infinitely many time-out steps. -/
  ticks : ∀ p, r.F.Correct p → ∀ T, ∃ t ≥ T, r.σ t = some (p, .tick)
  /-- Every message is eventually received by every correct process. -/
  delivery : ∀ p, r.F.Correct p → ∀ t s q m, (A.cfg r t).msg s = some (q, m) →
    ∃ t', r.σ t' = some (p, .recv q s)

/-! ### Basic lemmas -/

variable {A} (r : Run P R I)

@[simp] lemma cfg_zero : A.cfg r 0 = A.initCfg := rfl

lemma cfg_succ (t : ℕ) : A.cfg r (t + 1) = (A.next r.H t (A.cfg r t) (r.σ t)).1 := rfl

/-- Messages are recorded at their sending time and never change. -/
lemma msg_succ (t s : ℕ) (hs : s ≠ t) : (A.cfg r (t + 1)).msg s = (A.cfg r t).msg s := by
  rw [cfg_succ]
  rcases h : r.σ t with _ | ⟨p, c⟩
  · rfl
  · simp only [next]
    rcases (A.cfg r t).event c with _ | e
    · rfl
    · simp [Function.update_of_ne hs]

lemma msg_eq_none_of_le (t s : ℕ) (h : t ≤ s) : (A.cfg r t).msg s = none := by
  induction t with
  | zero => rfl
  | succ t ih => rw [msg_succ r t s (by omega)]; exact ih (by omega)

lemma msg_mono {t t' s : ℕ} (h : s < t) (h' : t ≤ t') : (A.cfg r t').msg s = (A.cfg r t).msg s := by
  induction t', h' using Nat.le_induction with
  | base => rfl
  | succ t' ht ih => rw [msg_succ r t' s (by omega), ih]

/-- The message stored for time `s` is the one stored right after the step at `s`. -/
lemma msg_eq_succ {t s : ℕ} (h : s < t) : (A.cfg r t).msg s = (A.cfg r (s + 1)).msg s :=
  msg_mono r (Nat.lt_succ_self s) h

/-- Local states change only by steps of their owner. -/
lemma loc_succ_of_ne (t : ℕ) (q : P) (h : ∀ c, r.σ t ≠ some (q, c)) :
    A.st r q (t + 1) = A.st r q t := by
  simp only [st, cfg_succ]
  rcases hσ : r.σ t with _ | ⟨p, c⟩
  · rfl
  · simp only [next]
    rcases (A.cfg r t).event c with _ | e
    · rfl
    · have : q ≠ p := by rintro rfl; exact h c hσ
      simp [Function.update_of_ne this]

/-- The effect of a step of `p` consuming the (resolved) event `e`. -/
lemma cfg_succ_of_event (t : ℕ) (p : P) (c : Choice P I) (e : Event P M I)
    (hσ : r.σ t = some (p, c)) (he : (A.cfg r t).event c = some e) :
    A.st r p (t + 1) = (A.step p (r.H p t) (A.st r p t) e).1 ∧
    (A.cfg r (t + 1)).msg t = (A.step p (r.H p t) (A.st r p t) e).2.1.map (fun m => (p, m)) ∧
    A.outAt r t = (A.step p (r.H p t) (A.st r p t) e).2.2 := by
  simp [st, cfg_succ, outAt, hσ, next, he]

/-- A step whose choice does not resolve changes nothing. -/
lemma cfg_succ_of_event_none (t : ℕ) (p : P) (c : Choice P I)
    (hσ : r.σ t = some (p, c)) (he : (A.cfg r t).event c = none) :
    A.cfg r (t + 1) = A.cfg r t ∧ A.outAt r t = [] := by
  simp [cfg_succ, outAt, hσ, next, he]

lemma outAt_of_none (t : ℕ) (hσ : r.σ t = none) : A.outAt r t = [] := by
  simp [outAt, hσ, next]

lemma event_tick (C : Config P M S) : C.event (.tick : Choice P I) = some .tick := rfl

lemma event_input (C : Config P M S) (i : I) : C.event (.input i : Choice P I) = some (.input i) :=
  rfl

lemma event_recv {C : Config P M S} {q : P} {s : ℕ} {m : M} (h : C.msg s = some (q, m)) :
    C.event (.recv q s : Choice P I) = some (.recv q m) := by
  simp [Config.event, h]

/-- A resolved reception designates a stored message. -/
lemma event_eq_recv {C : Config P M S} {c : Choice P I} {q : P} {m : M}
    (h : C.event c = some (.recv q m)) : ∃ s, c = .recv q s ∧ C.msg s = some (q, m) := by
  cases c with
  | recv q' s =>
    simp only [Config.event] at h
    rcases hs : C.msg s with _ | ⟨q'', m'⟩
    · simp [hs] at h
    · simp only [hs] at h
      split_ifs at h with hq
      · simp only [Option.some.injEq, Event.recv.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hq
        exact ⟨s, rfl, hs⟩
  | tick => simp [Config.event] at h
  | input i => simp [Config.event] at h

/-- A resolved reception choice is a reception of the stored message. -/
lemma event_of_recv {C : Config P M S} {q : P} {s : ℕ} {e : Event P M I}
    (h : C.event (.recv q s : Choice P I) = some e) :
    ∃ m, e = .recv q m ∧ C.msg s = some (q, m) := by
  simp only [Config.event] at h
  rcases hs : C.msg s with _ | ⟨q', m⟩
  · simp [hs] at h
  · simp only [hs] at h
    split_ifs at h with hq
    · subst hq; simp only [Option.some.injEq] at h; exact ⟨m, h.symm, rfl⟩

lemma event_eq_tick {C : Config P M S} {c : Choice P I} (h : C.event c = some .tick) :
    c = .tick := by
  cases c with
  | recv q' s =>
    simp only [Config.event] at h
    rcases hs : C.msg s with _ | ⟨q'', m'⟩
    · simp [hs] at h
    · simp only [hs] at h; split_ifs at h; simp at h
  | tick => rfl
  | input i => simp [Config.event] at h

/-- Outputs come from resolved steps. -/
lemma out_iff {p : P} {o : O} {t : ℕ} :
    A.Out r p o t ↔ ∃ c e, r.σ t = some (p, c) ∧ (A.cfg r t).event c = some e ∧
      o ∈ (A.step p (r.H p t) (A.st r p t) e).2.2 := by
  constructor
  · rintro ⟨⟨c, hσ⟩, ho⟩
    rcases he : (A.cfg r t).event c with _ | e
    · rw [(cfg_succ_of_event_none r t p c hσ he).2] at ho; simp at ho
    · rw [(cfg_succ_of_event r t p c e hσ he).2.2] at ho
      exact ⟨c, e, hσ, he, ho⟩
  · rintro ⟨c, e, hσ, he, ho⟩
    exact ⟨⟨c, hσ⟩, by rw [(cfg_succ_of_event r t p c e hσ he).2.2]; exact ho⟩

/-- What a stored message is: the broadcast of a step of its sender at its sending time. -/
lemma msg_spec {t s : ℕ} {q : P} {m : M} (h : (A.cfg r t).msg s = some (q, m)) :
    ∃ c e, r.σ s = some (q, c) ∧ (A.cfg r s).event c = some e ∧
      (A.step q (r.H q s) (A.st r q s) e).2.1 = some m := by
  have hst : s < t := by
    by_contra hc
    rw [msg_eq_none_of_le r t s (by omega)] at h
    exact absurd h (by simp)
  rw [msg_eq_succ r hst, cfg_succ] at h
  rcases hσ : r.σ s with _ | ⟨p, c⟩
  · rw [hσ] at h; simp [next, msg_eq_none_of_le r s s le_rfl] at h
  · rw [hσ] at h
    rcases he : (A.cfg r s).event c with _ | e
    · simp [next, he, msg_eq_none_of_le r s s le_rfl] at h
    · simp only [next, he, Function.update_self] at h
      rcases hb : (A.step p (r.H p s) ((A.cfg r s).loc p) e).2.1 with _ | b
      · simp [hb] at h
      · simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨c, e, rfl, he, hb⟩

/-- In an admissible run, a scheduled reception resolves to the stored message. -/
lemma Admissible.recv_event {r : Run P R I} (hA : A.Admissible r) {t : ℕ} {p q : P} {s : ℕ}
    (hσ : r.σ t = some (p, .recv q s)) :
    ∃ m, (A.cfg r t).msg s = some (q, m) ∧ (A.cfg r t).event (.recv q s : Choice P I) = some (.recv q m) := by
  obtain ⟨-, m, hm⟩ := hA.recv_valid t p q s hσ
  exact ⟨m, hm, event_recv hm⟩

/-- In an admissible run every scheduled step resolves to an event. -/
lemma Admissible.event_isSome {r : Run P R I} (hA : A.Admissible r) {t : ℕ} {p : P}
    {c : Choice P I} (hσ : r.σ t = some (p, c)) : ∃ e, (A.cfg r t).event c = some e := by
  cases c with
  | recv q s => obtain ⟨m, -, he⟩ := hA.recv_event hσ; exact ⟨_, he⟩
  | tick => exact ⟨_, event_tick _⟩
  | input i => exact ⟨_, event_input _ i⟩

/-- A step of a process at time `t` shows that it has not crashed by any earlier time. -/
lemma Admissible.not_crashed_of_step {r : Run P R I} (hA : A.Admissible r) {t t' : ℕ} {p : P}
    {c : Choice P I} (hσ : r.σ t = some (p, c)) (h : t' ≤ t) : p ∉ r.F.crashed t' :=
  r.F.not_crashed_of_le h (hA.alive t p c hσ)

/-- **Invariant principle.** A property of local states preserved by every step of its owner and
holding initially holds forever. -/
lemma st_induction (Q : P → S → Prop) (h0 : ∀ p, Q p (A.init p))
    (hstep : ∀ t p c e, r.σ t = some (p, c) → (A.cfg r t).event c = some e →
      Q p (A.st r p t) → Q p (A.step p (r.H p t) (A.st r p t) e).1) :
    ∀ t p, Q p (A.st r p t) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro q
    rcases hσ : r.σ t with _ | ⟨p, c⟩
    · rw [loc_succ_of_ne r t q (by simp [hσ])]; exact ih q
    · by_cases hq : q = p
      · subst hq
        rcases he : (A.cfg r t).event c with _ | e
        · rw [st, (cfg_succ_of_event_none r t q c hσ he).1]; exact ih q
        · rw [(cfg_succ_of_event r t q c e hσ he).1]; exact hstep t q c e hσ he (ih q)
      · rw [loc_succ_of_ne r t q (by intro c' h; rw [hσ] at h; simp at h; exact hq h.1.symm)]
        exact ih q

/-- **Time-indexed invariant principle.** -/
lemma st_induction_time (Q : ℕ → P → S → Prop) (h0 : ∀ p, Q 0 p (A.init p))
    (hmono : ∀ t p s, Q t p s → Q (t + 1) p s)
    (hstep : ∀ t p c e, r.σ t = some (p, c) → (A.cfg r t).event c = some e →
      Q t p (A.st r p t) → Q (t + 1) p (A.step p (r.H p t) (A.st r p t) e).1) :
    ∀ t p, Q t p (A.st r p t) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro q
    rcases hσ : r.σ t with _ | ⟨p, c⟩
    · rw [loc_succ_of_ne r t q (by simp [hσ])]; exact hmono _ _ _ (ih q)
    · by_cases hq : q = p
      · subst hq
        rcases he : (A.cfg r t).event c with _ | e
        · rw [st, (cfg_succ_of_event_none r t q c hσ he).1]; exact hmono _ _ _ (ih q)
        · rw [(cfg_succ_of_event r t q c e hσ he).1]; exact hstep t q c e hσ he (ih q)
      · rw [loc_succ_of_ne r t q (by intro c' h; rw [hσ] at h; simp at h; exact hq h.1.symm)]
        exact hmono _ _ _ (ih q)

/-- A relation between consecutive local states that holds along every step (and trivially
when the state does not change) holds between the states at any two times. -/
lemma st_rel_of_step (Rel : P → S → S → Prop) (hrefl : ∀ p s, Rel p s s)
    (htrans : ∀ p a b c, Rel p a b → Rel p b c → Rel p a c)
    (hstep : ∀ t p c e, r.σ t = some (p, c) → (A.cfg r t).event c = some e →
      Rel p (A.st r p t) (A.step p (r.H p t) (A.st r p t) e).1) :
    ∀ p t t', t ≤ t' → Rel p (A.st r p t) (A.st r p t') := by
  intro q t t' h
  induction t', h using Nat.le_induction with
  | base => exact hrefl _ _
  | succ t' _ ih =>
    refine htrans _ _ _ _ ih ?_
    rcases hσ : r.σ t' with _ | ⟨p, c⟩
    · rw [loc_succ_of_ne r t' q (by simp [hσ])]; exact hrefl _ _
    · by_cases hq : q = p
      · subst hq
        rcases he : (A.cfg r t').event c with _ | e
        · rw [st, st, (cfg_succ_of_event_none r t' q c hσ he).1]; exact hrefl _ _
        · rw [(cfg_succ_of_event r t' q c e hσ he).1]; exact hstep t' q c e hσ he
      · rw [loc_succ_of_ne r t' q (by intro c' h; rw [hσ] at h; simp at h; exact hq h.1.symm)]
        exact hrefl _ _

end Algorithm

end Cslib.FailureDetectors
