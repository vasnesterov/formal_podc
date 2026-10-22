import Mathlib

/-!
# Two-party impossibility over a fully-defective channel

Theorem 3 of [CCGS22] (= Theorem 20 of the arXiv full version 2205.11148):
*Fix a non-constant function `f(x, y)`. No two-party deterministic algorithm that gives output
(or terminates) can compute `f` over a fully-defective channel.*

[CCGS22]: K. Censor-Hillel, S. Cohen, R. Gelles, G. Sela,
*Distributed Computations in Fully-Defective Networks*, PODC 2022.

## Model

* Two parties, Alice (input `x : X`) and Bob (input `y : Y`), joined by one bidirectional
  channel; messages are drawn from an arbitrary alphabet `M`.
* **Parties** (`Party`) are deterministic, event-driven state machines: a start-up event
  (`start`, depending on the input) and one event per received message (`recv`). At every event a
  party moves to a new state, sends a finite list of messages and may produce an output.
  Outputs are **irrevocable**: a party's output register (`Config.outA`, `Config.outB`) holds the
  *first* value it ever output. (Termination is a special case: a terminated party is one that
  never sends anything afterwards; the impossibility only needs the output requirement.)
  For the remark on revocable outputs we also keep the *latest* value output (`Config.estA`,
  `Config.estB`).
* **Fully-defective channel**: the adversary may replace the content of every message by any
  element of `M`. It can neither create nor drop messages. Hence a configuration only records how
  many messages were sent and delivered in each direction; a delivery step (`Protocol.Step`)
  takes one in-transit message and hands it to its receiver with an adversarially chosen
  content `m : M`, in an adversarially chosen order (asynchrony).
* **Executions** (`Protocol.IsFairExec`) are sequences `e : ℕ → Config` starting at the initial
  configuration in which every step is a delivery or a stutter (`e (n+1) = e n`), and which are
  **fair**: every message sent is eventually delivered. Stutters encode finite executions (which
  must end with no message in transit) and are harmless otherwise.
* `Protocol.ComputesWithOutput P f`: for all inputs, in every fair execution both parties
  eventually output `f x y`.

## Main results

* `Protocol.bob_fails` / `Protocol.alice_fails`: if `f` depends on Alice's (resp. Bob's) input,
  then for some inputs there is a fair execution in which Bob (resp. Alice) never outputs `f x y`.
* `Protocol.theorem3`: no protocol computes a non-constant `f` and gives output.
* `Protocol.exists_fairExec` (non-vacuity): every protocol has a fair execution on every input;
  `constProtocol_computes`: constant functions are computable with output.
* `estimateProtocol_stabilizes`: the paper's remark — without the output requirement, the protocol
  "send `x` messages, then keep `f(x, #received)` as a revocable estimate" eventually stabilizes
  on `f x y` in every fair execution (`X = Y = ℕ`).

## Proof

As in the paper. The executions used are those in which the adversary overwrites every message
with a fixed `m₀`; then a party's state and output are functions of its input and the number of
messages received so far (`Party.runState`, `Party.runOut`; this is the paper's sequence `B_y`).
A round-robin scheduler (`Protocol.rr`) yields such a fair execution for all inputs.
If `f x y ≠ f x' y`, Bob's first output on `y` is the same value `r̂` in both executions on
`(x, y)` and `(x', y)` whenever he outputs at all (`Party.runOut_unique`), so it is wrong in one
of them. If the alphabet `M` is empty, no message is ever sent and the argument is immediate.
-/

namespace Podc.FullyDefective.TwoParty

/-- A deterministic event-driven party with inputs `I`, message alphabet `M`, outputs `R` and
local states `S`. At the start-up event (`start i`) and upon every reception (`recv s m`) the
party computes its new state, the list of messages it sends, and an optional output. -/
structure Party (I M R S : Type*) where
  /-- Start-up event on input `i`: initial state, messages sent, optional output. -/
  start : I → S × List M × Option R
  /-- Reception of message `m` in state `s`: new state, messages sent, optional output. -/
  recv : S → M → S × List M × Option R

/-- A two-party protocol: Alice gets inputs in `X`, Bob gets inputs in `Y`. -/
structure Protocol (X Y M R SA SB : Type*) where
  /-- Alice's algorithm. -/
  alice : Party X M R SA
  /-- Bob's algorithm. -/
  bob : Party Y M R SB

/-- A global configuration. Since the adversary may overwrite the content of every message,
in-transit messages are only counted: `sentAB - delAB` messages are in transit from Alice to Bob,
`sentBA - delBA` from Bob to Alice. -/
structure Config (SA SB R : Type*) where
  /-- Alice's local state. -/
  stA : SA
  /-- Bob's local state. -/
  stB : SB
  /-- Alice's (irrevocable) output register: the first value Alice output. -/
  outA : Option R
  /-- Bob's (irrevocable) output register: the first value Bob output. -/
  outB : Option R
  /-- The latest value Alice output (a revocable estimate). -/
  estA : Option R
  /-- The latest value Bob output (a revocable estimate). -/
  estB : Option R
  /-- Number of messages sent by Alice to Bob so far. -/
  sentAB : ℕ
  /-- Number of messages delivered to Bob so far. -/
  delAB : ℕ
  /-- Number of messages sent by Bob to Alice so far. -/
  sentBA : ℕ
  /-- Number of messages delivered to Alice so far. -/
  delBA : ℕ

variable {I X Y M R S SA SB : Type*}

/-! ### A party's behaviour when every received message is `m₀` -/

namespace Party

variable (p : Party I M R S)

/-- The state of the party on input `i` after receiving `t` copies of `m₀`. -/
def runState (i : I) (m₀ : M) : ℕ → S
  | 0 => (p.start i).1
  | t + 1 => (p.recv (runState i m₀ t) m₀).1

/-- The output produced at the event triggered by the `t`-th reception (`t = 0`: start-up). -/
def eventOut (i : I) (m₀ : M) : ℕ → Option R
  | 0 => (p.start i).2.2
  | t + 1 => (p.recv (p.runState i m₀ t) m₀).2.2

/-- The output register (first output) of the party on input `i` after receiving `t` copies of
`m₀`. This is the paper's description of Bob by the sequence `B_y`. -/
def runOut (i : I) (m₀ : M) : ℕ → Option R
  | 0 => p.eventOut i m₀ 0
  | t + 1 => (runOut i m₀ t).or (p.eventOut i m₀ (t + 1))

lemma runOut_add {i : I} {m₀ : M} {t : ℕ} {r : R} (h : p.runOut i m₀ t = some r) :
    ∀ k, p.runOut i m₀ (t + k) = some r
  | 0 => h
  | k + 1 => by
    rw [← add_assoc, runOut, runOut_add h k]
    rfl

/-- Whenever the party has output at all, it has output the same value `r̂` (the value output at
the first event `t̂` that outputs): the output register depends only on the number of received
messages, and is irrevocable. -/
lemma runOut_unique {i : I} {m₀ : M} {t t' : ℕ} {r r' : R} (h : p.runOut i m₀ t = some r)
    (h' : p.runOut i m₀ t' = some r') : r = r' := by
  rcases le_total t t' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [p.runOut_add h k] at h'
    exact Option.some_injective _ h'
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [p.runOut_add h' k] at h
    exact (Option.some_injective _ h).symm

end Party

/-! ### Executions -/

namespace Protocol

variable (P : Protocol X Y M R SA SB)

/-- The initial configuration on inputs `(x, y)`: both parties have run their start-up event. -/
def init (x : X) (y : Y) : Config SA SB R :=
  { stA := (P.alice.start x).1, stB := (P.bob.start y).1,
    outA := (P.alice.start x).2.2, outB := (P.bob.start y).2.2,
    estA := (P.alice.start x).2.2, estB := (P.bob.start y).2.2,
    sentAB := (P.alice.start x).2.1.length, delAB := 0,
    sentBA := (P.bob.start y).2.1.length, delBA := 0 }

/-- Deliver one message, with (adversarial) content `m`, to Bob. -/
def deliverToBob (m : M) (c : Config SA SB R) : Config SA SB R :=
  { c with stB := (P.bob.recv c.stB m).1,
           outB := c.outB.or (P.bob.recv c.stB m).2.2,
           estB := (P.bob.recv c.stB m).2.2.or c.estB,
           delAB := c.delAB + 1,
           sentBA := c.sentBA + (P.bob.recv c.stB m).2.1.length }

/-- Deliver one message, with (adversarial) content `m`, to Alice. -/
def deliverToAlice (m : M) (c : Config SA SB R) : Config SA SB R :=
  { c with stA := (P.alice.recv c.stA m).1,
           outA := c.outA.or (P.alice.recv c.stA m).2.2,
           estA := (P.alice.recv c.stA m).2.2.or c.estA,
           delBA := c.delBA + 1,
           sentAB := c.sentAB + (P.alice.recv c.stA m).2.1.length }

/-- An asynchronous step over the fully-defective channel: some in-transit message is delivered
to its receiver, its content replaced by an arbitrary `m : M`. -/
inductive Step : Config SA SB R → Config SA SB R → Prop
  | toBob (c : Config SA SB R) (m : M) : c.delAB < c.sentAB → Step c (P.deliverToBob m c)
  | toAlice (c : Config SA SB R) (m : M) : c.delBA < c.sentBA → Step c (P.deliverToAlice m c)

/-- `e` is a fair (complete) execution of `P` on inputs `(x, y)`: it starts in the initial
configuration, every step is a delivery or a stutter, and every message sent is eventually
delivered (so a finite execution ends with no message in transit). -/
structure IsFairExec (x : X) (y : Y) (e : ℕ → Config SA SB R) : Prop where
  init : e 0 = P.init x y
  step : ∀ n, P.Step (e n) (e (n + 1)) ∨ e (n + 1) = e n
  fairAB : ∀ n, ∃ m, (e n).sentAB ≤ (e m).delAB
  fairBA : ∀ n, ∃ m, (e n).sentBA ≤ (e m).delBA

/-- `P` computes `f` and gives output: on all inputs, in every fair execution, both Alice and Bob
eventually (irrevocably) output `f x y`. -/
def ComputesWithOutput (f : X → Y → R) : Prop :=
  ∀ x y e, P.IsFairExec x y e →
    (∃ n, (e n).outA = some (f x y)) ∧ (∃ n, (e n).outB = some (f x y))

variable {P}

lemma Step.delAB_le {c c' : Config SA SB R} (h : P.Step c c') : c.delAB ≤ c'.delAB := by
  cases h <;> simp [deliverToBob, deliverToAlice]

lemma Step.delBA_le {c c' : Config SA SB R} (h : P.Step c c') : c.delBA ≤ c'.delBA := by
  cases h <;> simp [deliverToBob, deliverToAlice]

lemma IsFairExec.delAB_mono {x : X} {y : Y} {e : ℕ → Config SA SB R} (he : P.IsFairExec x y e) :
    Monotone fun n => (e n).delAB :=
  monotone_nat_of_le_succ fun n => by
    rcases he.step n with h | h
    · exact h.delAB_le
    · simp [h]

lemma IsFairExec.delBA_mono {x : X} {y : Y} {e : ℕ → Config SA SB R} (he : P.IsFairExec x y e) :
    Monotone fun n => (e n).delBA :=
  monotone_nat_of_le_succ fun n => by
    rcases he.step n with h | h
    · exact h.delBA_le
    · simp [h]

variable (P)

/-! ### A round-robin fair execution (adversary overwrites every message with `m₀`) -/

/-- The round-robin execution: at even steps deliver a message to Bob if one is in transit, at odd
steps deliver one to Alice; every delivered message carries content `m₀`. -/
def rr (m₀ : M) (x : X) (y : Y) : ℕ → Config SA SB R
  | 0 => P.init x y
  | n + 1 =>
    let c := rr m₀ x y n
    if n % 2 = 0 then
      if c.delAB < c.sentAB then P.deliverToBob m₀ c else c
    else
      if c.delBA < c.sentBA then P.deliverToAlice m₀ c else c

/-- An abstract fairness lemma for alternating schedulers: if `d` (delivered) increases every two
steps (at steps `≡ c mod 2`) as long as it is below `s` (sent), then `d` eventually catches up with
every value of `s`. -/
lemma exists_le_of_alternating {d s : ℕ → ℕ} (c : ℕ) (hd : Monotone d) (hs : Monotone s)
    (h : ∀ j, d (2 * j + c) < s (2 * j + c) → d (2 * j + c) < d (2 * j + c + 2)) (n : ℕ) :
    ∃ m, s n ≤ d m := by
  have key : ∀ k, min (s n) k ≤ d (2 * (n + k) + c) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hidx : 2 * (n + (k + 1)) + c = 2 * (n + k) + c + 2 := by ring
      rw [hidx]
      by_cases hlt : d (2 * (n + k) + c) < s n
      · have h1 : s n ≤ s (2 * (n + k) + c) := hs (by omega)
        have h2 := h (n + k) (lt_of_lt_of_le hlt h1)
        omega
      · have h3 : d (2 * (n + k) + c) ≤ d (2 * (n + k) + c + 2) := hd (by omega)
        omega
  exact ⟨_, (min_self (s n)).symm.le.trans (key (s n))⟩

lemma rr_step (m₀ : M) (x : X) (y : Y) (n : ℕ) :
    P.Step (P.rr m₀ x y n) (P.rr m₀ x y (n + 1)) ∨ P.rr m₀ x y (n + 1) = P.rr m₀ x y n := by
  rw [rr]
  split_ifs with h1 h2 h3
  · exact Or.inl (Step.toBob _ _ h2)
  · exact Or.inr rfl
  · exact Or.inl (Step.toAlice _ _ h3)
  · exact Or.inr rfl

lemma rr_sentAB_mono (m₀ : M) (x : X) (y : Y) : Monotone fun n => (P.rr m₀ x y n).sentAB :=
  monotone_nat_of_le_succ fun n => by
    simp only [rr]; split_ifs <;> simp [deliverToBob, deliverToAlice]

lemma rr_sentBA_mono (m₀ : M) (x : X) (y : Y) : Monotone fun n => (P.rr m₀ x y n).sentBA :=
  monotone_nat_of_le_succ fun n => by
    simp only [rr]; split_ifs <;> simp [deliverToBob, deliverToAlice]

/-- The round-robin execution is a fair execution. -/
theorem rr_isFairExec (m₀ : M) (x : X) (y : Y) : P.IsFairExec x y (P.rr m₀ x y) := by
  have hstep := P.rr_step m₀ x y
  have hAB : Monotone fun n => (P.rr m₀ x y n).delAB :=
    monotone_nat_of_le_succ fun n => by
      rcases hstep n with h | h
      · exact h.delAB_le
      · simp [h]
  have hBA : Monotone fun n => (P.rr m₀ x y n).delBA :=
    monotone_nat_of_le_succ fun n => by
      rcases hstep n with h | h
      · exact h.delBA_le
      · simp [h]
  refine ⟨rfl, hstep, ?_, ?_⟩
  · refine exists_le_of_alternating 0 hAB (P.rr_sentAB_mono m₀ x y) (fun j hj => ?_)
    have h1 : (P.rr m₀ x y (2 * j + 0 + 1)).delAB = (P.rr m₀ x y (2 * j + 0)).delAB + 1 := by
      rw [rr]; simp only [Nat.add_zero] at hj ⊢
      simp only [show (2 * j) % 2 = 0 by omega, hj, ↓reduceIte, deliverToBob]
    have h2 := hAB (show 2 * j + 0 + 1 ≤ 2 * j + 0 + 2 by omega)
    simp only at h2
    omega
  · refine exists_le_of_alternating 1 hBA (P.rr_sentBA_mono m₀ x y) (fun j hj => ?_)
    have h1 : (P.rr m₀ x y (2 * j + 1 + 1)).delBA = (P.rr m₀ x y (2 * j + 1)).delBA + 1 := by
      rw [rr]; simp only [show ¬ ((2 * j + 1) % 2 = 0) by omega, hj, ↓reduceIte, deliverToAlice]
    have h2 := hBA (show 2 * j + 1 + 1 ≤ 2 * j + 1 + 2 by omega)
    simp only at h2
    omega

/-- In the round-robin execution each party's state and output register are functions of its
input and of the number of messages it has received. -/
lemma rr_local (m₀ : M) (x : X) (y : Y) (n : ℕ) :
    (P.rr m₀ x y n).stA = P.alice.runState x m₀ (P.rr m₀ x y n).delBA ∧
    (P.rr m₀ x y n).outA = P.alice.runOut x m₀ (P.rr m₀ x y n).delBA ∧
    (P.rr m₀ x y n).stB = P.bob.runState y m₀ (P.rr m₀ x y n).delAB ∧
    (P.rr m₀ x y n).outB = P.bob.runOut y m₀ (P.rr m₀ x y n).delAB := by
  induction n with
  | zero => simp [rr, init, Party.runState, Party.runOut, Party.eventOut]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [rr]
    split_ifs <;>
      simp [deliverToBob, deliverToAlice, Party.runState, Party.runOut, Party.eventOut, *]

/-- If the alphabet is empty, no message is ever sent, and the trivial execution is fair. -/
lemma const_isFairExec [IsEmpty M] (x : X) (y : Y) :
    P.IsFairExec x y (fun _ => P.init x y) := by
  have hl : ∀ l : List M, l.length = 0 := fun l => by
    cases l with
    | nil => rfl
    | cons a _ => exact isEmptyElim a
  refine ⟨rfl, fun _ => Or.inr rfl, fun n => ⟨n, ?_⟩, fun n => ⟨n, ?_⟩⟩ <;> simp [init, hl]

/-- Non-vacuity: every protocol has a fair execution on every pair of inputs. -/
theorem exists_fairExec (x : X) (y : Y) : ∃ e, P.IsFairExec x y e := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨m₀⟩⟩
  · exact ⟨_, P.const_isFairExec x y⟩
  · exact ⟨_, P.rr_isFairExec m₀ x y⟩

/-! ### The impossibility -/

/-- Core of the proof of Theorem 3 (Bob's side): if `f` depends on Alice's input, then for some
inputs there is a fair execution in which Bob never outputs `f x y` (he either never outputs or
outputs a wrong value). -/
theorem bob_fails (f : X → Y → R) (hf : ∃ x x' y, f x y ≠ f x' y) :
    ∃ x y e, P.IsFairExec x y e ∧ ∀ n, (e n).outB ≠ some (f x y) := by
  obtain ⟨x, x', y, hne⟩ := hf
  by_contra hcon
  push Not at hcon
  rcases isEmpty_or_nonempty M with hM | ⟨⟨m₀⟩⟩
  · obtain ⟨n, hn⟩ := hcon x y _ (P.const_isFairExec x y)
    obtain ⟨n', hn'⟩ := hcon x' y _ (P.const_isFairExec x' y)
    simp only [init] at hn hn'
    exact hne (Option.some_injective _ (hn.symm.trans hn'))
  · obtain ⟨n, hn⟩ := hcon x y _ (P.rr_isFairExec m₀ x y)
    obtain ⟨n', hn'⟩ := hcon x' y _ (P.rr_isFairExec m₀ x' y)
    rw [(P.rr_local m₀ x y n).2.2.2] at hn
    rw [(P.rr_local m₀ x' y n').2.2.2] at hn'
    exact hne (P.bob.runOut_unique hn hn')

/-- Core of the proof of Theorem 3 (Alice's side, symmetric): if `f` depends on Bob's input, then
for some inputs there is a fair execution in which Alice never outputs `f x y`. -/
theorem alice_fails (f : X → Y → R) (hf : ∃ x y y', f x y ≠ f x y') :
    ∃ x y e, P.IsFairExec x y e ∧ ∀ n, (e n).outA ≠ some (f x y) := by
  obtain ⟨x, y, y', hne⟩ := hf
  by_contra hcon
  push Not at hcon
  rcases isEmpty_or_nonempty M with hM | ⟨⟨m₀⟩⟩
  · obtain ⟨n, hn⟩ := hcon x y _ (P.const_isFairExec x y)
    obtain ⟨n', hn'⟩ := hcon x y' _ (P.const_isFairExec x y')
    simp only [init] at hn hn'
    exact hne (Option.some_injective _ (hn.symm.trans hn'))
  · obtain ⟨n, hn⟩ := hcon x y _ (P.rr_isFairExec m₀ x y)
    obtain ⟨n', hn'⟩ := hcon x y' _ (P.rr_isFairExec m₀ x y')
    rw [(P.rr_local m₀ x y n).2.1] at hn
    rw [(P.rr_local m₀ x y' n').2.1] at hn'
    exact hne (P.alice.runOut_unique hn hn')

/-- Theorem 3, strong form: for a non-constant `f`, for some inputs `(x, y)` there is a fair
execution in which some party never outputs `f x y`. -/
theorem theorem3_strong (f : X → Y → R) (hf : ∃ x y x' y', f x y ≠ f x' y') :
    ∃ x y e, P.IsFairExec x y e ∧
      ((∀ n, (e n).outA ≠ some (f x y)) ∨ (∀ n, (e n).outB ≠ some (f x y))) := by
  by_cases hx : ∃ x x' y, f x y ≠ f x' y
  · obtain ⟨x, y, e, he, h⟩ := P.bob_fails f hx
    exact ⟨x, y, e, he, Or.inr h⟩
  · push Not at hx
    obtain ⟨x, y, x', y', hne⟩ := hf
    obtain ⟨a, b, e, he, h⟩ := P.alice_fails f ⟨x, y, y', by rwa [hx x x' y']⟩
    exact ⟨a, b, e, he, Or.inl h⟩

/-- Theorem 3 of [CCGS22] (= Theorem 20 of the full version). Over a fully-defective channel,
no deterministic two-party protocol computes a non-constant function `f` and gives output. -/
theorem theorem3 (f : X → Y → R) (hf : ∃ x y x' y', f x y ≠ f x' y') :
    ¬ P.ComputesWithOutput f := by
  intro hP
  obtain ⟨x, y, e, he, h | h⟩ := P.theorem3_strong f hf
  · obtain ⟨n, hn⟩ := (hP x y e he).1
    exact h n hn
  · obtain ⟨n, hn⟩ := (hP x y e he).2
    exact h n hn

end Protocol

/-! ### Non-vacuity and the remark on revocable outputs -/

/-- The protocol in which both parties output the constant `r` at start-up and never send. -/
def constProtocol (r : R) : Protocol X Y M R Unit Unit where
  alice := { start := fun _ => ((), [], some r), recv := fun _ _ => ((), [], none) }
  bob := { start := fun _ => ((), [], some r), recv := fun _ _ => ((), [], none) }

/-- The hypothesis "non-constant" in `Protocol.theorem3` is necessary: constant functions are
computed with output. -/
theorem constProtocol_computes (r : R) :
    (constProtocol (X := X) (Y := Y) (M := M) r).ComputesWithOutput (fun _ _ => r) := by
  intro x y e he
  exact ⟨⟨0, by simp [he.init, Protocol.init, constProtocol]⟩,
    ⟨0, by simp [he.init, Protocol.init, constProtocol]⟩⟩

/-- The paper's protocol for revocable outputs (`X = Y = ℕ`, pulses): each party sends as many
pulses as its input, counts received pulses, and after every event sets its (revocable) output to
`f` applied to its input and the current count. The state is (input, count). -/
def estimateProtocol (f : ℕ → ℕ → R) : Protocol ℕ ℕ Unit R (ℕ × ℕ) (ℕ × ℕ) where
  alice :=
    { start := fun x => ((x, 0), List.replicate x (), some (f x 0)),
      recv := fun s _ => ((s.1, s.2 + 1), [], some (f s.1 (s.2 + 1))) }
  bob :=
    { start := fun y => ((y, 0), List.replicate y (), some (f 0 y)),
      recv := fun s _ => ((s.1, s.2 + 1), [], some (f (s.2 + 1) s.1)) }

/-- Remark before Theorem 3: without the requirement of an irrevocable output the problem is
solvable. In every fair execution of `estimateProtocol f` on `(x, y)`, from some time on both
parties' latest outputs equal `f x y` forever. -/
theorem estimateProtocol_stabilizes (f : ℕ → ℕ → R) (x y : ℕ) (e : ℕ → Config (ℕ × ℕ) (ℕ × ℕ) R)
    (he : (estimateProtocol f).IsFairExec x y e) :
    ∃ N, ∀ n ≥ N, (e n).estA = some (f x y) ∧ (e n).estB = some (f x y) := by
  let Inv : Config (ℕ × ℕ) (ℕ × ℕ) R → Prop := fun c =>
    c.sentAB = x ∧ c.sentBA = y ∧ c.delAB ≤ x ∧ c.delBA ≤ y ∧ c.stA = (x, c.delBA) ∧
      c.stB = (y, c.delAB) ∧ c.estA = some (f x c.delBA) ∧ c.estB = some (f c.delAB y)
  have hstep : ∀ c c', (estimateProtocol f).Step c c' → Inv c → Inv c' := by
    rintro c c' h ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    cases h with
    | toBob m hlt =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [Protocol.deliverToBob, estimateProtocol, h1, h2, h4, h5, h6, h7]
      omega
    | toAlice m hlt =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [Protocol.deliverToAlice, estimateProtocol, h1, h2, h3, h5, h6, h8]
      omega
  have inv : ∀ n, Inv (e n) := by
    intro n
    induction n with
    | zero => simp [Inv, he.init, Protocol.init, estimateProtocol]
    | succ n ih =>
      rcases he.step n with h | h
      · exact hstep _ _ h ih
      · rw [h]; exact ih
  obtain ⟨m1, hm1⟩ := he.fairAB 0
  obtain ⟨m2, hm2⟩ := he.fairBA 0
  rw [(inv 0).1] at hm1
  rw [(inv 0).2.1] at hm2
  refine ⟨max m1 m2, fun n hn => ?_⟩
  have hAB : (e m1).delAB ≤ (e n).delAB := he.delAB_mono (le_of_max_le_left hn)
  have hBA : (e m2).delBA ≤ (e n).delBA := he.delBA_mono (le_of_max_le_right hn)
  obtain ⟨-, -, h3, h4, -, -, h7, h8⟩ := inv n
  rw [h7, h8, show (e n).delAB = x by omega, show (e n).delBA = y by omega]
  exact ⟨rfl, rfl⟩

end Podc.FullyDefective.TwoParty
