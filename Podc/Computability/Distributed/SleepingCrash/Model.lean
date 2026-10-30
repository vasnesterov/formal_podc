import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/SleepingCrash/Model.lean

/-!
# The synchronous sleeping model with crash failures

The *sleeping model* (Chatterjee, Gmyr, Pandurangan, PODC 2020) on a complete network of
processes `P`, extended with crash failures:

* computation proceeds in synchronous rounds `1, 2, …`; `config alg adv r p` is the local state of
  `p` at the end of round `r` (`config … 0` is the initial state);
* in every round each process is either **awake** or **asleep**; the choice
  `Algorithm.awake p r s` is a function of the round number and of the state `s` at the start of
  the round, so it is fixed at the end of the last awake round (the algorithm "sets an alarm");
* an awake process sends `Algorithm.send p r s q` to each `q` and then updates its state with
  `Algorithm.recv` from the messages it receives; a message sent to a process that is asleep in
  that round is lost; an asleep process sends nothing and its state does not change;
* the adversary (`Adversary`) fixes the inputs and a crash pattern: `crash p = some c` means that
  `p` crashes in round `c ≥ 1`. It behaves correctly in rounds `< c`; in round `c` only its messages
  to `reach p` are delivered; afterwards it sends nothing. A crashed process does not decide, so
  its (formal) later states are irrelevant;
* `Adversary.Admissible f`: at most `f` processes crash;
* complexity measures: `awakeCount` (number of rounds among `1..R` in which `p` is awake and not
  yet crashed — the energy / awake complexity is its maximum over `p`) and `msgCount` (number of
  messages sent in rounds `1..R`, counting a message of a process in its crashing round even if it
  is lost).

Everything is computable for computable algorithms, so concrete executions can be checked by
`decide`.
-/

namespace Cslib.SleepingCrash

/-- A deterministic algorithm in the synchronous sleeping model on the complete network `P`, with
inputs `I`, local states `S` and messages `M`. -/
structure Algorithm (P I S M : Type*) where
  /-- Initial state from the input. -/
  init : P → I → S
  /-- `awake p r s`: `p` is awake in round `r` if its state at the start of the round is `s`. -/
  awake : P → ℕ → S → Bool
  /-- The message (if any) that `p`, awake in round `r` with state `s`, sends to `q`. -/
  send : P → ℕ → S → P → Option M
  /-- The new state of `p`, awake in round `r` with state `s`, after receiving `inbox`
  (`inbox q` = the message received from `q`). -/
  recv : P → ℕ → S → (P → Option M) → S

/-- The adversary: inputs and crash pattern. `crash p = some c`: `p` crashes in round `c`, and in
that round its messages are delivered only to `reach p`. -/
structure Adversary (P I : Type*) where
  /-- The inputs. -/
  input : P → I
  /-- Crash round (`none`: `p` never crashes). -/
  crash : P → Option ℕ
  /-- The processes still reached by `p` in its crashing round. -/
  reach : P → Finset P

namespace Adversary

variable {P I : Type*} (adv : Adversary P I)

/-- `p` has not crashed in rounds `1, …, r` (the paper's "alive in round `r + 1`"). -/
def Alive (p : P) (r : ℕ) : Prop := ∀ c, adv.crash p = some c → r < c

instance (p : P) (r : ℕ) : Decidable (adv.Alive p r) :=
  match h : adv.crash p with
  | none => isTrue (by intro c hc; simp [h] at hc)
  | some c =>
    if hr : r < c then isTrue (by intro c' hc'; rw [h] at hc'; cases hc'; exact hr)
    else isFalse (fun H => hr (H c h))

/-- `p` is faulty: it crashes at some point. -/
def Faulty (p : P) : Prop := adv.crash p ≠ none

instance (p : P) : Decidable (adv.Faulty p) := inferInstanceAs (Decidable (_ ≠ _))

/-- The adversary crashes at most `f` processes, each in some round `≥ 1`. -/
def Admissible [Fintype P] (f : ℕ) : Prop :=
  (Finset.univ.filter adv.Faulty).card ≤ f ∧ ∀ p c, adv.crash p = some c → 1 ≤ c

variable {adv}

lemma Alive.mono {p : P} {r r' : ℕ} (h : adv.Alive p r) (hr : r' ≤ r) : adv.Alive p r' :=
  fun c hc => lt_of_le_of_lt hr (h c hc)

lemma alive_of_not_faulty {p : P} (h : ¬ adv.Faulty p) (r : ℕ) : adv.Alive p r := by
  intro c hc
  exact absurd hc (by simp [Faulty] at h; simp [h])

lemma alive_iff_of_not_crash {p : P} {r : ℕ} (h : adv.crash p ≠ some (r + 1)) :
    adv.Alive p (r + 1) ↔ adv.Alive p r := by
  refine ⟨fun H => H.mono (Nat.le_succ r), fun H c hc => ?_⟩
  have := H c hc
  have : c ≠ r + 1 := fun e => h (e ▸ hc)
  omega

lemma Admissible.alive_zero [Fintype P] {f : ℕ} (h : adv.Admissible f) (p : P) :
    adv.Alive p 0 := fun c hc => h.2 p c hc

/-- More than `f` processes contain one that never crashes. -/
lemma Admissible.exists_not_faulty [Fintype P] {f : ℕ} (h : adv.Admissible f) {s : Finset P}
    (hs : f < s.card) : ∃ p ∈ s, ¬ adv.Faulty p := by
  by_contra H
  push Not at H
  have : s ⊆ Finset.univ.filter adv.Faulty := fun p hp => by simpa using H p hp
  exact absurd ((Finset.card_le_card this).trans h.1) (by omega)

/-- If at most `f` processes crash, one of the rounds `1, …, f + 1` is *clean*: nobody crashes
in it. -/
lemma Admissible.exists_clean_round [Fintype P] {f : ℕ} (h : adv.Admissible f) :
    ∃ t, 1 ≤ t ∧ t ≤ f + 1 ∧ ∀ p, adv.crash p ≠ some t := by
  classical
  by_contra H
  push Not at H
  -- every round `t ∈ [1, f+1]` is the crash round of some faulty process
  choose g hg using fun t : Finset.Icc 1 (f + 1) =>
    H t (Finset.mem_Icc.1 t.2).1 (Finset.mem_Icc.1 t.2).2
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 := hg a
    have h2 := hg b
    rw [hab, h2] at h1
    exact Subtype.ext (Option.some_injective _ h1).symm
  have : Fintype.card (Finset.Icc 1 (f + 1)) ≤ (Finset.univ.filter adv.Faulty).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun t => ⟨g t, by simp [Faulty, hg t]⟩) ?_
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  simp at this
  have := h.1
  omega

end Adversary

variable {P I S M : Type*} (alg : Algorithm P I S M) (adv : Adversary P I)

/-- Is the message of `p` to `q` in round `r` delivered (as far as the sender is concerned)?
`p` must not have crashed before round `r`, and if it crashes in round `r`, `q ∈ reach p`. -/
def Delivers (p q : P) (r : ℕ) : Prop :=
  adv.Alive p (r - 1) ∧ (adv.crash p = some r → q ∈ adv.reach p)

instance [DecidableEq P] (p q : P) (r : ℕ) : Decidable (Delivers adv p q r) := by
  unfold Delivers; infer_instance

/-- The message that `q` receives from `p` in round `r` when the states at the start of the round
are `s`: `p` must be awake and its message delivered (whether `q` is awake is checked by the
receiver, see `step`). -/
def inbox [DecidableEq P] (r : ℕ) (s : P → S) (q : P) (p : P) : Option M :=
  if alg.awake p r (s p) ∧ Delivers adv p q r then alg.send p r (s p) q else none

/-- One synchronous round `r`: awake processes receive and update; asleep ones keep their state. -/
def step [DecidableEq P] (r : ℕ) (s : P → S) (q : P) : S :=
  if alg.awake q r (s q) then alg.recv q r (s q) (inbox alg adv r s q) else s q

/-- The configuration at the end of round `r` (`r = 0`: initial states). -/
def config [DecidableEq P] : ℕ → P → S
  | 0 => fun p => alg.init p (adv.input p)
  | r + 1 => step alg adv (r + 1) (config r)

variable [DecidableEq P]

@[simp] lemma config_zero (p : P) : config alg adv 0 p = alg.init p (adv.input p) := rfl

lemma config_succ (r : ℕ) : config alg adv (r + 1) = step alg adv (r + 1) (config alg adv r) := rfl

lemma config_succ_apply (r : ℕ) (q : P) : config alg adv (r + 1) q =
    if alg.awake q (r + 1) (config alg adv r q) then
      alg.recv q (r + 1) (config alg adv r q) (inbox alg adv (r + 1) (config alg adv r) q)
    else config alg adv r q := rfl

/-- `p` is awake in round `r ≥ 1` (and has not crashed before). -/
def AwakeIn (p : P) (r : ℕ) : Prop :=
  adv.Alive p (r - 1) ∧ alg.awake p r (config alg adv (r - 1) p) = true

instance (p : P) (r : ℕ) : Decidable (AwakeIn alg adv p r) := by
  unfold AwakeIn; infer_instance

/-- The number of rounds among `1, …, R` in which `p` is awake (energy spent by `p`). The energy
(awake) complexity of an execution is the maximum of this over all processes. -/
def awakeCount (R : ℕ) (p : P) : ℕ :=
  ((Finset.Icc 1 R).filter (fun r => AwakeIn alg adv p r)).card

/-- `p` sends a message to `q` in round `r` (it is awake, has not crashed before, and its algorithm
produces a message; the message may be lost if `q` sleeps or `p` crashes in round `r`). -/
def SendsIn (p q : P) (r : ℕ) : Prop :=
  AwakeIn alg adv p r ∧ (alg.send p r (config alg adv (r - 1) p) q).isSome

instance (p q : P) (r : ℕ) : Decidable (SendsIn alg adv p q r) := by
  unfold SendsIn; infer_instance

/-- The number of messages sent in rounds `1, …, R`. -/
def msgCount [Fintype P] (R : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 R, (Finset.univ.filter (fun e : P × P => SendsIn alg adv e.1 e.2 r)).card

/-! ### Basic lemmas -/

variable {alg adv}

lemma inbox_eq_none_of_not_awake {r : ℕ} {s : P → S} {q p : P} (h : alg.awake p r (s p) = false) :
    inbox alg adv r s q p = none := by
  simp [inbox, h]

/-- A message from a process that does not crash in round `r` (and has not crashed before) is
delivered. -/
lemma inbox_eq_send {r : ℕ} {s : P → S} {q p : P} (hp : adv.Alive p r)
    (ha : alg.awake p r (s p) = true) : inbox alg adv r s q p = alg.send p r (s p) q := by
  have h1 : adv.Alive p (r - 1) := hp.mono (Nat.sub_le r 1)
  have h2 : adv.crash p = some r → q ∈ adv.reach p := fun hc => absurd (hp r hc) (lt_irrefl r)
  have : Delivers adv p q r := ⟨h1, h2⟩
  simp [inbox, ha, this]

/-- Received messages were sent. -/
lemma inbox_eq_some {r : ℕ} {s : P → S} {q p : P} {m : M} (h : inbox alg adv r s q p = some m) :
    alg.awake p r (s p) = true ∧ adv.Alive p (r - 1) ∧ alg.send p r (s p) q = some m := by
  unfold inbox at h
  split_ifs at h with h'
  · exact ⟨h'.1, h'.2.1, h⟩

lemma awakeCount_le_card [Fintype P] {R : ℕ} {p : P} {A : Finset ℕ}
    (h : ∀ r, 1 ≤ r → r ≤ R → AwakeIn alg adv p r → r ∈ A) : awakeCount alg adv R p ≤ A.card := by
  refine Finset.card_le_card fun r hr => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hr
  exact h r hr.1.1 hr.1.2 hr.2

end Cslib.SleepingCrash
