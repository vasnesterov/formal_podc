import Papers.PODC2021.TrustedHardwareUnidirectional.Rounds

-- CSLib candidate: generic model (SRB systems / round-layer spec), see README.
/-!
# Asynchronous Byzantine systems with sequenced reliable broadcast (Definition 1)

Every process `s` is the designated sender of one SRB instance. Since SRB delivers, at every
correct process, the messages of `s` in sequence-number order (property 3), and a sequence
number `k` delivered by one correct process is eventually delivered with the *same* message by all
correct processes (property 2), the messages of `s` that correct processes deliver form prefixes of
one common sequence, the *log* of `s` (`Config.log s`; the index in the log is the sequence
number). For a correct `s` the log is what `s` broadcast (property 4); a Byzantine `s` appends
arbitrary messages to its log, subject to unforgeability of signatures (see below).

* A protocol (`SRBProtocol`) is a deterministic message-driven state machine: initial state and
  initial broadcasts of `p` (given `p`'s client), and a reaction to the delivery of message `m`
  from sender `s`, returning the new state and the messages broadcast.
* `Config.dl q s` = number of messages of `s` delivered so far by `q`.
* Steps (`Step`): a correct `q` delivers the next message of some `s` (`deliver`), or a Byzantine
  `s` appends a message to its log (`byz`).
* **Signatures.** Each message `m` declares the messages of other processes it relays
  (`relays m`, pairs `(q, m')` = "`m` carries `q`'s signature on `m'`"). Correct processes sign
  exactly what they broadcast, so a Byzantine process can only relay `(q, m')` if `q` is
  Byzantine or `m'` is already in `q`'s log. Correct processes are not restricted (the protocol is
  trusted not to forge).
* Fairness (`Fair`): SRB properties 1 and 2 — a correct `q` eventually delivers every message of
  a correct sender, and every message of a Byzantine sender delivered by some correct process.

Asynchrony is the absence of any further constraint: the scheduler interleaves deliveries
arbitrarily. `SRBProtocol.Implements A f` says that `A` implements unidirectional rounds whenever
at most `f` processes are Byzantine, for every client.
-/

namespace Podc.TrustedHW

/-- Global configurations of an SRB system with messages `M` and local states `S`: logs of all SRB
instances, delivery counters, local states. -/
@[ext]
structure SRBConfig (P M S : Type) where
  /-- `log s`: the sequence of messages of sender `s` (index = sequence number). -/
  log : P → List M
  /-- `dl q s`: how many messages of `s` process `q` has delivered. -/
  dl : P → P → ℕ
  /-- Local states. -/
  st : P → S

/-- The configuration after Byzantine `s` appends `m` to its log. -/
def SRBConfig.append {P M S : Type} [DecidableEq P] (c : SRBConfig P M S) (s : P) (m : M) :
    SRBConfig P M S :=
  { c with log := Function.update c.log s (c.log s ++ [m]) }

/-- A protocol over sequenced reliable broadcast implementing rounds (see module docstring), with
messages `M` and local states `S`. -/
structure SRBProtocol (P V M S : Type) where
  /-- The signed messages of other processes contained in a message. -/
  relays : M → Set (P × M)
  /-- Initial local state and initial broadcasts. -/
  init : P → Client P V → S × List M
  /-- Reaction of `p` to the delivery of message `m` from sender `s`. -/
  step : P → Client P V → S → P → M → S × List M
  /-- The completed rounds (output of the round layer). -/
  rounds : S → List (P → Option V)

namespace SRBProtocol

variable {P V M S : Type} [DecidableEq P] (A : SRBProtocol P V M S)

/-- The configuration after `q` delivers `m` from `s` and reacts. -/
def deliver (c : SRBConfig P M S) (cl : P → Client P V) (q s : P) (m : M) : SRBConfig P M S :=
  { log := Function.update c.log q (c.log q ++ (A.step q (cl q) (c.st q) s m).2)
    dl := Function.update c.dl q (Function.update (c.dl q) s (c.dl q s + 1))
    st := Function.update c.st q (A.step q (cl q) (c.st q) s m).1 }

/-- Initial configurations for Byzantine set `F` and clients `cl`. -/
def Init (F : Finset P) (cl : P → Client P V) (c : SRBConfig P M S) : Prop :=
  (∀ p, p ∉ F → c.st p = (A.init p (cl p)).1 ∧ c.log p = (A.init p (cl p)).2) ∧
    (∀ p ∈ F, c.log p = []) ∧ ∀ q s, c.dl q s = 0

/-- Atomic steps. -/
inductive Step (F : Finset P) (cl : P → Client P V) : SRBConfig P M S → SRBConfig P M S → Prop
  /-- Correct `q` delivers the next message `m` of sender `s`. -/
  | deliver (c : SRBConfig P M S) (q s : P) (m : M) (hq : q ∉ F) (hm : (c.log s)[c.dl q s]? = some m) :
      Step F cl c (A.deliver c cl q s m)
  /-- Byzantine `s` broadcasts `m`; it may relay only signatures that exist. -/
  | byz (c : SRBConfig P M S) (s : P) (m : M) (hs : s ∈ F)
      (hm : ∀ x ∈ A.relays m, x.1 ∈ F ∨ x.2 ∈ c.log x.1) :
      Step F cl c (c.append s m)

/-- Fairness = SRB properties 1 and 2. -/
def Fair (F : Finset P) (e : ℕ → SRBConfig P M S) : Prop :=
  ∀ q, q ∉ F → ∀ s k, (∃ t, k < ((e t).log s).length) →
    (s ∉ F ∨ ∃ q', q' ∉ F ∧ ∃ t, k < (e t).dl q' s) → ∃ t, k < (e t).dl q s

/-- The round system of protocol `A` with Byzantine set `F` and clients `cl`. -/
abbrev system (F : Finset P) (cl : P → Client P V) : RoundSystem P V where
  Config := SRBConfig P M S
  Init := A.Init F cl
  Step := A.Step F cl
  Fair := Fair F
  rounds c p := A.rounds (c.st p)

/-- `A` implements unidirectional rounds over SRB with at most `f` Byzantine processes. -/
def Implements [Fintype P] (f : ℕ) : Prop :=
  ∀ F : Finset P, F.card ≤ f → ∀ cl : P → Client P V,
    (A.system F cl).ImplementsUnidirectional (· ∉ F) cl

/-! ### Basic facts -/

variable {A} {F : Finset P} {cl : P → Client P V}

lemma Step.log_prefix {c c' : SRBConfig P M S} (h : A.Step F cl c c') (s : P) :
    c.log s <+: c'.log s := by
  cases h with
  | deliver q s' m hq hm =>
    simp only [SRBProtocol.deliver]
    by_cases hs : s = q
    · subst hs; simp
    · simp [Function.update_of_ne hs]
  | byz s' m hs hm =>
    simp only [SRBConfig.append]
    by_cases h : s = s'
    · subst h; simp
    · simp [Function.update_of_ne h]

lemma Step.dl_mono {c c' : SRBConfig P M S} (h : A.Step F cl c c') (q s : P) :
    c.dl q s ≤ c'.dl q s := by
  cases h with
  | deliver q' s' m hq hm =>
    simp only [SRBProtocol.deliver]
    by_cases h1 : q = q'
    · subst h1
      by_cases h2 : s = s'
      · subst h2; simp
      · simp [Function.update_of_ne h2]
    · simp [Function.update_of_ne h1]
  | byz => exact le_rfl

lemma Step.st_eq_of_ne {c c' : SRBConfig P M S} (h : A.Step F cl c c') {p : P}
    (hp : ∀ s m, c' ≠ A.deliver c cl p s m) : c'.st p = c.st p := by
  cases h with
  | deliver q s m hq hm =>
    by_cases hpq : p = q
    · subst hpq; exact absurd rfl (hp s m)
    · simp [SRBProtocol.deliver, Function.update_of_ne hpq]
  | byz => rfl

section simpLemmas

variable {c : SRBConfig P M S} {q s x y : P} {m : M}

@[simp] lemma deliver_log_self : (A.deliver c cl q s m).log q = c.log q ++ (A.step q (cl q) (c.st q) s m).2 := by
  simp [SRBProtocol.deliver]

lemma deliver_log_of_ne (h : x ≠ q) : (A.deliver c cl q s m).log x = c.log x := by
  simp [SRBProtocol.deliver, Function.update_of_ne h]

@[simp] lemma deliver_st_self : (A.deliver c cl q s m).st q = (A.step q (cl q) (c.st q) s m).1 := by
  simp [SRBProtocol.deliver]

lemma deliver_st_of_ne (h : x ≠ q) : (A.deliver c cl q s m).st x = c.st x := by
  simp [SRBProtocol.deliver, Function.update_of_ne h]

@[simp] lemma deliver_dl_self : (A.deliver c cl q s m).dl q s = c.dl q s + 1 := by
  simp [SRBProtocol.deliver]

lemma deliver_dl_of_ne (h : x ≠ q ∨ y ≠ s) : (A.deliver c cl q s m).dl x y = c.dl x y := by
  rcases h with h | h
  · simp [SRBProtocol.deliver, Function.update_of_ne h]
  · by_cases hx : x = q
    · subst hx; simp [SRBProtocol.deliver, Function.update_of_ne h]
    · simp [SRBProtocol.deliver, Function.update_of_ne hx]

lemma deliver_log_prefix : c.log x <+: (A.deliver c cl q s m).log x := by
  by_cases h : x = q
  · subst h; simp
  · rw [deliver_log_of_ne h]

@[simp] lemma append_log_self : (c.append s m).log s = c.log s ++ [m] := by simp [SRBConfig.append]

lemma append_log_of_ne (h : x ≠ s) : (c.append s m).log x = c.log x := by
  simp [SRBConfig.append, Function.update_of_ne h]

@[simp] lemma append_st : (c.append s m).st = c.st := rfl

@[simp] lemma append_dl : (c.append s m).dl = c.dl := rfl

lemma append_log_prefix : c.log x <+: (c.append s m).log x := by
  by_cases h : x = s
  · subst h; simp
  · rw [append_log_of_ne h]

end simpLemmas

/-- In reachable configurations, delivery counters never exceed the log length, and Byzantine
processes deliver nothing. -/
lemma dl_le_length {c : SRBConfig P M S} (hc : (A.system F cl).Reachable c) :
    ∀ q s, c.dl q s ≤ (c.log s).length := by
  obtain ⟨c₀, h₀, hr⟩ := hc
  induction hr with
  | refl => intro q s; simp [h₀.2.2]
  | tail _ h ih =>
    rename_i c₁ c₂ _
    intro q s
    cases h with
    | deliver q' s' m hq hm =>
      have hlt : c₁.dl q' s' < (c₁.log s').length := by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hm
        exact absurd hm (by simp)
      have ih' := ih q s
      simp only [SRBProtocol.deliver]
      by_cases h1 : q = q'
      · subst h1
        by_cases h2 : s = s'
        · subst h2
          by_cases h3 : s = q
          · subst h3; simp; omega
          · simp [Function.update_of_ne h3]; omega
        · simp only [Function.update_self, Function.update_of_ne h2]
          by_cases h3 : s = q
          · subst h3; simp; omega
          · simp [Function.update_of_ne h3]; exact ih'
      · simp only [Function.update_of_ne h1]
        by_cases h3 : s = q'
        · subst h3; simp; omega
        · simp [Function.update_of_ne h3]; exact ih'
    | byz s' m hs hm =>
      have ih' := ih q s
      simp only [SRBConfig.append]
      by_cases h3 : s = s'
      · subst h3; simp; omega
      · simp [Function.update_of_ne h3]; exact ih'

/-- Along an execution, logs only grow. -/
lemma log_prefix_of_le {e : ℕ → SRBConfig P M S} (he : (A.system F cl).IsExec e) {t t' : ℕ}
    (h : t ≤ t') (s : P) : (e t).log s <+: (e t').log s :=
  RoundSystem.IsExec.mono (S := A.system F cl) he (R := fun a b => a.log s <+: b.log s)
    (fun _ => List.prefix_refl _) (fun _ _ _ h1 h2 => h1.trans h2)
    (fun _ _ _ h => h.log_prefix s) h

/-- Along an execution, delivery counters only grow. -/
lemma dl_le_of_le {e : ℕ → SRBConfig P M S} (he : (A.system F cl).IsExec e) {t t' : ℕ}
    (h : t ≤ t') (q s : P) : (e t).dl q s ≤ (e t').dl q s :=
  RoundSystem.IsExec.mono (S := A.system F cl) he (R := fun a b => a.dl q s ≤ b.dl q s)
    (fun _ => le_rfl) (fun _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ h => h.dl_mono q s) h

end SRBProtocol

end Podc.TrustedHW
