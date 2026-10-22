import Mathlib
import Cslib.Computability.Distributed.SyncCrash.Model

/-!
# Rational consensus: the game (Section 2 of Halpern–Vilaça)

The consensus game of [Halpern, Vilaça, *Rational Consensus*, PODC 2016] on top of CSLib's
synchronous crash model (`Cslib.SyncCrash`).

* **Agents** `P` (a finite type, `n = |P|`), synchronous rounds, reliable channels, crash failures.
* **Strategies.** A strategy profile is a CSLib lock-step protocol
  (`Cslib.Byzantine.LockStep.Protocol`) whose input is the pair *(initial preference, random seed)*:
  agent `p` with preference `v` and seed `ω p : Ω` sends `σ.send p (v, ω p) h q` to `q` and has
  decided `σ.decide p (v, ω p) h` after history `h` (the list of inboxes received so far).
  Randomization is thus by private seeds; the seed vector `ω : P → Ω` is drawn from an arbitrary
  probability measure `μ`. Decisions are `Option Bool`: `some b` decides `b`, `none` decides `⊥`.
* **Contexts** (`Context`): initial preferences and a failure pattern (crash round and the set of
  agents still reached in the crashing round), exactly as `Cslib.SyncCrash.Run` without the inputs.
* **Outcome** (`outcome`): consensus on `b` iff every nonfaulty agent's (first) decision is `b`.
* **Utilities** (`Utility`): agents *care only about consensus*: `β₀ i > β₁ i > β₂ i` are `i`'s
  utilities for consensus on its own preference, consensus on the other value, and no consensus.
* **Solution concepts.** `SolvesFairConsensus μ σ f` (agreement, termination, integrity, validity
  almost surely, plus fairness) and `IsEpsNash μ u σ ε f` (`ε`–`f`-Nash equilibrium: in every
  context with at most `f` faulty agents no agent gains more than `ε` by a unilateral deviation).

The simulation lemmas at the end (`status_ignore`, `status_congr_silent`) are the two
indistinguishability arguments used in the proof of Theorem 1.
-/

namespace Podc.RationalConsensus

open Cslib Cslib.SyncCrash MeasureTheory
open scoped ENNReal

/-- Outcomes of a run of the consensus game. -/
inductive Outcome
  /-- All nonfaulty agents decided the value `b`. -/
  | cons (b : Bool)
  /-- No consensus. -/
  | noCons
  deriving DecidableEq, Fintype

instance : MeasurableSpace Outcome := ⊤

instance : DiscreteMeasurableSpace Outcome := ⟨fun _ => trivial⟩

/-- A strategy profile: a lock-step protocol with input *(preference, seed)* and decisions in
`Option Bool` (`none` = `⊥`). -/
abbrev Profile (P M Ω : Type*) :=
  Cslib.Byzantine.LockStep.Protocol P (Bool × Ω) M (Option Bool)

/-- A context: initial preferences and a failure pattern. `crash p = some m`: `p` crashes in round
`m ≥ 1`, sending its round-`m` messages only to `reach p`. -/
structure Context (P : Type*) where
  /-- Initial preferences. -/
  pref : P → Bool
  /-- Crash round (`none` = nonfaulty). -/
  crash : P → Option ℕ
  /-- Agents reached in the crashing round. -/
  reach : P → Set P

namespace Context

variable {P Ω : Type*} (c : Context P)

/-- The run of the crash model determined by a context and a seed vector. -/
def run (ω : P → Ω) : SyncCrash.Run P (Bool × Ω) :=
  ⟨fun p => (c.pref p, ω p), c.crash, c.reach⟩

/-- `p` is faulty in the context. -/
def Faulty (p : P) : Prop := c.crash p ≠ none

open Classical in
/-- The set of faulty agents. -/
noncomputable def faulty [Fintype P] : Finset P := Finset.univ.filter c.Faulty

/-- At most `f` agents crash (and crash rounds are `≥ 1`). -/
def Admissible [Fintype P] (f : ℕ) : Prop :=
  c.faulty.card ≤ f ∧ ∀ p m, c.crash p = some m → 1 ≤ m

@[simp] lemma run_crash (ω : P → Ω) : (c.run ω).crash = c.crash := rfl

@[simp] lemma run_reach (ω : P → Ω) : (c.run ω).reach = c.reach := rfl

@[simp] lemma run_input (ω : P → Ω) (p : P) : (c.run ω).input p = (c.pref p, ω p) := rfl

lemma faulty_run_iff (ω : P → Ω) (p : P) : (c.run ω).Faulty p ↔ c.Faulty p := Iff.rfl

end Context

variable {P M Ω : Type*}

section Decisions

variable (σ : Profile P M Ω) (c : Context P) (ω : P → Ω)

/-- The decision status of `p` at time `t` (`none`: undecided, or crashed by time `t`). -/
noncomputable def status (p : P) (t : ℕ) : Option (Option Bool) :=
  (SyncCrash.state σ (c.run ω) p t).bind fun s => σ.decide p s.1 s.2

/-- The (first, hence only: *Integrity*) decision of `p` is `o`. -/
def Decides (p : P) (o : Option Bool) : Prop :=
  Cslib.Byzantine.LockStep.FirstSome (status σ c ω p) o

/-- All nonfaulty agents decide `b`. -/
def ConsOn (b : Bool) : Prop := ∀ p, ¬ c.Faulty p → Decides σ c ω p (some b)

open Classical in
/-- The outcome of the run. (If there is no nonfaulty agent, there is no consensus.) -/
noncomputable def outcome : Outcome :=
  if ConsOn σ c ω true ∧ ¬ ConsOn σ c ω false then .cons true
  else if ConsOn σ c ω false ∧ ¬ ConsOn σ c ω true then .cons false
  else .noCons

/-- Agreement, termination and validity in one run (integrity holds by construction: `Decides`
is the first decision). -/
structure IsConsensusRun : Prop where
  /-- Agreement: no two nonfaulty agents decide differently. -/
  agreement : ∀ p q, ¬ c.Faulty p → ¬ c.Faulty q → ∀ o o',
    Decides σ c ω p o → Decides σ c ω q o' → o = o'
  /-- Termination: every nonfaulty agent decides. -/
  termination : ∀ p, ¬ c.Faulty p → ∃ o, Decides σ c ω p o
  /-- Validity: a decided value (`⊥` is not a value) is the initial preference of some agent. -/
  validity : ∀ p o, Decides σ c ω p o → ∃ b, o = some b ∧ ∃ q, c.pref q = b

end Decisions

/-- Agents *care only about consensus*: `β₀ i > β₁ i > β₂ i`. -/
structure Utility (P : Type*) where
  /-- Utility of `i` for a consensus on its own initial preference. -/
  β₀ : P → ℝ
  /-- Utility of `i` for a consensus on the other value. -/
  β₁ : P → ℝ
  /-- Utility of `i` if there is no consensus. -/
  β₂ : P → ℝ
  lt₀₁ : ∀ i, β₁ i < β₀ i
  lt₁₂ : ∀ i, β₂ i < β₁ i

/-- The utility of agent `i` with initial preference `v` for an outcome. -/
def Utility.val (u : Utility P) (i : P) (v : Bool) : Outcome → ℝ
  | .cons b => if b = v then u.β₀ i else u.β₁ i
  | .noCons => u.β₂ i

/-- `i`'s expected utility for the profile `σ` in the context `c` (the expectation is over the
seeds). -/
noncomputable def expUtil [MeasurableSpace Ω] (μ : Measure (P → Ω)) (u : Utility P) (σ : Profile P M Ω)
    (c : Context P) (i : P) : ℝ :=
  ∫ ω, u.val i (c.pref i) (outcome σ c ω) ∂μ

/-- Agent `i` deviates to (the `i`-component of) `τ`. -/
def deviate [DecidableEq P] (σ τ : Profile P M Ω) (i : P) : Profile P M Ω where
  send p := if p = i then τ.send p else σ.send p
  decide p := if p = i then τ.decide p else σ.decide p

section Defs

variable [Fintype P]

open Classical in
/-- **Fair consensus** (Section 2): in every context with at most `f` failures, agreement,
termination, integrity and validity hold almost surely, and if `k` nonfaulty agents prefer `b`, the
probability of a consensus on `b` is at least `k / n`. -/
structure SolvesFairConsensus [MeasurableSpace Ω] (μ : Measure (P → Ω)) (σ : Profile P M Ω) (f : ℕ) : Prop where
  consensus : ∀ c : Context P, c.Admissible f → ∀ᵐ ω ∂μ, IsConsensusRun σ c ω
  fair : ∀ c : Context P, c.Admissible f → ∀ b : Bool,
    ((Finset.univ.filter fun p => ¬ c.Faulty p ∧ c.pref p = b).card : ℝ≥0∞) / Fintype.card P ≤
      μ {ω | outcome σ c ω = .cons b}

/-- **`ε`–`f`-Nash equilibrium** (Section 2): for every context with at most `f` faulty agents and
every agent `i`, no strategy of `i` improves `i`'s expected utility by more than `ε`. We require
the outcome to be measurable, so that expected utilities are meaningful; only deviations with a
measurable outcome are considered (this only makes "not an equilibrium" harder to prove). -/
def IsEpsNash [DecidableEq P] [MeasurableSpace Ω] (μ : Measure (P → Ω)) (u : Utility P) (σ : Profile P M Ω) (ε : ℝ)
    (f : ℕ) : Prop :=
  ∀ c : Context P, c.Admissible f → AEMeasurable (outcome σ c) μ ∧
    ∀ (i : P) (τ : Profile P M Ω), AEMeasurable (outcome (deviate σ τ i) c) μ →
      expUtil μ u (deviate σ τ i) c i ≤ expUtil μ u σ c i + ε

/-- **`f`-Nash equilibrium** = `0`–`f`-Nash equilibrium. -/
def IsNash [DecidableEq P] [MeasurableSpace Ω] (μ : Measure (P → Ω)) (u : Utility P) (σ : Profile P M Ω)
    (f : ℕ) : Prop :=
  IsEpsNash μ u σ 0 f

end Defs

/-! ### Basic lemmas on outcomes -/

section Lemmas

variable {σ : Profile P M Ω} {c : Context P} {ω : P → Ω}

lemma Decides.unique {p : P} {o o' : Option Bool} (h : Decides σ c ω p o)
    (h' : Decides σ c ω p o') : o = o' :=
  Cslib.Byzantine.LockStep.FirstSome.unique h h'

lemma not_consOn_of_consOn {b : Bool} {p : P} (hp : ¬ c.Faulty p) (h : ConsOn σ c ω b) :
    ¬ ConsOn σ c ω (!b) := by
  intro h'
  have := (h p hp).unique (h' p hp)
  cases b <;> simp at this

/-- If some agent is nonfaulty, the outcome is `cons b` iff all nonfaulty agents decide `b`. -/
lemma outcome_eq_cons_iff {p : P} (hp : ¬ c.Faulty p) (b : Bool) :
    outcome σ c ω = .cons b ↔ ConsOn σ c ω b := by
  have h1 := not_consOn_of_consOn (σ := σ) (ω := ω) (b := true) hp
  have h2 := not_consOn_of_consOn (σ := σ) (ω := ω) (b := false) hp
  simp only [Bool.not_true, Bool.not_false] at h1 h2
  unfold outcome
  cases b <;> by_cases ht : ConsOn σ c ω true <;> by_cases hf : ConsOn σ c ω false <;>
    simp_all

/-- In a consensus run with a nonfaulty agent, the outcome is a consensus on some value. -/
lemma IsConsensusRun.exists_outcome {p : P} (hp : ¬ c.Faulty p) (h : IsConsensusRun σ c ω) :
    ∃ b, outcome σ c ω = .cons b := by
  obtain ⟨o, ho⟩ := h.termination p hp
  obtain ⟨b, rfl, -⟩ := h.validity p o ho
  refine ⟨b, (outcome_eq_cons_iff hp b).2 fun q hq => ?_⟩
  obtain ⟨o', ho'⟩ := h.termination q hq
  rwa [← h.agreement p q hp hq _ _ ho ho'] at ho'

lemma outcome_eq_of_status {σ' : Profile P M Ω} {c' : Context P} {ω' : P → Ω}
    (hF : ∀ p, c.Faulty p ↔ c'.Faulty p)
    (hs : ∀ p, ¬ c.Faulty p → status σ c ω p = status σ' c' ω' p) :
    outcome σ c ω = outcome σ' c' ω' := by
  have hc : ∀ b, ConsOn σ c ω b ↔ ConsOn σ' c' ω' b := by
    intro b
    simp only [ConsOn, Decides]
    refine forall_congr' fun p => ?_
    by_cases hp : c.Faulty p
    · exact ⟨fun _ h => absurd ((hF p).1 hp) h, fun _ h => absurd hp h⟩
    · rw [hs p hp]; exact ⟨fun h _ => h hp, fun h _ => h ((hF p).not.1 hp)⟩
  have hc' : ∀ b, ConsOn σ c ω b = ConsOn σ' c' ω' b := fun b => propext (hc b)
  unfold outcome
  rw [hc' true, hc' false]

end Lemmas

/-! ### Simulation lemmas -/

section Simulation

variable [DecidableEq P]

open Cslib.Byzantine.LockStep

/-- Erase the message from `i` in the inbox of round `t₀ + 1` of a history. -/
def eraseMsg (i : P) (t₀ : ℕ) (h : History P M) : History P M :=
  h.mapIdx fun k inbox => if k = t₀ then Function.update inbox i none else inbox

lemma eraseMsg_append_singleton (i : P) (t₀ : ℕ) (h : History P M) (x : Inbox P M) :
    eraseMsg i t₀ (h ++ [x]) =
      eraseMsg i t₀ h ++ [if h.length = t₀ then Function.update x i none else x] := by
  simp [eraseMsg, List.mapIdx_append]

/-- The profile in which everybody runs `σ` but ignores the message from `i` received in round
`t₀ + 1` (only its component at the deviating agent matters). -/
def ignore (σ : Profile P M Ω) (i : P) (t₀ : ℕ) : Profile P M Ω where
  send p x h := σ.send p x (eraseMsg i t₀ h)
  decide p x h := σ.decide p x (eraseMsg i t₀ h)

@[simp] lemma deviate_send_self (σ τ : Profile P M Ω) (i : P) :
    (deviate σ τ i).send i = τ.send i := by simp [deviate]

@[simp] lemma deviate_send_ne (σ τ : Profile P M Ω) {i p : P} (h : p ≠ i) :
    (deviate σ τ i).send p = σ.send p := by simp [deviate, h]

@[simp] lemma deviate_decide_self (σ τ : Profile P M Ω) (i : P) :
    (deviate σ τ i).decide i = τ.decide i := by simp [deviate]

@[simp] lemma deviate_decide_ne (σ τ : Profile P M Ω) {i p : P} (h : p ≠ i) :
    (deviate σ τ i).decide p = σ.decide p := by simp [deviate, h]

/-- **Pretending not to have received a message.** Let the run `r'` deliver exactly the messages
of `r`, plus the message from `i` to `j ≠ i` in round `t₀ + 1` (which `r` does not deliver). If
`j` ignores that message, every agent has the same history in `r'` as in `r` (`j` up to the
erased message). -/
lemma hist_ignore (σ : Profile P M Ω) {r r' : SyncCrash.Run P (Bool × Ω)} {i j : P} {t₀ : ℕ}
    (hij : i ≠ j) (hin : ∀ p, r.input p = r'.input p)
    (hD : ∀ p q t, p ≠ q → (r'.Deliv p q t ↔ r.Deliv p q t ∨ (p = i ∧ q = j ∧ t = t₀)))
    (hn : ¬ r.Deliv i j t₀) (t : ℕ) :
    eraseMsg i t₀ (hist (deviate σ (ignore σ i t₀) j) r' t j) = hist σ r t j ∧
      ∀ p, p ≠ j → hist (deviate σ (ignore σ i t₀) j) r' t p = hist σ r t p := by
  set σ' := deviate σ (ignore σ i t₀) j
  induction t with
  | zero => exact ⟨by simp [eraseMsg], fun p _ => by simp⟩
  | succ t ih =>
    -- the messages coincide except for the one from `i` to `j` in round `t₀ + 1`
    have hmsg : ∀ y q, ¬ (y = i ∧ q = j ∧ t = t₀) → msg σ' r' y q t = msg σ r y q t := by
      intro y q hyq
      rw [msg_eq_deliv, msg_eq_deliv]
      have hd : y ≠ q → (r'.Deliv y q t ↔ r.Deliv y q t) := fun hne => by
        rw [hD y q t hne]; tauto
      by_cases hyq' : y ≠ q ∧ r.Deliv y q t
      · rw [ite_eq_left ⟨hyq'.1, (hd hyq'.1).2 hyq'.2⟩, ite_eq_left hyq', ← hin y]
        by_cases hy : y = j
        · subst hy; rw [deviate_send_self]; exact congrArg (σ.send y _ · q) ih.1
        · rw [deviate_send_ne _ _ hy, ih.2 y hy]
      · rw [ite_eq_right hyq', ite_eq_right]
        rintro ⟨h1, h2⟩; exact hyq' ⟨h1, (hd h1).1 h2⟩
    refine ⟨?_, fun p hp => ?_⟩
    · rw [SyncCrash.hist_succ, SyncCrash.hist_succ, eraseMsg_append_singleton, ih.1, SyncCrash.length_hist]
      congr 2
      funext y
      by_cases hc : t = t₀ ∧ y = i
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [ite_true, Function.update_self]
        rw [msg_eq_deliv, ite_eq_right (fun h => hn h.2)]
      · have : (if t = t₀ then Function.update (fun p => msg σ' r' p j t) i none else
            fun p => msg σ' r' p j t) y = msg σ' r' y j t := by
          split_ifs with h
          · rw [Function.update_of_ne (fun hy => hc ⟨h, hy⟩)]
          · rfl
        rw [this, hmsg y j (fun h => hc ⟨h.2.2, h.1⟩)]
    · rw [SyncCrash.hist_succ, SyncCrash.hist_succ, ih.2 p hp]
      congr 2
      funext y
      exact hmsg y p (fun h => hp h.2.1)

/-- Under the hypotheses of `hist_ignore`, every agent other than `i` (alive in the same rounds in
both runs) has the same decision status in `r'` with `j` ignoring the message as in `r`. -/
lemma status_ignore (σ : Profile P M Ω) {c c' : Context P} {ω : P → Ω} {i j : P} {t₀ : ℕ}
    (hij : i ≠ j) (hpref : c.pref = c'.pref) (hcr : ∀ p, p ≠ i → c.crash p = c'.crash p)
    (hD : ∀ p q t, p ≠ q →
      ((c'.run ω).Deliv p q t ↔ (c.run ω).Deliv p q t ∨ (p = i ∧ q = j ∧ t = t₀)))
    (hn : ¬ (c.run ω).Deliv i j t₀) (p : P) (hp : p ≠ i) :
    status (deviate σ (ignore σ i t₀) j) c' ω p = status σ c ω p := by
  funext t
  have hh := hist_ignore σ hij (fun q => by simp [hpref]) hD hn t
  have hal : (c'.run ω).Alive p t ↔ (c.run ω).Alive p t := by
    simp [SyncCrash.Run.Alive, hcr p hp]
  simp only [status, SyncCrash.state]
  by_cases ha : (c.run ω).Alive p t
  · rw [ite_eq_left (hal.2 ha), ite_eq_left ha]
    simp only [Option.bind_some, Context.run_input, hpref]
    by_cases hpj : p = j
    · subst hpj; rw [deviate_decide_self]; exact congrArg (σ.decide p _ ·) hh.1
    · rw [deviate_decide_ne _ _ hpj, hh.2 p hpj]
  · rw [ite_eq_right (fun h => ha (hal.1 h)), ite_eq_right ha]; rfl

/-- **A silent agent.** If `i` never delivers a message (e.g. it crashes in round `1` reaching
nobody), the other agents cannot tell `i`'s input: two contexts that differ only in `i`'s
preference give every other agent the same decision status. -/
lemma status_congr_silent (σ : Profile P M Ω) {c c' : Context P} (ω : P → Ω) {i : P}
    (hpref : ∀ p, p ≠ i → c.pref p = c'.pref p) (hcr : c.crash = c'.crash)
    (hre : c.reach = c'.reach) (hsil : ∀ q t, ¬ (c.run ω).Deliv i q t) (p : P) (hp : p ≠ i) :
    status σ c ω p = status σ c' ω p := by
  have hD : ∀ p q t, (c.run ω).Deliv p q t ↔ (c'.run ω).Deliv p q t := by
    intro p q t; simp [SyncCrash.Run.Deliv, SyncCrash.Run.Alive, hcr, hre]
  have hh : ∀ t, ∀ p, p ≠ i → hist σ (c.run ω) t p = hist σ (c'.run ω) t p := by
    intro t
    induction t with
    | zero => intros; rfl
    | succ t ih =>
      intro p hp
      rw [SyncCrash.hist_succ, SyncCrash.hist_succ, ih p hp]
      congr 2
      funext y
      by_cases hy : y = i
      · subst hy
        rw [msg_eq_deliv, msg_eq_deliv, ite_eq_right (fun h => hsil p t h.2),
          ite_eq_right (fun h => hsil p t ((hD _ _ _).2 h.2))]
      · exact msg_congr (by simp [hpref y hy]) (fun _ => ih y hy) (hD y p t)
  funext t
  have hst : SyncCrash.state σ (c.run ω) p t = SyncCrash.state σ (c'.run ω) p t := by
    unfold SyncCrash.state
    have hal : (c.run ω).Alive p t ↔ (c'.run ω).Alive p t := by
      simp [SyncCrash.Run.Alive, hcr]
    by_cases ha : (c.run ω).Alive p t
    · rw [ite_eq_left ha, ite_eq_left (hal.1 ha), Context.run_input, Context.run_input, hpref p hp,
        hh t p hp]
    · rw [ite_eq_right ha, ite_eq_right (fun h => ha (hal.2 h))]
  simp only [status, hst]

end Simulation

end Podc.RationalConsensus
