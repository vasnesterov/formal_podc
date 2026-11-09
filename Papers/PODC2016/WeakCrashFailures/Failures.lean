import Podc.Computability.Distributed.SWMR.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card

/-!
# Weak crash failures (m-failures of type 1)

G. Taubenfeld, *Computing in the presence of weak crash failures*, PODC 2016 (brief announcement);
full version *Weak Failures: Definitions, Algorithms and Impossibility Results* (2018), §1.1.

Executions are described by their infinite schedule `σ : ℕ → P` (`σ t` takes the `t`-th step),
as in `Cslib.SWMR`: a process is *correct* if it takes infinitely many steps (`InfOften`) and
*faulty* otherwise (`Faulty`). A process that has terminated keeps taking (no-op) steps, so it is
correct; hence "participation is required": every correct process takes steps.

* A process *participates* at time `t` if it has taken a step before `t` (`started σ t`).
* The *point contention* at time `t` is the number of participating processes (`contention σ t`).
  It never decreases (`contention_mono`).
* An *m-failure of type 1* (`WeakFailure m σ p`): `p` stops taking steps from some time `t` on, and
  at that time the point contention is at most `m` (the crash "occurs" at time `t`). Since the
  contention never decreases, the most permissive choice of `t` is right after `p`'s last step.
* An *initial failure*: the process never takes a step.

With `m ≥ |P|` an m-failure is an ordinary crash failure (`weakFailure_iff_faulty`).
-/

namespace Podc.WeakCrashFailures

open Cslib.SWMR

variable {P : Type} [DecidableEq P]

/-- The processes that have taken at least one step before time `t` (the participating ones). -/
def started (σ : ℕ → P) (t : ℕ) : Finset P := (pre σ t).toFinset

/-- The point contention at time `t`: the number of processes that have taken a step before `t`. -/
def contention (σ : ℕ → P) (t : ℕ) : ℕ := (started σ t).card

/-- `p` takes no step at time `t` or later. -/
def StoppedFrom (σ : ℕ → P) (p : P) (t : ℕ) : Prop := ∀ s, t ≤ s → σ s ≠ p

/-- An *m-failure of type 1* of `p` in the schedule `σ`: `p` crashes (takes no step from time `t`
on) at a time `t` at which the point contention is at most `m`. -/
def WeakFailure (m : ℕ) (σ : ℕ → P) (p : P) : Prop :=
  ∃ t, StoppedFrom σ p t ∧ contention σ t ≤ m

/-- An *initial failure*: `p` never takes a step. -/
def InitialFailure (σ : ℕ → P) (p : P) : Prop := StoppedFrom σ p 0

/-- The schedule `σ` has at most `f` faulty processes, all of which are m-failures
("at most `f` crash m-failures"). -/
def WeakAdmissible (m f : ℕ) (σ : ℕ → P) : Prop :=
  (Faulty σ).ncard ≤ f ∧ ∀ p ∈ Faulty σ, WeakFailure m σ p

lemma mem_started {σ : ℕ → P} {t : ℕ} {p : P} : p ∈ started σ t ↔ ∃ s < t, σ s = p := by
  simp [started, pre]

lemma started_succ (σ : ℕ → P) (t : ℕ) : started σ (t + 1) = insert (σ t) (started σ t) := by
  ext p
  simp only [mem_started, Finset.mem_insert]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
    · exact Or.inr ⟨s, h, rfl⟩
    · exact Or.inl (by rw [h])
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨t, Nat.lt_succ_self t, rfl⟩
    · exact ⟨s, Nat.lt_succ_of_lt hs, rfl⟩

lemma started_mono (σ : ℕ → P) {t t' : ℕ} (h : t ≤ t') : started σ t ⊆ started σ t' := by
  intro p hp
  obtain ⟨s, hs, rfl⟩ := mem_started.1 hp
  exact mem_started.2 ⟨s, lt_of_lt_of_le hs h, rfl⟩

/-- The point contention never decreases. -/
lemma contention_mono (σ : ℕ → P) {t t' : ℕ} (h : t ≤ t') : contention σ t ≤ contention σ t' :=
  Finset.card_le_card (started_mono σ h)

omit [DecidableEq P] in
lemma StoppedFrom.mono {σ : ℕ → P} {p : P} {t t' : ℕ} (h : StoppedFrom σ p t) (ht : t ≤ t') :
    StoppedFrom σ p t' := fun s hs => h s (le_trans ht hs)

omit [DecidableEq P] in
lemma StoppedFrom.faulty {σ : ℕ → P} {p : P} {t : ℕ} (h : StoppedFrom σ p t) : p ∈ Faulty σ := by
  intro hinf
  obtain ⟨m, hm, hmp⟩ := hinf t
  exact h m hm hmp

/-- A weakly failing process is faulty. -/
lemma WeakFailure.faulty {m : ℕ} {σ : ℕ → P} {p : P} (h : WeakFailure m σ p) : p ∈ Faulty σ := by
  obtain ⟨t, ht, -⟩ := h
  exact ht.faulty

lemma WeakFailure.mono {m m' : ℕ} {σ : ℕ → P} {p : P} (h : WeakFailure m σ p) (hm : m ≤ m') :
    WeakFailure m' σ p := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, ht, le_trans hc hm⟩

omit [DecidableEq P] in
/-- A faulty process stops taking steps from some time on. -/
lemma exists_stoppedFrom_of_faulty {σ : ℕ → P} {p : P} (h : p ∈ Faulty σ) :
    ∃ t, StoppedFrom σ p t := by
  by_contra hc
  simp only [StoppedFrom, not_exists, not_forall, not_not] at hc
  apply h
  intro N
  obtain ⟨s, hs, hsp⟩ := hc N
  exact ⟨s, hs, hsp⟩

/-- An initial failure is an m-failure of type 1 for every `m` (the crash happens at time `0`,
when the contention is `0`). -/
lemma InitialFailure.weakFailure {σ : ℕ → P} {p : P} (h : InitialFailure σ p) (m : ℕ) :
    WeakFailure m σ p :=
  ⟨0, h, by simp [contention, started, pre]⟩

lemma contention_le_card [Fintype P] (σ : ℕ → P) (t : ℕ) : contention σ t ≤ Fintype.card P :=
  Finset.card_le_univ _

/-- With `m ≥ |P|`, m-failures of type 1 are exactly the ordinary crash failures
("n-failures of type 1 are the traditional crash failures", §1.1). -/
lemma weakFailure_iff_faulty [Fintype P] {m : ℕ} (hm : Fintype.card P ≤ m) (σ : ℕ → P) (p : P) :
    WeakFailure m σ p ↔ p ∈ Faulty σ := by
  refine ⟨WeakFailure.faulty, fun h => ?_⟩
  obtain ⟨t, ht⟩ := exists_stoppedFrom_of_faulty h
  exact ⟨t, ht, le_trans (contention_le_card σ t) hm⟩

/-- If `p` crashes as an m-failure and has taken a step at a time when the contention exceeded
`m`, then ... contradiction: a process that has seen contention `> m` can no longer fail.
(Used for Lemma 1 and Lemma 7.) -/
lemma WeakFailure.contention_le_of_step {m : ℕ} {σ : ℕ → P} {p : P} (h : WeakFailure m σ p)
    {s : ℕ} (hs : σ s = p) : contention σ (s + 1) ≤ m := by
  obtain ⟨t, ht, hc⟩ := h
  have hst : s < t := by
    by_contra hcon
    exact ht s (Nat.le_of_not_lt hcon) hs
  exact le_trans (contention_mono σ hst) hc

end Podc.WeakCrashFailures
