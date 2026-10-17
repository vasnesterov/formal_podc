import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundOne
import Podc.PartialSync.RunClasses

/-!
# Byzantine broadcast specifications and good-case latency

Abraham, Nayak, Ren, Xiang, *Good-case Latency of Byzantine Broadcast: a Complete
Categorization*, PODC 2021 (arXiv:2102.07240v3), Section 2.

We work in the shared Byzantine message-passing model `Cslib.Byzantine.PartialSync`
(discrete time, deterministic state machines, the adversary chooses the Byzantine processes,
their messages and all delivery times; ideal signatures via `Auth`).

## Time conventions

* **Synchrony (Section 5).** A batch sent at time `τ` and delivered at `dl` is processed in the
  step at `dl`, so it is visible in the state at time `dl + 1`. We call `dl + 1 - τ` its
  *effective delay*; the state at time `t` is the paper's local history at time `t` (it reflects
  all messages received at times `≤ t`, and a process reacts to a message at the same time it
  receives it). A *synchronous run with delay bound `d`* (`SyncValid f d`) has at most `f`
  Byzantine processes and effective delays in `[1, d]` between correct processes (the paper also
  allows delay `0`; forbidding it only weakens the adversary, which makes lower bounds stronger).
  "Commits before time `T`" is `CommitsBy A R p (T - 1)`.
* **Partial synchrony (Section 4).** We use the CSLib model verbatim (`Run.Valid f D`: delays
  `dl - τ ∈ [0, max τ gst + D - τ]`). Rounds have length `D`; in the lock-step schedule round-`r`
  messages are delivered at time `r * D`, so "commits within `R` rounds" is `CommitsBy … (R * D + 1)`
  (as in the formalization of Kuznetsov–Tonkikh–Zhang, PODC 2021).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K VI : Type*} [DecidableEq P]

/-- `p` has committed some value by time `τ₀` (in its state at some time `≤ τ₀`). -/
def CommitsBy (A : Algorithm P M S VI V) (R : Run P M VI) (p : P) (τ₀ : ℕ) : Prop :=
  ∃ v, R.DecidesBy A p v τ₀

theorem CommitsBy.decides {A : Algorithm P M S VI V} {R : Run P M VI} {p : P} {τ₀ : ℕ}
    (h : CommitsBy A R p τ₀) : ∃ v, R.Decides A p v := by
  obtain ⟨v, τ, -, hτ⟩ := h; exact ⟨v, τ, hτ⟩

/-- A **synchronous run with (effective) delay bound `d`**: at most `f` Byzantine processes, and
every batch between correct processes sent at `τ` is processed by time `τ + d` (i.e. delivered at
a time in `[τ, τ + d - 1]`). The GST is irrelevant. This is the library's `Run.SyncValid f (d - 1)`
up to the GST (`syncValid_iff`), not the library notion itself. -/
structure SyncValid (f d : ℕ) (R : Run P M V) : Prop where
  card_faulty : R.faulty.card ≤ f
  dl_ge : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → τ ≤ R.dl q τ p
  dl_lt : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → R.dl q τ p < τ + d

theorem SyncValid.mono {f d d' : ℕ} {R : Run P M V} (h : SyncValid f d R) (hd : d ≤ d') :
    SyncValid f d' R :=
  ⟨h.card_faulty, h.dl_ge, fun q τ p hq hp => (h.dl_lt q τ p hq hp).trans_le (by omega)⟩

/-- A synchronous run is in particular a partially synchronous run (with any GST). -/
theorem SyncValid.valid {f d : ℕ} {R : Run P M V} (h : SyncValid f d R) : R.Valid f (d - 1) where
  card_faulty := h.card_faulty
  dl_ge := h.dl_ge
  dl_le q τ p hq hp := by
    have := h.dl_lt q τ p hq hp
    have := le_max_left τ R.gst
    omega

/-- Bridge to the library's synchronous runs (`Run.Valid` with `gst = 0`): with `gst = 0`,
effective delay bound `δ + 1` is delay bound `δ`. -/
theorem syncValid_iff {f δ : ℕ} {R : Run P M V} (h0 : R.gst = 0) :
    SyncValid f (δ + 1) R ↔ R.SyncValid f δ := by
  rw [Run.syncValid_iff_dl_le]
  constructor
  · intro h
    exact ⟨h.card_faulty, fun q τ p hq hp => ⟨h.dl_ge q τ p hq hp, by
      have := h.dl_lt q τ p hq hp; omega⟩, h0⟩
  · rintro ⟨hc, hdl, -⟩
    exact ⟨hc, fun q τ p hq hp => (hdl q τ p hq hp).1, fun q τ p hq hp => by
      have := (hdl q τ p hq hp).2; omega⟩

/-- A library-synchronous run with delay bound `δ` is synchronous with effective delay bound
`δ + 1`. -/
theorem SyncValid.of_syncValid {f δ : ℕ} {R : Run P M V} (h : R.SyncValid f δ) :
    SyncValid f (δ + 1) R :=
  (syncValid_iff h.gst_eq).2 h

/-! ### Broadcast specifications (Definitions 2–4) -/

section specs

variable (Au : Auth P M K) (A : Algorithm P M S V V) (s : P)

/-- **Byzantine reliable broadcast** (Definition 3) with designated broadcaster `s` (its input
is `R.inp s`; the inputs of the other processes are irrelevant), required in every admissible run
(`Adm`) whose adversary respects unforgeability. -/
structure IsBRB (Adm : Set (Run P M V)) : Prop where
  /-- Agreement. -/
  agreement : ∀ R ∈ Adm, R.AuthValid Au A → ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w,
    R.Decides A p v → R.Decides A q w → v = w
  /-- Validity: if the broadcaster is honest, all honest processes commit its value. -/
  validity : ∀ R ∈ Adm, R.AuthValid Au A → s ∉ R.faulty → ∀ p ∉ R.faulty, R.Decides A p (R.inp s)
  /-- Termination (reliable broadcast): if some honest process commits, all do. -/
  termination : ∀ R ∈ Adm, R.AuthValid Au A → (∃ p ∉ R.faulty, ∃ v, R.Decides A p v) →
    ∀ p ∉ R.faulty, ∃ v, R.Decides A p v

/-- **Byzantine broadcast** (Definition 2): BRB with unconditional termination. -/
structure IsBB (Adm : Set (Run P M V)) : Prop extends IsBRB Au A s Adm where
  /-- Termination. -/
  termination' : ∀ R ∈ Adm, R.AuthValid Au A → ∀ p ∉ R.faulty, ∃ v, R.Decides A p v

/-- **Partially synchronous Byzantine broadcast** (Definition 4), with at most `f` faults and
post-GST delay bound `D` (CSLib convention). -/
structure IsPsyncBB (f D : ℕ) : Prop where
  /-- Agreement. -/
  agreement : ∀ R : Run P M V, R.Valid f D → R.AuthValid Au A → ∀ p ∉ R.faulty, ∀ q ∉ R.faulty,
    ∀ v w, R.Decides A p v → R.Decides A q w → v = w
  /-- Validity: honest broadcaster and `GST = 0`. -/
  validity : ∀ R : Run P M V, R.Valid f D → R.AuthValid Au A → R.gst = 0 → s ∉ R.faulty →
    ∀ p ∉ R.faulty, R.Decides A p (R.inp s)
  /-- Termination. -/
  termination : ∀ R : Run P M V, R.Valid f D → R.AuthValid Au A → ∀ p ∉ R.faulty,
    ∃ v, R.Decides A p v

end specs

/-- Every honest process commits by time `T` in every admissible run with an honest broadcaster
whose adversary respects unforgeability. -/
def LatencyWithin (Au : Auth P M K) (A : Algorithm P M S VI V) (s : P) (Adm : Set (Run P M VI))
    (T : ℕ) : Prop :=
  ∀ R ∈ Adm, R.AuthValid Au A → s ∉ R.faulty → ∀ p ∉ R.faulty, CommitsBy A R p T

/-! ### Admissible runs -/

/-- Synchronous runs with at most `f` faults and (effective) delay bound `d`. -/
def syncRuns (f d : ℕ) : Set (Run P M V) := {R | SyncValid f d R}

/-- Asynchronous runs: every run of the model (any GST, any delay bound): **bounded** asynchrony
`Run.AsyncValidBounded f`, i.e. `∃ D, R.Valid f D` (not the unbounded `Run.AsyncValid f`). -/
def asyncRuns (f : ℕ) : Set (Run P M V) := {R | R.AsyncValidBounded f}

/-- Partially synchronous runs with `GST = 0` (the good case of Definition 7), i.e. the library's
synchronous runs `Run.SyncValid f D` (`R.Valid f D ∧ R.gst = 0`). -/
def psyncGoodRuns (f D : ℕ) : Set (Run P M V) := {R | R.SyncValid f D}

/-- **Good-case latency of `r` rounds under partial synchrony** (Definition 7): if the broadcaster
is honest and `GST = 0`, every honest process commits within `r` rounds of length `D`. -/
def PsyncGoodCaseRounds (Au : Auth P M K) (A : Algorithm P M S V V) (s : P) (f D r : ℕ) : Prop :=
  LatencyWithin Au A s (psyncGoodRuns f D) (r * D + 1)

/-- Self-agreement: a decision by a deadline has the value forced by validity. -/
theorem CommitsBy.eq_of_agreement {A : Algorithm P M S VI V} {R : Run P M VI} {p : P} {τ₀ : ℕ}
    {v : V} (hag : ∀ w, R.Decides A p w → R.Decides A p v → w = v) (h : CommitsBy A R p τ₀)
    (hv : R.Decides A p v) : ∃ τ ≤ τ₀, A.decide p (R.st A τ p) = some v := by
  obtain ⟨w, τ, hτ, hd⟩ := h
  obtain rfl := hag w ⟨τ, hd⟩ hv
  exact ⟨τ, hτ, hd⟩

end GoodCaseLatencyBB
