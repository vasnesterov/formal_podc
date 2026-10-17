import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth
import Cslib.Computability.Distributed.Byzantine.PartialSync.RunClasses
import Mathlib

/-!
# Approximate agreement with synchronous and asynchronous guarantees (Ghinea–Liu-Zhang–Wattenhofer,
PODC 2022): the specification

We work in CSLib's Byzantine message-passing model `Cslib.Byzantine.PartialSync` (discrete time,
deterministic per-process state machines, the adversary chooses the Byzantine set, the Byzantine
messages, the GST and all delivery times) together with its abstract signature layer
(`Auth`, `Algorithm.Unforging`, `Run.AuthValid`). Inputs and outputs are real numbers.

* `Outputs A R p v`: the *first* decision of `p` in run `R` is `v` (the paper's parties output once
  and terminate; later decisions are ignored).
* `SecureAA Au A ε D C` (Definition 2.1 of the paper, for a fixed `ε`): on every run of the class `C`
  that respects unforgeability and has inputs in `D`, every honest party outputs (termination), every
  output lies in the range of the honest inputs (`t`-validity), and any two honest outputs are
  `ε`-close (`(t, ε)`-agreement).
* Run classes (the library classes of `Cslib.Computability.Distributed.Byzantine.PartialSync.RunClasses`): `syncRuns t δ` =
  `Run.SyncValid t δ` (at most `t` faults, `gst = 0`: every message between honest parties is
  delivered within `δ`; clocks are synchronised because all parties step every tick),
  `psyncRuns t δ` = `Run.Valid t δ` (the same bound only after an arbitrary GST) and `asyncRuns t` =
  `Run.AsyncValid t` (at most `t` faults, every message between honest parties is eventually
  delivered, **no bound**). `psyncRuns t δ ⊆ asyncRuns t`, so security on `asyncRuns` implies
  security on `psyncRuns` (`SecureAA.mono`).
-/

open Cslib.Byzantine.PartialSync Finset

namespace HybridApproxAgreement

set_option linter.unusedSectionVars false

variable {P M S K : Type*} [Fintype P] [DecidableEq P]

/-- The first decision of `p` in `R` is `v` (`p` outputs `v`). -/
def Outputs (A : Algorithm P M S ℝ ℝ) (R : Run P M ℝ) (p : P) (v : ℝ) : Prop :=
  ∃ τ, A.decide p (R.st A τ p) = some v ∧ ∀ σ < τ, A.decide p (R.st A σ p) = none

/-- `v` lies in the range `[min, max]` of the inputs of the honest parties of `R`. -/
def InHonestRange (R : Run P M ℝ) (v : ℝ) : Prop :=
  (∃ p ∉ R.faulty, R.inp p ≤ v) ∧ ∃ p ∉ R.faulty, v ≤ R.inp p

/-- **Definition 2.1** (for a fixed `ε`): `A` is a secure approximate-agreement protocol on the
class of runs `C`, for inputs in `D`, in the authenticated setting `Au`. -/
structure SecureAA (Au : Auth P M K) (A : Algorithm P M S ℝ ℝ) (ε : ℝ) (D : Set ℝ)
    (C : Run P M ℝ → Prop) : Prop where
  termination : ∀ R, C R → R.AuthValid Au A → (∀ p, R.inp p ∈ D) →
    ∀ p ∉ R.faulty, ∃ v, Outputs A R p v
  validity : ∀ R, C R → R.AuthValid Au A → (∀ p, R.inp p ∈ D) →
    ∀ p ∉ R.faulty, ∀ v, Outputs A R p v → InHonestRange R v
  agreement : ∀ R, C R → R.AuthValid Au A → (∀ p, R.inp p ∈ D) →
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, Outputs A R p v → Outputs A R q w → |v - w| ≤ ε

/-- Synchronous network: at most `t` corruptions, every message between honest parties is
delivered within `δ` ticks (`gst = 0`). -/
abbrev syncRuns (t δ : ℕ) (R : Run P M ℝ) : Prop := R.SyncValid t δ

/-- Partially synchronous network: delays bounded by `δ` after an arbitrary (unknown) GST. -/
abbrev psyncRuns (t δ : ℕ) (R : Run P M ℝ) : Prop := R.Valid t δ

/-- Asynchronous network: at most `t` corruptions, every message between honest parties is
delivered at some (finite, arbitrary) time — **unbounded** asynchrony `Run.AsyncValid t`. -/
abbrev asyncRuns (t : ℕ) (R : Run P M ℝ) : Prop := R.AsyncValid t

/-- Bridge to the explicit form: at most `t` corruptions and delivery at or after sending. -/
theorem asyncRuns_iff {t : ℕ} {R : Run P M ℝ} : asyncRuns t R ↔
    R.faulty.card ≤ t ∧ ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → τ ≤ R.dl q τ p :=
  ⟨fun h => ⟨h.card_faulty, h.dl_ge⟩, fun h => ⟨h.1, h.2⟩⟩

theorem psyncRuns_le_asyncRuns {t δ : ℕ} {R : Run P M ℝ} (h : psyncRuns t δ R) :
    asyncRuns t R :=
  h.asyncValid

/-- Security on a larger class of runs implies security on a smaller one. -/
theorem SecureAA.mono {Au : Auth P M K} {A : Algorithm P M S ℝ ℝ} {ε : ℝ} {D : Set ℝ}
    {C C' : Run P M ℝ → Prop} (h : SecureAA Au A ε D C) (hC : ∀ R, C' R → C R) :
    SecureAA Au A ε D C' :=
  ⟨fun R hR => h.termination R (hC R hR), fun R hR => h.validity R (hC R hR),
    fun R hR => h.agreement R (hC R hR)⟩

/-- Hybrid AA is solvable for `n = |P|` parties with thresholds `ts` (synchronous network with
delay bound `δ`) and `ta` (asynchronous network), for agreement parameter `ε` and inputs in `D`:
some unforging protocol (any message, state and signature types) is secure in both networks. -/
def HybridAASolvable (P : Type*) [Fintype P] [DecidableEq P] (ε : ℝ) (D : Set ℝ)
    (ts ta δ : ℕ) : Prop :=
  ∃ (M S K : Type) (Au : Auth P M K) (A : Algorithm P M S ℝ ℝ), A.Unforging Au ∧
    SecureAA Au A ε D (syncRuns ts δ) ∧ SecureAA Au A ε D (asyncRuns ta)

/-! ### Basic facts -/

/-- If two runs give `p` the same states up to `T` and `p` outputs `v` by time `T` in one of them,
it outputs `v` in the other. -/
theorem Outputs.of_st_eq {A : Algorithm P M S ℝ ℝ} {R R' : Run P M ℝ} {p : P} {v : ℝ} {T : ℕ}
    (h : Outputs A R' p v) (hT : ∃ τ ≤ T, A.decide p (R'.st A τ p) = some v)
    (hst : ∀ τ ≤ T, R.st A τ p = R'.st A τ p) : Outputs A R p v := by
  obtain ⟨τ, hτ, hfirst⟩ := h
  obtain ⟨τ', hτ'T, hτ'⟩ := hT
  have hle : τ ≤ τ' := by
    by_contra hlt
    have := hfirst τ' (by omega)
    rw [hτ'] at this
    exact absurd this (by simp)
  refine ⟨τ, by rw [hst τ (by omega)]; exact hτ, fun σ hσ => ?_⟩
  rw [hst σ (by omega)]; exact hfirst σ hσ

/-- An output is attained at some time. -/
theorem Outputs.exists_time {A : Algorithm P M S ℝ ℝ} {R : Run P M ℝ} {p : P} {v : ℝ}
    (h : Outputs A R p v) : ∃ τ, A.decide p (R.st A τ p) = some v :=
  let ⟨τ, hτ, _⟩ := h; ⟨τ, hτ⟩

/-- If all honest parties have input `x`, the only value in the honest range is `x`. -/
theorem InHonestRange.eq_of_const {R : Run P M ℝ} {v x : ℝ} (h : InHonestRange R v)
    (hx : ∀ p ∉ R.faulty, R.inp p = x) : v = x := by
  obtain ⟨⟨p, hp, h1⟩, ⟨q, hq, h2⟩⟩ := h
  rw [hx p hp] at h1; rw [hx q hq] at h2
  linarith

end HybridApproxAgreement
