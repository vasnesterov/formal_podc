import Cslib.Computability.Distributed.Byzantine.PartialSync.RunClasses

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/PartialSync/Timeliness.lean

/-!
# Eventually timely channels, sinks, sources and bisources

Per-channel synchrony assumptions on runs of CSLib's partially synchronous model
(`Cslib.Byzantine.PartialSync`), in the style of Aguilera, Delporte-Gallet, Fauconnier and Toueg
(DSN 2006) and Bouzid, Mostéfaoui and Raynal (PODC 2015).

* `Run.EventuallyTimely R q p`: the channel `q → p` is eventually timely: there are a time `τ₀`
  and a bound `δ` (both unknown to the processes) such that every batch sent by `q` to `p` at
  time `τ` is delivered by `max τ τ₀ + δ`.
* `Run.IsSink R k ℓ` / `Run.IsSource R k ℓ`: the correct process `ℓ` has eventually timely input
  (resp. output) channels from (resp. to) a set of `k` correct processes including itself
  (an *eventual `⟨k⟩sink`* / *eventual `⟨k⟩source`*); `Run.IsBisource R k ℓ`: both (the two sets
  may differ).
* `Run.BisourceValid t k R`: the asynchronous runs (`Run.AsyncValid t`: at most `t` faults, no
  loss between correct processes, unbounded delays) that have an eventual `⟨k⟩bisource`.

A synchronous run has every correct process as a bisource (`Run.SyncValid.isBisource`), so
counterexamples built from synchronous runs are valid in every bisource model.
-/

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M VI : Type*} {t δ : ℕ}

namespace Run

/-- The channel `q → p` is *eventually timely*: from some time `τ₀` on, batches are delivered
within `δ` (`τ₀` and `δ` depend on the run and the channel). -/
def EventuallyTimely (R : Run P M VI) (q p : P) : Prop :=
  ∃ τ₀ δ : ℕ, ∀ τ, R.dl q τ p ≤ max τ τ₀ + δ

/-- `ℓ` is an *eventual `⟨k⟩sink`*: a correct process with eventually timely input channels from
a set of `k` correct processes that includes `ℓ` itself. -/
def IsSink (R : Run P M VI) (k : ℕ) (ℓ : P) : Prop :=
  ℓ ∉ R.faulty ∧ ∃ X : Finset P, ℓ ∈ X ∧ X.card = k ∧
    ∀ q ∈ X, q ∉ R.faulty ∧ R.EventuallyTimely q ℓ

/-- `ℓ` is an *eventual `⟨k⟩source`*: a correct process with eventually timely output channels to
a set of `k` correct processes that includes `ℓ` itself. -/
def IsSource (R : Run P M VI) (k : ℕ) (ℓ : P) : Prop :=
  ℓ ∉ R.faulty ∧ ∃ X : Finset P, ℓ ∈ X ∧ X.card = k ∧
    ∀ p ∈ X, p ∉ R.faulty ∧ R.EventuallyTimely ℓ p

/-- `ℓ` is an *eventual `⟨k⟩bisource`*: both an eventual `⟨k⟩sink` and an eventual
`⟨k⟩source` (the two sets of processes may differ). -/
def IsBisource (R : Run P M VI) (k : ℕ) (ℓ : P) : Prop := R.IsSink k ℓ ∧ R.IsSource k ℓ

/-- Asynchronous runs (at most `t` faults, reliable channels between correct processes,
unbounded delays) with an eventual `⟨k⟩bisource`. -/
def BisourceValid (t k : ℕ) (R : Run P M VI) : Prop := R.AsyncValid t ∧ ∃ ℓ, R.IsBisource k ℓ

variable {R : Run P M VI}

/-- In a synchronous run every channel between correct processes is eventually timely. -/
theorem SyncValid.eventuallyTimely (h : R.SyncValid t δ) {q p : P} (hq : q ∉ R.faulty)
    (hp : p ∉ R.faulty) : R.EventuallyTimely q p :=
  ⟨0, δ, fun τ => by
    have := h.1.dl_le q τ p hq hp
    rw [h.2] at this
    simpa using this⟩

/-- In a synchronous run every correct process is an eventual `⟨k⟩bisource`, for every `k` not
exceeding the number of correct processes. -/
theorem SyncValid.isBisource [Fintype P] [DecidableEq P] (h : R.SyncValid t δ) {ℓ : P}
    (hℓ : ℓ ∉ R.faulty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ (univ \ R.faulty).card) :
    R.IsBisource k ℓ := by
  have hmem : ℓ ∈ univ \ R.faulty := by simp [hℓ]
  obtain ⟨X, hXs, hℓX, hXc⟩ : ∃ X ⊆ univ \ R.faulty, ℓ ∈ X ∧ X.card = k := by
    obtain ⟨Y, hY, hYc⟩ := Finset.exists_subset_card_eq (s := (univ \ R.faulty).erase ℓ)
      (n := k - 1) (by rw [Finset.card_erase_of_mem hmem]; omega)
    refine ⟨insert ℓ Y, ?_, mem_insert_self _ _, ?_⟩
    · exact insert_subset hmem (hY.trans (erase_subset _ _))
    · rw [card_insert_of_notMem (fun h => by simpa using hY h), hYc]; omega
  have hX : ∀ q ∈ X, q ∉ R.faulty := fun q hq => by simpa using hXs hq
  exact ⟨⟨hℓ, X, hℓX, hXc, fun q hq => ⟨hX q hq, h.eventuallyTimely (hX q hq) hℓ⟩⟩,
    ⟨hℓ, X, hℓX, hXc, fun p hp => ⟨hX p hp, h.eventuallyTimely hℓ (hX p hp)⟩⟩⟩

/-- A synchronous run with a correct process is in every bisource model `BisourceValid t k`
with `1 ≤ k ≤` the number of correct processes. -/
theorem SyncValid.bisourceValid [Fintype P] [DecidableEq P] (h : R.SyncValid t δ) {ℓ : P}
    (hℓ : ℓ ∉ R.faulty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ (univ \ R.faulty).card) :
    R.BisourceValid t k :=
  ⟨h.asyncValid, ℓ, h.isBisource hℓ hk1 hk⟩

end Run

end Cslib.Byzantine.PartialSync
