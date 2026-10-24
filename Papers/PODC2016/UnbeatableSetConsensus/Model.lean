import Cslib.Computability.Distributed.SyncCrash.Model
import Cslib.Computability.Distributed.DynamicNetworks.FullInfo
import Mathlib

/-!
# The model of Castañeda–Gonczarowski–Moses, *Unbeatable Set Consensus* (PODC 2016)

Synchronous message passing with crash failures (§2.1 of the paper):

* processes `P` (a `Fintype`), a complete network, rounds; round `t + 1` takes place between time
  `t` and time `t + 1`;
* an **adversary** (a run) is CSLib's `Cslib.SyncCrash.Run P ℕ`: input vector (natural numbers),
  crash round `crash p = some c` (`c ≥ 1`) and the set `reach p` of processes that still get `p`'s
  round-`c` message; `r.Deliv q p t` says that a message of `q` in round `t + 1` reaches `p`;
* protocols are **full-information protocols**: every process sends its whole view to everybody
  in every round, so the communication graph `comm r t q p` (`p` receives `q`'s message of round
  `t + 1`) depends on the adversary only, and protocols differ only in their decision rule
  (`Protocol`): a function of the view, i.e. invariant under `SameView`;
* the view of `⟨i, m⟩` is the full-information view `G_α(i, m)`; "same view" is CSLib's
  `Cslib.HeardOf.FIIndist` for the communication graph `comm r`.

The notions of §3–4 (seen, guaranteed crashed, hidden nodes, hidden capacity `HC⟨i, m⟩`,
`Vals⟨i, m⟩`, `Min⟨i, m⟩`, low/high), the problem (nonuniform `k`-set consensus with inputs in a
set `D ⊆ ℕ`) and the comparison notions of §2.2 and Appendix D (domination, unbeatability,
last-decider domination and unbeatability) are defined here; basic lemmas about views are in
`Views.lean`.
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Cslib.DynNet Cslib.HeardOf Finset

/-- An adversary `α = (v⃗, F)` (equivalently, the run of a full-information protocol): inputs and
crash pattern. -/
abbrev Run (P : Type*) := Cslib.SyncCrash.Run P ℕ

variable {P : Type*}

/-- The communication graph of the full-information protocol: `comm r t q p` iff `p` receives the
message that `q` sends in round `t + 1` (sent at time `t`). There are no self-messages. -/
def comm (r : Run P) (t : ℕ) (q p : P) : Prop := q ≠ p ∧ r.Deliv q p t

/-- `⟨j, ℓ⟩` **is seen by** `⟨i, m⟩`: there is a (Lamport) message chain from `⟨j, ℓ⟩` to
`⟨i, m⟩`, i.e. `⟨j, ℓ⟩` is a node of the view `G_α(i, m)`. -/
def Seen (r : Run P) (j : P) (ℓ : ℕ) (i : P) (m : ℕ) : Prop := Journey (comm r) ℓ j m i

/-- `⟨j, ℓ⟩` **is guaranteed crashed** at `⟨i, m⟩`: `i` has proof at time `m` that `j` crashed
before time `ℓ`, i.e. `⟨i, m⟩` has seen a node `⟨h, s + 1⟩` (`s + 1 ≤ ℓ`) such that `h` did not
receive `j`'s message of round `s + 1`. -/
def GuarCrashed (r : Run P) (i : P) (m : ℕ) (j : P) (ℓ : ℕ) : Prop :=
  ∃ h s, s < ℓ ∧ Seen r h (s + 1) i m ∧ h ≠ j ∧ ¬ r.Deliv j h s

/-- `⟨j, ℓ⟩` **is hidden from** `⟨i, m⟩`: neither seen by `⟨i, m⟩` nor guaranteed crashed there. -/
def Hidden (r : Run P) (i : P) (m : ℕ) (j : P) (ℓ : ℕ) : Prop :=
  ¬ Seen r j ℓ i m ∧ ¬ GuarCrashed r i m j ℓ

/-- Two adversaries give `i` the same view at time `m` (`r_i(m) = r'_i(m)` for full-information
protocols). -/
def SameView (r r' : Run P) (i : P) (m : ℕ) : Prop :=
  FIIndist (fun q => r.input q = r'.input q) (comm r) (comm r') m i

variable [Fintype P]

/-- The processes `j` such that `⟨j, ℓ⟩` is hidden from `⟨i, m⟩`. -/
noncomputable def hiddenAt (r : Run P) (i : P) (m ℓ : ℕ) : Finset P := by
  classical exact univ.filter (fun j => Hidden r i m j ℓ)

/-- **Definition 2.** The hidden capacity `HC⟨i, m⟩`: the largest `c` such that at every time
`ℓ ≤ m` at least `c` nodes are hidden from `⟨i, m⟩`. -/
noncomputable def hc (r : Run P) (i : P) (m : ℕ) : ℕ :=
  (range (m + 1)).inf' nonempty_range_add_one (fun ℓ => (hiddenAt r i m ℓ).card)

/-- `Vals⟨i, m⟩`: the initial values seen by `⟨i, m⟩` (the values `v` with `K_i ∃v`). -/
noncomputable def vals (r : Run P) (i : P) (m : ℕ) : Finset ℕ := by
  classical exact (univ.filter (fun j => Seen r j 0 i m)).image r.input

lemma vals_nonempty (r : Run P) (i : P) (m : ℕ) : (vals r i m).Nonempty := by
  classical
  refine ⟨r.input i, ?_⟩
  simp only [vals, mem_image, mem_filter, mem_univ, true_and]
  exact ⟨i, Journey.self (Nat.zero_le m), rfl⟩

/-- `Min⟨i, m⟩`: the minimal value seen by `⟨i, m⟩`. -/
noncomputable def minVal (r : Run P) (i : P) (m : ℕ) : ℕ := (vals r i m).min' (vals_nonempty r i m)

/-- `Lows⟨i, m⟩ = Vals⟨i, m⟩ ∩ {0, …, k - 1}`. -/
noncomputable def lows (k : ℕ) (r : Run P) (i : P) (m : ℕ) : Finset ℕ :=
  (vals r i m).filter (· < k)

/-- `i` is **low** at time `m`: it has seen a value `< k` (`Min⟨i, m⟩ < k`). Otherwise it is
*high*. -/
def Low (k : ℕ) (r : Run P) (i : P) (m : ℕ) : Prop := ∃ v ∈ vals r i m, v < k

/-! ### Protocols and the problem -/

/-- A decision protocol in the full-information setting: a decision rule `dec r i m` (the value
`i` decides on at `⟨i, m⟩` if it has not decided before, `none` = no decision) that depends only
on the view of `⟨i, m⟩`. Every deterministic protocol gives such a rule (`LockStep.lean`). -/
structure Protocol (P : Type*) where
  /-- The decision rule. -/
  dec : Run P → P → ℕ → Option ℕ
  /-- The rule is a function of the local state (the view). -/
  dec_congr : ∀ r r' i m, SameView r r' i m → dec r i m = dec r' i m

/-- `i` decides `v` at time `m` in the run `Q[α]`: `i` is alive at `m`, the rule fires at `m` with
value `v`, and it did not fire before (decisions are irrevocable). -/
def DecidesAt (Q : Protocol P) (r : Run P) (i : P) (m v : ℕ) : Prop :=
  r.Alive i m ∧ Q.dec r i m = some v ∧ ∀ m' < m, Q.dec r i m' = none

/-- `i` has decided by time `m`. -/
def DecidesBy (Q : Protocol P) (r : Run P) (i : P) (m : ℕ) : Prop :=
  ∃ m' ≤ m, ∃ v, DecidesAt Q r i m' v

/-- The context `γ = (D^n, Crash(t))`: at most `t` crashes, inputs in `D`. -/
def Adm (t : ℕ) (D : Set ℕ) (r : Run P) : Prop := r.Admissible t ∧ ∀ p, r.input p ∈ D

/-- **Nonuniform `k`-set consensus** (§2.3): Decision (every correct process decides), Validity
(only values that are some input are decided) and `k`-Agreement (correct processes decide at most
`k` distinct values), in every run of the context. -/
structure SolvesSetConsensus (k t : ℕ) (D : Set ℕ) (Q : Protocol P) : Prop where
  decision : ∀ r, Adm t D r → ∀ i, ¬ r.Faulty i → ∃ m v, DecidesAt Q r i m v
  validity : ∀ r, Adm t D r → ∀ i m v, DecidesAt Q r i m v → ∃ j, r.input j = v
  agreement : ∀ r, Adm t D r → {v | ∃ i m, ¬ r.Faulty i ∧ DecidesAt Q r i m v}.encard ≤ k

/-- `Q ⪰_γ P'` (§2.2): in every run, every process that decides in `P'` decides in `Q` no later. -/
def Dominates (t : ℕ) (D : Set ℕ) (Q P' : Protocol P) : Prop :=
  ∀ r, Adm t D r → ∀ i m v, DecidesAt P' r i m v → DecidesBy Q r i m

/-- **Definition 1** (unbeatability): `P'` solves the problem and no solution strictly dominates it,
i.e. every solution `Q` with `Q ⪰ P'` satisfies `P' ⪰ Q`. -/
def Unbeatable (k t : ℕ) (D : Set ℕ) (P' : Protocol P) : Prop :=
  SolvesSetConsensus k t D P' ∧
    ∀ Q, SolvesSetConsensus k t D Q → Dominates t D Q P' → Dominates t D P' Q

/-- **Definition 6** (last-decider domination): whenever all correct processes have decided by
time `m` in `P'`, they have all decided by time `m` in `Q`. -/
def LDDominates (t : ℕ) (D : Set ℕ) (Q P' : Protocol P) : Prop :=
  ∀ r, Adm t D r → ∀ m, (∀ i, ¬ r.Faulty i → DecidesBy P' r i m) →
    ∀ i, ¬ r.Faulty i → DecidesBy Q r i m

/-- **Definition 6** (last-decider unbeatability). -/
def LDUnbeatable (k t : ℕ) (D : Set ℕ) (P' : Protocol P) : Prop :=
  SolvesSetConsensus k t D P' ∧
    ∀ Q, SolvesSetConsensus k t D Q → LDDominates t D Q P' → LDDominates t D P' Q

end Podc.UnbeatableSetConsensus
