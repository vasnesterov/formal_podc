import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundOne

/-!
# `t`-two-step consensus protocols (Section 4.1 of Kuznetsov–Tonkikh–Zhang, PODC 2021)

We work in the shared partially synchronous model `Cslib.Byzantine.PartialSync` (discrete time, one step
per time unit, post-GST delay bound `δ`, ideal signatures via `Auth`). The paper's known delay bound
`Δ` is `δ` (we assume `0 < δ`), and *round `i`* is the time interval `[(i-1)δ, iδ)`.

* `weakValidity`: if all processes are correct and propose `x`, only `x` may be decided.
* `tsRun A δ I T`: the **`T`-faulty two-step execution** starting from `I`: the processes of `T`
  are Byzantine, follow the protocol during the first round and are silent afterwards; every
  message sent in round `i` is delivered at the beginning of round `i + 1` (`nextRound`);
  `gst = 0`. In our model this execution is *unique* (simultaneous deliveries are processed in
  one step), so the paper's "there is a `T`-faulty two-step execution" becomes a property of
  `tsRun` (see `differencies.md`).
* `TwoStep A t δ`: for every `I` and every `T` with `|T| = t`, every correct process decides by
  time `2δ` (i.e. in its state after processing the messages delivered at time `2δ`, which is
  the state at time `2δ + 1`).
* `FastConsensus A Au f t δ`: `f`-resilient consensus with weak validity + `t`-two-step.

Generic tools (`quiet`, `nextRound`, `round1`, `templateRun` and the round-1 lemmas = Lemma 4.1)
live in `Cslib/Computability/Distributed/Byzantine/PartialSync/RoundOne.lean`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

/-- **Weak validity** (Section 2.2): if all processes are correct and propose the same value `x`,
then only `x` can be decided. -/
def weakValidity : ValidityProperty P V V := fun c => {w | ∀ x, (∀ p, c p = some x) → w = x}

variable (A : Algorithm P M S V V)

/-- The **`T`-faulty two-step execution** starting from `I` (Section 4.1), with rounds of length
`D` (= `δ`): the processes in `T` are Byzantine, follow the protocol during the first round and
then stop; every message sent in a round is delivered at the beginning of the next round. -/
def tsRun (D : ℕ) (I : P → V) (T : Finset P) : Run P M V where
  faulty := T
  inp := I
  gst := 0
  byz q τ x := if τ < D then A.send q (quiet A q (I q) τ) x else []
  dl _ τ _ := nextRound D τ

/-- `x` decides `v` at some time `≤ τ₀`. -/
def DecidesBy (R : Run P M V) (x : P) (v : V) (τ₀ : ℕ) : Prop :=
  ∃ τ ≤ τ₀, A.decide x (R.st A τ x) = some v

/-- A protocol is **`t`-two-step** (Section 4.1, condition (2)): for every initial configuration `I`
and every set `T` of `t` processes, in the `T`-faulty two-step execution every correct process
decides not later than at time `2Δ` (state at time `2δ + 1`). -/
def TwoStep (t δ : ℕ) : Prop :=
  ∀ (I : P → V) (T : Finset P), T.card = t → ∀ x ∉ T, ∃ v, DecidesBy A (tsRun A δ I T) x v (2 * δ + 1)

/-- An **`f`-resilient `t`-two-step consensus protocol** (with signatures `Au`): it solves consensus
with weak validity tolerating `f` Byzantine processes (post-GST delay bound `δ`), and is
`t`-two-step. -/
def FastConsensus (Au : Auth P M K) (f t δ : ℕ) : Prop :=
  SolvesConsensusAuth Au f δ A weakValidity ∧ TwoStep A t δ

/-! ### Basic facts -/

theorem tsRun_eq (D : ℕ) (I : P → V) (T : Finset P) :
    tsRun (M := M) A D I T = templateRun A D T I 0 (fun q _ => some (I q)) (fun _ _ _ => [])
      (fun _ τ _ => nextRound D τ) := rfl

theorem tsRun_valid {f δ : ℕ} (hδ : 0 < δ) (I : P → V) {T : Finset P} (hT : T.card ≤ f) :
    (tsRun (M := M) A δ I T).Valid f δ where
  card_faulty := hT
  dl_ge _ _ _ _ _ := (le_nextRound hδ).le
  dl_le _ _ _ _ _ := nextRound_le.trans (by simp [tsRun])

theorem tsRun_authValid {Au : Auth P M K} (hU : A.Unforging Au) (D : ℕ) (I : P → V)
    (T : Finset P) : (tsRun (M := M) A D I T).AuthValid Au A := by
  intro b hb τ r _ m hm k hk
  simp only [tsRun] at hm
  split_ifs at hm
  · left; rw [quiet_tokens A hU hm hk]; exact hb
  · simp at hm

end FastByzantineConsensus