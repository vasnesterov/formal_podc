import Podc.PartialSync.TwoStepLB

/-!
# `t`-two-step consensus protocols (Section 4.1 of Kuznetsov–Tonkikh–Zhang, PODC 2021)

We work in the shared partially synchronous model `Cslib.Byzantine.PartialSync` (discrete time, one step
per time unit, post-GST delay bound `δ`, ideal signatures via `Auth`). The paper's known delay bound
`Δ` is `δ` (we assume `0 < δ`), and *round `i`* is the time interval `[(i-1)δ, iδ)`.

* `weakValidity P V` (CSLib): if all processes are correct and propose `x`, only `x` may be decided.
* `tsRun A δ I T` (`Podc.PartialSync.TwoStepLB`): the **`T`-faulty two-step execution** starting
  from `I`: the processes of `T` are Byzantine, follow the protocol during the first round and are
  silent afterwards; every message sent in round `i` is delivered at the beginning of round `i + 1`
  (`nextRound`); `gst = 0`. In our model this execution is *unique* (simultaneous deliveries are
  processed in one step), so the paper's "there is a `T`-faulty two-step execution" becomes a
  property of `tsRun` (see `differencies.md`).
* `TwoStep A t δ`: for every `I` and every `T` with `|T| = t`, every correct process decides by
  time `2δ` (i.e. in its state after processing the messages delivered at time `2δ`, which is
  the state at time `2δ + 1`; `Run.DecidesBy`).
* `FastConsensus A Au f t δ`: `f`-resilient consensus with weak validity + `t`-two-step.

Generic tools (`quiet`, `nextRound`, `round1`, `templateRun` and the round-1 lemmas = Lemma 4.1)
live in `Cslib/Computability/Distributed/Byzantine/PartialSync/RoundOne.lean`; `tsRun` and the
executions `ρ₃`, `ρ₄` of Theorem 4.5 in `Podc/PartialSync/TwoStepLB.lean`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

variable (A : Algorithm P M S V V)

/-- A protocol is **`t`-two-step** (Section 4.1, condition (2)): for every initial configuration `I`
and every set `T` of `t` processes, in the `T`-faulty two-step execution every correct process
decides not later than at time `2Δ` (state at time `2δ + 1`). -/
def TwoStep (t δ : ℕ) : Prop :=
  ∀ (I : P → V) (T : Finset P), T.card = t → ∀ x ∉ T, ∃ v,
    (tsRun A δ I T).DecidesBy A x v (2 * δ + 1)

/-- An **`f`-resilient `t`-two-step consensus protocol** (with signatures `Au`): it solves consensus
with weak validity tolerating `f` Byzantine processes (post-GST delay bound `δ`), and is
`t`-two-step. -/
def FastConsensus (Au : Auth P M K) (f t δ : ℕ) : Prop :=
  SolvesConsensusAuth Au f δ A (weakValidity P V) ∧ TwoStep A t δ

end FastByzantineConsensus
