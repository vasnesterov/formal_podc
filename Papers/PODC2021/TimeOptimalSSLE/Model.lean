import Cslib.Computability.Distributed.PopulationProtocols.Nondet
import Podc.Computability.Distributed.PopulationProtocols.Nondet
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Population protocols with randomized transitions: model and problem statements

Burman, Chen, Chen, Doty, Nowak, Severson, Xu, *Time-Optimal Self-Stabilizing Leader Election in
Population Protocols*, PODC 2021 (arXiv:1907.06068v5), Section 2.

The paper allows *probabilistic* transitions `T : S × S → Dist(S × S)`. All statements we formalize
about self-stabilization "with probability 1" only depend on the **support** of the transition
distributions (finite state space, uniformly random ordered pair; see `RandomScheduler.lean` for the
Markov-chain bridge). We therefore model a protocol by its support relation `δ p q ⊆ Q × Q`
(`NProtocol`, the shared model `Cslib.PopulationProtocol.NProtocol` of
`Cslib.Computability.Distributed.PopulationProtocols.Nondet`). Deterministic CSLib protocols embed via `NProtocol.ofProtocol`.

* `NProtocol.Step`, `NProtocol.Reachable`: one interaction of an ordered pair of distinct agents
  (the complete interaction graph).
* `NProtocol.StablyCorrect good C`: every configuration reachable from `C` is `good`
  (`Cslib.TransitionSystem.StablyIn`).
* `NProtocol.SelfStabilizes good`: from every configuration a stably correct one is reachable
  (`Cslib.TransitionSystem.SelfStabilizes`). For a finite state space and the uniform random
  scheduler this is *equivalent* to "from every configuration a stably correct configuration is
  reached with probability 1" (`RandomScheduler.lean`).
* `SolvesSSLE` (one agent with `leader = true`), `SolvesSSR` (ranks form a bijection onto
  `Fin n`).
* Sub-population runs (`StepIn`/`ReachIn`), silence (`Silent`) and the embedding of a run of a
  sub-population (`exists_reachIn_of_embedding`) are the shared notions of
  `Podc.Computability.Distributed.PopulationProtocols.Nondet`.
-/

open Cslib.PopulationProtocol Cslib.TransitionSystem

namespace TimeOptimalSSLE

/-- A population protocol whose transitions may be randomized: `δ p q` is the support of the
distribution of the new states `(initiator, responder)` when an initiator in state `p` meets a
responder in state `q`. -/
abbrev NProtocol := Cslib.PopulationProtocol.NProtocol

namespace NProtocol

export Cslib.PopulationProtocol (upd upd_left upd_right upd_other numLeaders)

variable {Q A : Type*} [DecidableEq A] (P : NProtocol Q)

/-- A state predicate / set of configurations is *stably correct* from `C` if all configurations
reachable from `C` satisfy it. -/
abbrev StablyCorrect (good : Config A Q → Prop) (C : Config A Q) : Prop :=
  StablyIn P.Step good C

/-- Self-stabilization (in the "probability 1" sense, see `RandomScheduler.lean`): from every
configuration, some stably correct configuration is reachable. -/
abbrev SelfStabilizes (good : Config A Q → Prop) : Prop :=
  Cslib.TransitionSystem.SelfStabilizes P.Step good

/-- Correct configurations for leader election: exactly one leader. -/
def LeaderCorrect [Fintype A] (leader : Q → Bool) (C : Config A Q) : Prop :=
  numLeaders leader C = 1

/-- Self-stabilizing leader election (SSLE) on the population `A`. -/
def SolvesSSLE [Fintype A] (leader : Q → Bool) : Prop :=
  P.SelfStabilizes (A := A) (LeaderCorrect leader)

/-- Correct configurations for ranking: the ranks form a bijection onto `Fin n`. -/
def RankCorrect {n : ℕ} (rank : Q → Fin n) (C : Config A Q) : Prop :=
  Function.Bijective fun a => rank (C a)

/-- Self-stabilizing ranking (SSR) on the population `A`, with output map `rank`. -/
def SolvesSSR {n : ℕ} (rank : Q → Fin n) : Prop :=
  P.SelfStabilizes (A := A) (RankCorrect rank)

/-! ### Deterministic protocols -/

/-- A deterministic CSLib population protocol as a protocol with (trivially) randomized
transitions. -/
abbrev ofProtocol (P : Protocol Q) : NProtocol Q := P.toN

lemma ofProtocol_step_iff (P : Protocol Q) (C D : Config A Q) :
    (ofProtocol P).Step C D ↔ P.Step C D :=
  Protocol.toN_step_iff

lemma ofProtocol_reachable_iff (P : Protocol Q) (C D : Config A Q) :
    (ofProtocol P).Reachable C D ↔ P.Reachable C D :=
  Protocol.toN_reachable_iff

end NProtocol

end TimeOptimalSSLE
