import Podc.PopulationProtocols.Nondet
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
`Podc.PopulationProtocols.Nondet`). Deterministic CSLib protocols embed via `NProtocol.ofProtocol`.

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
* Sub-population runs: `NProtocol.reachable_embed` (a run of a sub-population embeds into the
  whole population, the other agents being idle).
-/

open Cslib.PopulationProtocol Cslib.TransitionSystem
open Cslib.PopulationProtocol.NProtocol (reach_stepOn_mono reach_stepOn_apply_eq)

namespace TimeOptimalSSLE

/-- A population protocol whose transitions may be randomized: `δ p q` is the support of the
distribution of the new states `(initiator, responder)` when an initiator in state `p` meets a
responder in state `q`. -/
abbrev NProtocol := Cslib.PopulationProtocol.NProtocol

namespace NProtocol

export Cslib.PopulationProtocol (upd upd_left upd_right upd_other numLeaders)

variable {Q A : Type*} [DecidableEq A] (P : NProtocol Q)

/-- One interaction of two distinct agents, restricted to agents satisfying `S`. -/
abbrev StepIn (S : A → Prop) : Config A Q → Config A Q → Prop :=
  P.StepOn fun a b => S a ∧ S b ∧ a ≠ b

/-- Reachability inside the sub-population `S` (the other agents are idle). -/
abbrev ReachIn (S : A → Prop) : Config A Q → Config A Q → Prop := Reach (P.StepIn S)

lemma ReachIn.reachable {S : A → Prop} {C D : Config A Q} (h : P.ReachIn S C D) :
    P.Reachable C D :=
  reach_stepOn_mono (fun _ _ h => h.2.2) h

lemma ReachIn.mono {S S' : A → Prop} (hS : ∀ x, S x → S' x) {C D : Config A Q}
    (h : P.ReachIn S C D) : P.ReachIn S' C D :=
  reach_stepOn_mono (fun a b h => ⟨hS a h.1, hS b h.2.1, h.2.2⟩) h

/-- Agents outside the sub-population keep their states. -/
lemma ReachIn.eq_of_not_mem {S : A → Prop} {C D : Config A Q} (h : P.ReachIn S C D) {x : A}
    (hx : ¬ S x) : D x = C x :=
  reach_stepOn_apply_eq (fun _ => ⟨fun h => hx h.1, fun h => hx h.2.1⟩) h

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

/-- A configuration is silent if every enabled interaction leaves both states unchanged. -/
def Silent (C : Config A Q) : Prop :=
  ∀ a b, a ≠ b → ∀ o ∈ P.δ (C a) (C b), o = (C a, C b)

/-- Silence of the protocol is silence of its step relation. -/
lemma silent_iff_isSilent {C : Config A Q} : P.Silent C ↔ IsSilent P.Step C := by
  constructor
  · rintro hC D ⟨a, b, hab, o, ho, rfl⟩
    rw [hC a b hab o ho, upd_self _ hab]
  · intro hC a b hab o ho
    have h := hC _ ⟨a, b, hab, o, ho, rfl⟩
    rw [← congrFun h a, ← congrFun h b, upd_left _ hab, upd_right]

lemma Silent.reachable_eq {C : Config A Q} {D : Config A Q} (hC : P.Silent C)
    (h : P.Reachable C D) : D = C :=
  ((silent_iff_isSilent P).1 hC).reach_eq h

/-- A silent correct configuration is stably correct. -/
lemma Silent.stablyCorrect {good : Config A Q → Prop} {C : Config A Q} (hC : P.Silent C)
    (hg : good C) : P.StablyCorrect good C :=
  ((silent_iff_isSilent P).1 hC).stablyIn hg

/-! ### Sub-populations -/

/-- **Embedding a run of a sub-population.** If `e : A' ↪ A` and the population `A'` can go
from `C ∘ e` to `D'`, then the population `A` can go from `C` to a configuration that agrees
with `D'` on the image of `e` and with `C` elsewhere. -/
lemma reachable_embed {A' : Type*} [DecidableEq A'] (e : A' ↪ A) (C : Config A Q)
    {D' : Config A' Q} (h : P.Reachable (fun x => C (e x)) D') :
    ∃ D, P.ReachIn (fun x => ∃ y, e y = x) C D ∧ (fun x => D (e x)) = D' :=
  P.exists_reach_of_embedding e (fun a b hab => ⟨⟨a, rfl⟩, ⟨b, rfl⟩, e.injective.ne hab⟩) C h

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
