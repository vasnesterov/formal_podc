import Cslib.Computability.Distributed.PopulationProtocols.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Population protocols with randomized transitions: model and problem statements

Burman, Chen, Chen, Doty, Nowak, Severson, Xu, *Time-Optimal Self-Stabilizing Leader Election in
Population Protocols*, PODC 2021 (arXiv:1907.06068v5), Section 2.

The paper allows *probabilistic* transitions `T : S × S → Dist(S × S)`. All statements we formalize
about self-stabilization "with probability 1" only depend on the **support** of the transition
distributions (finite state space, uniformly random ordered pair; see `RandomScheduler.lean` for the
Markov-chain bridge). We therefore model a protocol by its support relation `δ p q ⊆ Q × Q`
(`NProtocol`). Deterministic CSLib protocols embed via `NProtocol.ofProtocol`.

* `NProtocol.Step`, `NProtocol.Reachable`: one interaction of an ordered pair of distinct agents.
* `NProtocol.StablyCorrect good C`: every configuration reachable from `C` is `good`.
* `NProtocol.SelfStabilizes good`: from every configuration a stably correct one is reachable. For
  a finite state space and the uniform random scheduler this is *equivalent* to "from every
  configuration a stably correct configuration is reached with probability 1"
  (`RandomScheduler.lean`).
* `SolvesSSLE` (one agent with `leader = true`), `SolvesSSR` (ranks form a bijection onto
  `Fin n`).
* Sub-population runs: `NProtocol.reachable_embed` (a run of a sub-population embeds into the
  whole population, the other agents being idle).
-/

open Cslib.PopulationProtocol

namespace TimeOptimalSSLE

-- CSLib candidate
/-- A population protocol whose transitions may be randomized: `δ p q` is the support of the
distribution of the new states `(initiator, responder)` when an initiator in state `p` meets a
responder in state `q`. -/
structure NProtocol (Q : Type*) where
  /-- Possible outcomes of an interaction (support of the transition distribution). -/
  δ : Q → Q → Set (Q × Q)
  /-- Every interaction has at least one outcome. -/
  nonempty : ∀ p q, (δ p q).Nonempty

namespace NProtocol

variable {Q A : Type*} [DecidableEq A] (P : NProtocol Q)

/-- The configuration after initiator `a` and responder `b` take the new states `o`. -/
def upd (C : Config A Q) (a b : A) (o : Q × Q) : Config A Q :=
  Function.update (Function.update C a o.1) b o.2

lemma upd_left (C : Config A Q) {a b : A} (h : a ≠ b) (o : Q × Q) : upd C a b o a = o.1 := by
  simp [upd, h]

@[simp] lemma upd_right (C : Config A Q) (a b : A) (o : Q × Q) : upd C a b o b = o.2 := by
  simp [upd]

lemma upd_other (C : Config A Q) {a b x : A} (ha : x ≠ a) (hb : x ≠ b) (o : Q × Q) :
    upd C a b o x = C x := by
  simp [upd, ha, hb]

/-- One interaction of two distinct agents, restricted to agents satisfying `S`. -/
def StepIn (S : A → Prop) (C D : Config A Q) : Prop :=
  ∃ a b, S a ∧ S b ∧ a ≠ b ∧ ∃ o ∈ P.δ (C a) (C b), D = upd C a b o

/-- One interaction of two distinct agents. -/
def Step (C D : Config A Q) : Prop := P.StepIn (fun _ => True) C D

/-- Reachability inside the sub-population `S` (the other agents are idle). -/
def ReachIn (S : A → Prop) : Config A Q → Config A Q → Prop := Relation.ReflTransGen (P.StepIn S)

/-- Reachability. -/
def Reachable : Config A Q → Config A Q → Prop := Relation.ReflTransGen P.Step

lemma ReachIn.reachable {S : A → Prop} {C D : Config A Q} (h : P.ReachIn S C D) :
    P.Reachable C D := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨a, b, -, -, hab, o, ho, rfl⟩ := hst
    exact ih.tail ⟨a, b, trivial, trivial, hab, o, ho, rfl⟩

lemma ReachIn.mono {S S' : A → Prop} (hS : ∀ x, S x → S' x) {C D : Config A Q}
    (h : P.ReachIn S C D) : P.ReachIn S' C D := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨a, b, ha, hb, hab, o, ho, rfl⟩ := hst
    exact ih.tail ⟨a, b, hS a ha, hS b hb, hab, o, ho, rfl⟩

/-- Agents outside the sub-population keep their states. -/
lemma ReachIn.eq_of_not_mem {S : A → Prop} {C D : Config A Q} (h : P.ReachIn S C D) {x : A}
    (hx : ¬ S x) : D x = C x := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨a, b, ha, hb, hab, o, ho, rfl⟩ := hst
    rw [upd_other _ (fun h => hx (by subst h; exact ha)) (fun h => hx (by subst h; exact hb))]
    exact ih

/-- A state predicate / set of configurations is *stably correct* from `C` if all configurations
reachable from `C` satisfy it. -/
def StablyCorrect (good : Config A Q → Prop) (C : Config A Q) : Prop :=
  ∀ D, P.Reachable C D → good D

/-- Self-stabilization (in the "probability 1" sense, see `RandomScheduler.lean`): from every
configuration, some stably correct configuration is reachable. -/
def SelfStabilizes (good : Config A Q → Prop) : Prop :=
  ∀ C : Config A Q, ∃ D, P.Reachable C D ∧ P.StablyCorrect good D

/-- The number of agents whose state is a leader state. -/
def numLeaders [Fintype A] (leader : Q → Bool) (C : Config A Q) : ℕ :=
  (Finset.univ.filter fun a => leader (C a) = true).card

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

lemma Silent.step_eq {C D : Config A Q} (hC : P.Silent C) (h : P.Step C D) : D = C := by
  obtain ⟨a, b, -, -, hab, o, ho, rfl⟩ := h
  rw [hC a b hab o ho]
  funext x
  by_cases hxb : x = b
  · subst hxb; simp
  · by_cases hxa : x = a
    · subst hxa; rw [upd_left _ hab]
    · rw [upd_other _ hxa hxb]

lemma Silent.reachable_eq {C : Config A Q} {D : Config A Q} (hC : P.Silent C) (h : P.Reachable C D) : D = C := by
  induction h with
  | refl => rfl
  | tail _ hst ih => subst ih; exact hC.step_eq P hst

/-- A silent correct configuration is stably correct. -/
lemma Silent.stablyCorrect {good : Config A Q → Prop} {C : Config A Q} (hC : P.Silent C)
    (hg : good C) : P.StablyCorrect good C := fun _ hD => (hC.reachable_eq P hD).symm ▸ hg

/-! ### Sub-populations -/

-- CSLib candidate
/-- **Embedding a run of a sub-population.** If `e : A' ↪ A` and the population `A'` can go
from `C ∘ e` to `D'`, then the population `A` can go from `C` to a configuration that agrees
with `D'` on the image of `e` and with `C` elsewhere. -/
lemma reachable_embed {A' : Type*} [DecidableEq A'] (e : A' ↪ A) (C : Config A Q)
    {D' : Config A' Q} (h : P.Reachable (fun x => C (e x)) D') :
    ∃ D, P.ReachIn (fun x => ∃ y, e y = x) C D ∧ (fun x => D (e x)) = D' := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDe⟩ := ih
    obtain ⟨a, b, -, -, hab, o, ho, rfl⟩ := hst
    refine ⟨upd D (e a) (e b) o, hD.tail ⟨e a, e b, ⟨a, rfl⟩, ⟨b, rfl⟩,
      e.injective.ne hab, o, ?_, rfl⟩, ?_⟩
    · subst hDe; exact ho
    · subst hDe
      funext x
      simp only [upd, Function.update_apply, e.injective.eq_iff]

/-! ### Deterministic protocols -/

/-- A deterministic CSLib population protocol as a protocol with (trivially) randomized
transitions. -/
def ofProtocol (P : Protocol Q) : NProtocol Q where
  δ p q := {P.δ p q}
  nonempty _ _ := Set.singleton_nonempty _

lemma ofProtocol_step_iff (P : Protocol Q) (C D : Config A Q) :
    (ofProtocol P).Step C D ↔ P.Step C D := by
  constructor
  · rintro ⟨a, b, -, -, hab, o, ho, rfl⟩
    refine ⟨a, b, hab, ?_⟩
    simp only [ofProtocol, Set.mem_singleton_iff] at ho
    subst ho
    funext x
    by_cases hxb : x = b
    · subst hxb; simp [Protocol.interact_self_right _ _ hab]
    · by_cases hxa : x = a
      · subst hxa; rw [upd_left _ hab]; simp
      · rw [upd_other _ hxa hxb, Protocol.interact_other _ _ hxa hxb]
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨a, b, trivial, trivial, hab, P.δ (C a) (C b), rfl, ?_⟩
    funext x
    by_cases hxb : x = b
    · subst hxb; simp [Protocol.interact_self_right _ _ hab]
    · by_cases hxa : x = a
      · subst hxa; rw [upd_left _ hab]; simp
      · rw [upd_other _ hxa hxb, Protocol.interact_other _ _ hxa hxb]

lemma ofProtocol_reachable_iff (P : Protocol Q) (C D : Config A Q) :
    (ofProtocol P).Reachable C D ↔ P.Reachable C D := by
  unfold Reachable Protocol.Reachable
  have : (ofProtocol P).Step (A := A) = P.Step := by
    funext C D; exact propext (ofProtocol_step_iff P C D)
  rw [this]

end NProtocol

end TimeOptimalSSLE
