import Cslib.Computability.Distributed.PopulationProtocols.Nondet
import Podc.Computability.Distributed.PopulationProtocols.Basic

-- CSLib candidate: Cslib/Computability/Distributed/PopulationProtocols/Nondet.lean (append to the
-- existing file)

/-!
# Nondeterministic population protocols: invariants, sub-populations, silence, output stability

Additions to `Cslib/Computability/Distributed/PopulationProtocols/Nondet.lean`, for a
nondeterministic protocol `P : NProtocol Q` and an interaction relation `I : A → A → Prop`.

* `NProtocol.ClosedStates P H`: every possible outcome of an interaction between states of `H`
  consists of states of `H`; then runs starting inside `H` stay inside `H`
  (`ClosedStates.reach`). Deterministic protocols: `Protocol.toN_closedStates_iff`.
* `NProtocol.StepIn P S`, `NProtocol.ReachIn P S`: interactions inside the sub-population `S`
  (the other agents are idle); `exists_reachIn_of_embedding`: a run of a population `A'` embeds
  into a sub-population of `A`.
* `NProtocol.SilentOn P I C` (`Silent` for the complete interaction graph): every possible
  interaction leaves both states unchanged; it is silence of the step relation
  (`silentOn_iff_isSilent`, for irreflexive `I`).
* `NProtocol.OutputStable P I out C`: the output can never change again; deterministic
  protocols: `Protocol.toN_outputStable_iff` (CSLib's `Protocol.OutputStable`).
* `NProtocol.exists_stepOn`: with nonempty transition sets and some interacting pair, every
  configuration has a successor (needed for fair runs).
-/

open Cslib.TransitionSystem

namespace Cslib.PopulationProtocol

variable {Q A : Type*}

namespace NProtocol

/-! ### Closed sets of states -/

/-- A set of states `H` is *closed* under `P` if every possible outcome of an interaction
between two states of `H` consists of states of `H`. -/
def ClosedStates (P : NProtocol Q) (H : Set Q) : Prop :=
  ∀ p ∈ H, ∀ q ∈ H, ∀ o ∈ P.δ p q, o.1 ∈ H ∧ o.2 ∈ H

variable [DecidableEq A] {P : NProtocol Q} {I J : A → A → Prop} {H : Set Q} {C D : Config A Q}

/-- A step keeps a configuration inside a closed set of states. -/
theorem ClosedStates.stepOn (hH : P.ClosedStates H) (hC : ∀ x, C x ∈ H)
    (h : P.StepOn I C D) : ∀ x, D x ∈ H := by
  obtain ⟨a, b, -, o, ho, rfl⟩ := h
  have h := hH _ (hC a) _ (hC b) o ho
  intro x
  by_cases hxb : x = b
  · subst hxb; rw [upd_right]; exact h.2
  · by_cases hxa : x = a
    · subst hxa; rw [upd, Function.update_of_ne hxb, Function.update_self]; exact h.1
    · rw [upd_other _ hxa hxb]; exact hC x

/-- **Closed sets of states are invariant.** If `C` only uses states of a closed set `H`, so does
every configuration reachable from `C`. -/
theorem ClosedStates.reach (hH : P.ClosedStates H) (hC : ∀ x, C x ∈ H)
    (h : Reach (P.StepOn I) C D) : ∀ x, D x ∈ H := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact hH.stepOn ih hst

/-! ### Sub-populations -/

variable (P) in
/-- One interaction of two distinct agents of the sub-population `S` (the other agents are
idle). -/
abbrev StepIn (S : A → Prop) : Config A Q → Config A Q → Prop :=
  P.StepOn fun a b => S a ∧ S b ∧ a ≠ b

variable (P) in
/-- Reachability inside the sub-population `S` (the other agents are idle). -/
abbrev ReachIn (S : A → Prop) : Config A Q → Config A Q → Prop := Reach (P.StepIn S)

/-- A run of a sub-population is a run of the population. -/
theorem ReachIn.reachable {S : A → Prop} (h : P.ReachIn S C D) : P.Reachable C D :=
  reach_stepOn_mono (fun _ _ h => h.2.2) h

/-- A run of a sub-population is a run of any larger sub-population. -/
theorem ReachIn.mono {S S' : A → Prop} (hS : ∀ x, S x → S' x) (h : P.ReachIn S C D) :
    P.ReachIn S' C D :=
  reach_stepOn_mono (fun a b h => ⟨hS a h.1, hS b h.2.1, h.2.2⟩) h

/-- Agents outside the sub-population keep their states. -/
theorem ReachIn.apply_eq {S : A → Prop} (h : P.ReachIn S C D) {x : A} (hx : ¬ S x) :
    D x = C x :=
  reach_stepOn_apply_eq (fun _ => ⟨fun h => hx h.1, fun h => hx h.2.1⟩) h

/-- **Embedding a run of another population.** If `e : A' ↪ A` and the population `A'` can go
from `C ∘ e` to `D'`, then the image of `e` can go from `C` to a configuration that agrees with
`D'` on the image of `e` (and with `C` elsewhere, `ReachIn.apply_eq`). -/
theorem exists_reachIn_of_embedding {A' : Type*} [DecidableEq A'] (e : A' ↪ A) (C : Config A Q)
    {D' : Config A' Q} (h : P.Reachable (fun x => C (e x)) D') :
    ∃ D, P.ReachIn (fun x => ∃ y, e y = x) C D ∧ (fun x => D (e x)) = D' :=
  P.exists_reach_of_embedding e (fun a b hab => ⟨⟨a, rfl⟩, ⟨b, rfl⟩, e.injective.ne hab⟩) C h

/-! ### Silent configurations -/

variable (P) in
/-- A configuration is *silent* along `I` if every possible interaction along `I` leaves both
states unchanged. -/
def SilentOn (I : A → A → Prop) (C : Config A Q) : Prop :=
  ∀ a b, I a b → ∀ o ∈ P.δ (C a) (C b), o = (C a, C b)

variable (P) in
/-- A silent configuration on the complete interaction graph. -/
abbrev Silent : Config A Q → Prop := P.SilentOn (· ≠ ·)

/-- For an irreflexive interaction relation, silence is silence of the step relation. -/
theorem silentOn_iff_isSilent (hI : ∀ a, ¬ I a a) : P.SilentOn I C ↔ IsSilent (P.StepOn I) C := by
  constructor
  · rintro hC D ⟨a, b, hab, o, ho, rfl⟩
    have hne : a ≠ b := by rintro rfl; exact hI a hab
    rw [hC a b hab o ho, upd_self _ hne]
  · intro hC a b hab o ho
    have hne : a ≠ b := by rintro rfl; exact hI a hab
    have h := hC _ ⟨a, b, hab, o, ho, rfl⟩
    rw [← congrFun h a, ← congrFun h b, upd_left _ hne, upd_right]

/-- Silence on the complete interaction graph is silence of `P.Step`. -/
theorem silent_iff_isSilent : P.Silent C ↔ IsSilent P.Step C :=
  silentOn_iff_isSilent fun _ h => h rfl

/-- Nothing changes from a silent configuration. -/
theorem SilentOn.reach_eq (hI : ∀ a, ¬ I a a) (hC : P.SilentOn I C)
    (h : Reach (P.StepOn I) C D) : D = C :=
  ((silentOn_iff_isSilent hI).1 hC).reach_eq h

/-- A silent configuration in a set `S` is stably in `S`. -/
theorem SilentOn.stablyIn (hI : ∀ a, ¬ I a a) {S : Set (Config A Q)} (hC : P.SilentOn I C)
    (hS : C ∈ S) : StablyIn (P.StepOn I) S C :=
  ((silentOn_iff_isSilent hI).1 hC).stablyIn hS

/-- Nothing changes from a silent configuration (complete interaction graph). -/
theorem Silent.reach_eq (hC : P.Silent C) (h : P.Reachable C D) : D = C :=
  SilentOn.reach_eq (fun _ h => h rfl) hC h

/-- A silent configuration in a set `S` is stably in `S` (complete interaction graph). -/
theorem Silent.stablyIn {S : Set (Config A Q)} (hC : P.Silent C) (hS : C ∈ S) :
    StablyIn P.Step S C :=
  SilentOn.stablyIn (fun _ h => h rfl) hC hS

/-! ### Output stability -/

variable (P) in
/-- The output of `C` (for an output map `out` on states) is *stable* along `I`: no configuration
reachable from `C` has a different output. -/
def OutputStable {O : Type*} (I : A → A → Prop) (out : Q → O) (C : Config A Q) : Prop :=
  ∀ D, Reach (P.StepOn I) C D → ∀ a, out (D a) = out (C a)

/-- Output stability is the stability of the set of configurations with the same output. -/
theorem outputStable_iff_stablyIn {O : Type*} {out : Q → O} :
    P.OutputStable I out C ↔ StablyIn (P.StepOn I) {D | ∀ a, out (D a) = out (C a)} C :=
  Iff.rfl

/-- Output-stable configurations are closed under steps. -/
theorem isTrap_outputStable {O : Type*} (out : Q → O) :
    IsTrap (P.StepOn I) {C | P.OutputStable I out C} := by
  intro C D hC hCD E hDE v
  rw [hC E (Relation.ReflTransGen.head hCD hDE) v, hC D (Relation.ReflTransGen.single hCD) v]

/-- The output stays the same along runs from an output-stable configuration. -/
theorem OutputStable.apply_eq {O : Type*} {out : Q → O} (hC : P.OutputStable I out C)
    (h : Reach (P.StepOn I) C D) (a : A) : out (D a) = out (C a) :=
  hC D h a

/-- The number of leaders does not change along runs from an output-stable configuration. -/
theorem OutputStable.numLeaders_eq [Fintype A] {leader : Q → Bool}
    (hC : P.OutputStable I leader C) (h : Reach (P.StepOn I) C D) :
    numLeaders leader D = numLeaders leader C := by
  unfold numLeaders
  congr 1
  ext v
  simp [hC D h v]

/-! ### Totality -/

/-- If some pair of agents may interact and every transition set is nonempty, every
configuration has a successor. -/
theorem exists_stepOn (hI : ∃ a b, I a b) (hδ : ∀ p q, (P.δ p q).Nonempty) (C : Config A Q) :
    ∃ D, P.StepOn I C D := by
  obtain ⟨a, b, hab⟩ := hI
  obtain ⟨o, ho⟩ := hδ (C a) (C b)
  exact ⟨_, a, b, hab, o, ho, rfl⟩

end NProtocol

/-! ### Deterministic protocols -/

namespace Protocol

variable {P : Protocol Q} {H : Set Q}

/-- A closed set of states of `P` is a closed set of states of `P.toN`. -/
theorem toN_closedStates_iff : P.toN.ClosedStates H ↔ P.ClosedStates H := by
  simp [NProtocol.ClosedStates, ClosedStates]

variable [DecidableEq A]

/-- Output stability for `P.toN` (complete interaction graph) is CSLib's output stability. -/
theorem toN_outputStable_iff {O : Type*} {out : Q → O} {C : Config A Q} :
    P.toN.OutputStable (· ≠ ·) out C ↔ P.OutputStable out C :=
  ⟨fun h D hD => h D (toN_reachable_iff.2 hD), fun h D hD => h D (toN_reachable_iff.1 hD)⟩

end Protocol

end Cslib.PopulationProtocol
