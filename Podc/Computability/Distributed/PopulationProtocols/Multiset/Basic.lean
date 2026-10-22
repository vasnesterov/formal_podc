/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/PopulationProtocols/Multiset/Basic.lean
import Podc.Computability.Distributed.SelfStabilization.EdgeFair
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Abel

/-!
# Population protocols over multiset configurations (Petri-net style)

The model of population protocols used by Esparza and coauthors (e.g. Blondin, Esparza, Jaax,
Meyer, *Towards efficient verification of population protocols*, PODC 2017): agents are anonymous,
so a configuration is a *multiset* of states, and a protocol is a *relation* `T ⊆ Q² × Q²` of
transitions (nondeterministic), total on pairs of states. This complements CSLib's
labelled-agent model (`Cslib.PopulationProtocol.Protocol`, `NProtocol`).

## Main definitions

* `Transition Q`: a transition `(p, q) ↦ (p', q')`, with `pre`, `post` (multisets of size 2) and
  `Transition.Silent` (`pre = post`).
* `MStep T C C'`: `C'` is obtained from `C` by firing some `t ∈ T` (`pre t ≤ C`,
  `C' = C - pre t + post t`); `MReach T` is its reflexive-transitive closure, `Terminal T C`
  means that only `C` is reachable from `C`.
* `MProtocol Q Λ`: transitions `T` (total), input map `I : Λ → Q`, output map `O : Q → Bool`.
  `P.restrict S` is the protocol `P[S]` induced by `S ⊆ T` (plus all identity transitions).
* Executions are runs of `MStep P.T` (`Cslib.TransitionSystem.Run`); fairness is *edge fairness*
  `Run.EdgeFair` (if `C` occurs infinitely often and `C → C'` then `C C'` occurs consecutively
  infinitely often).
* `P.WellSpecified`, `P.Silent`, `P.Termination`, `P.Consensus`.

## Main statements

* `MProtocol.silent_iff_termination`: a protocol is silent iff it satisfies Termination.
* `MProtocol.wellSpecified_iff_consensus`: a silent protocol is well specified iff it satisfies
  Consensus.
-/

namespace Cslib.PopulationProtocol

open Cslib.TransitionSystem Filter

/-- A transition `(p, q) ↦ (p', q')` of a population protocol. -/
structure Transition (Q : Type*) where
  /-- First pre-state. -/
  p : Q
  /-- Second pre-state. -/
  q : Q
  /-- First post-state. -/
  p' : Q
  /-- Second post-state. -/
  q' : Q
deriving DecidableEq

namespace Transition

variable {Q : Type*}

/-- Transitions are quadruples of states. -/
def equivProd : Transition Q ≃ Q × Q × Q × Q where
  toFun t := (t.p, t.q, t.p', t.q')
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

instance [Fintype Q] : Fintype (Transition Q) := Fintype.ofEquiv _ equivProd.symm

/-- The multiset `⦃p, q⦄` of states consumed by the transition. -/
def pre (t : Transition Q) : Multiset Q := {t.p, t.q}

/-- The multiset `⦃p', q'⦄` of states produced by the transition. -/
def post (t : Transition Q) : Multiset Q := {t.p', t.q'}

/-- A transition is silent if it cannot change any configuration. -/
def Silent (t : Transition Q) : Prop := t.pre = t.post

@[simp] theorem card_pre (t : Transition Q) : Multiset.card t.pre = 2 := by simp [pre]
@[simp] theorem card_post (t : Transition Q) : Multiset.card t.post = 2 := by simp [post]

variable [DecidableEq Q]

/-- `t` fires at `C` and leads to `C'`. -/
def Fires (t : Transition Q) (C C' : Multiset Q) : Prop :=
  t.pre ≤ C ∧ C' = C - t.pre + t.post


theorem Fires.card_eq {t : Transition Q} {C C' : Multiset Q} (h : t.Fires C C') :
    Multiset.card C' = Multiset.card C := by
  have := Multiset.card_le_card h.1
  rw [h.2, Multiset.card_add, Multiset.card_sub h.1]
  simp only [card_pre, card_post] at this ⊢
  omega

theorem Fires.two_le_card {t : Transition Q} {C C' : Multiset Q} (h : t.Fires C C') :
    2 ≤ Multiset.card C := by simpa using Multiset.card_le_card h.1

/-- A silent transition does not change the configuration. -/
theorem Fires.eq_of_silent {t : Transition Q} {C C' : Multiset Q}
    (h : t.Fires C C') (hs : t.Silent) : C' = C := by
  rw [h.2, ← hs, tsub_add_cancel_of_le h.1]

/-- A transition that does not change the configuration is silent. -/
theorem Fires.silent_of_eq {t : Transition Q} {C : Multiset Q}
    (h : t.Fires C C) : t.Silent := by
  have h2 := h.2
  conv_lhs at h2 => rw [← tsub_add_cancel_of_le h.1]
  exact add_left_cancel h2

/-- Additive functionals change by `post − pre` when a transition fires. -/
theorem Fires.sum_map {t : Transition Q} {C C' : Multiset Q} (h : t.Fires C C') {M : Type*}
    [AddCommMonoid M] (w : Q → M) :
    (C'.map w).sum + (t.pre.map w).sum = (C.map w).sum + (t.post.map w).sum := by
  conv_rhs => rw [← tsub_add_cancel_of_le h.1]
  rw [h.2]
  simp only [Multiset.map_add, Multiset.sum_add]
  abel

end Transition

variable {Q Λ : Type*} [DecidableEq Q]

/-- One step through a transition of `T`. -/
def MStep (T : Set (Transition Q)) (C C' : Multiset Q) : Prop := ∃ t ∈ T, t.Fires C C'

/-- Reachability through transitions of `T`. -/
abbrev MReach (T : Set (Transition Q)) : Multiset Q → Multiset Q → Prop :=
  Relation.ReflTransGen (MStep T)

/-- A configuration is *terminal* if every configuration reachable from it equals it. -/
def Terminal (T : Set (Transition Q)) (C : Multiset Q) : Prop := ∀ C', MReach T C C' → C' = C

section Steps

variable {T : Set (Transition Q)} {C C' : Multiset Q}

theorem MStep.card_eq (h : MStep T C C') : Multiset.card C' = Multiset.card C :=
  h.elim fun _ ht => ht.2.card_eq

theorem MReach.card_eq (h : MReach T C C') : Multiset.card C' = Multiset.card C := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact hs.card_eq.trans ih

theorem MReach.mono {S : Set (Transition Q)} (hST : S ⊆ T) (h : MReach S C C') :
    MReach T C C' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => obtain ⟨t, ht, hf⟩ := hs; exact ih.tail ⟨t, hST ht, hf⟩

theorem terminal_iff_isSilent : Terminal T C ↔ IsSilent (MStep T) C :=
  ⟨fun h C' hC' => h C' (.single hC'), fun h _ hC' => h.reach_eq hC'⟩

/-- `C` is terminal iff every transition of `T` enabled at `C` is silent. -/
theorem terminal_iff_forall_silent :
    Terminal T C ↔ ∀ t ∈ T, t.pre ≤ C → t.Silent := by
  rw [terminal_iff_isSilent]
  refine ⟨fun h t ht hle => ?_, fun h C' ⟨t, ht, hf⟩ => hf.eq_of_silent (h t ht hf.1)⟩
  have hf : t.Fires C (C - t.pre + t.post) := ⟨hle, rfl⟩
  have := h _ ⟨t, ht, hf⟩
  exact (this ▸ hf).silent_of_eq

/-- Terminality for a union of transition sets. -/
theorem terminal_union {S : Set (Transition Q)} :
    Terminal (S ∪ T) C ↔ Terminal S C ∧ Terminal T C := by
  simp only [terminal_iff_forall_silent, Set.mem_union]
  exact ⟨fun h => ⟨fun t ht => h t (.inl ht), fun t ht => h t (.inr ht)⟩,
    fun h t ht => ht.elim (h.1 t) (h.2 t)⟩

/-- Finitely many configurations are reachable from any configuration. -/
theorem MReach.finite [Fintype Q] (C : Multiset Q) : {C' | MReach T C C'}.Finite := by
  refine (Set.finite_range (fun s : Sym Q (Multiset.card C) => (s : Multiset Q))).subset ?_
  intro C' hC'
  exact ⟨⟨C', MReach.card_eq hC'⟩, rfl⟩

end Steps

/-- A population protocol in the multiset (Petri net) formalism: states `Q`, transitions `T`
(a relation, total on pairs of states), input alphabet `Λ`, input map `I`, output map `O`. -/
structure MProtocol (Q Λ : Type*) where
  /-- The transitions. -/
  T : Set (Transition Q)
  /-- Every pair of states has at least one transition. -/
  total : ∀ p q, ∃ p' q', (⟨p, q, p', q'⟩ : Transition Q) ∈ T
  /-- The input function. -/
  I : Λ → Q
  /-- The output function. -/
  O : Q → Bool

/-- `C` is a consensus configuration with output `b`. -/
def IsConsensus (O : Q → Bool) (C : Multiset Q) (b : Bool) : Prop := ∀ q ∈ C, O q = b

namespace MProtocol

variable (P : MProtocol Q Λ)

/-- The identity transitions `(p, q) ↦ (p, q)`. -/
def idTrans : Set (Transition Q) := {t | t.p' = t.p ∧ t.q' = t.q}

/-- The protocol `P[S]` induced by a set of transitions `S` (identity transitions are added so
that any two states can interact). -/
def restrict (S : Set (Transition Q)) : MProtocol Q Λ where
  T := S ∪ idTrans
  total p q := ⟨p, q, Or.inr ⟨rfl, rfl⟩⟩
  I := P.I
  O := P.O

omit [DecidableEq Q] in
/-- Identity transitions are silent. -/
theorem silent_of_mem_idTrans {t : Transition Q} (ht : t ∈ idTrans) : t.Silent := by
  obtain ⟨h1, h2⟩ := ht
  simp [Transition.Silent, Transition.pre, Transition.post, h1, h2]

/-- Steps through identity transitions can be dropped. -/
theorem _root_.Cslib.PopulationProtocol.MReach.of_union_idTrans {S : Set (Transition Q)}
    {C D : Multiset Q} (h : MReach (S ∪ idTrans) C D) : MReach S C D := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨t, ht | ht, hf⟩ := hs
    · exact ih.tail ⟨t, ht, hf⟩
    · exact hf.eq_of_silent (silent_of_mem_idTrans ht) ▸ ih

/-- Every configuration is terminal for the identity transitions. -/
theorem terminal_idTrans (C : Multiset Q) : Terminal idTrans C :=
  terminal_iff_forall_silent.2 fun _ ht _ => silent_of_mem_idTrans ht

/-- Reachability in `P[S]` is reachability through `S`. -/
theorem restrict_reach_iff {S : Set (Transition Q)} {C D : Multiset Q} :
    MReach (P.restrict S).T C D ↔ MReach S C D :=
  ⟨MReach.of_union_idTrans, MReach.mono Set.subset_union_left⟩

/-- One step of `P`. -/
abbrev Step : Multiset Q → Multiset Q → Prop := MStep P.T

/-- The initial configuration `I(X)` of an input `X`. -/
def init (X : Multiset Λ) : Multiset Q := X.map P.I

/-- `C` is initial: `C = I(X)` for some input population `X` (at least two agents). -/
def IsInitial (C : Multiset Q) : Prop := ∃ X : Multiset Λ, 2 ≤ Multiset.card X ∧ C = P.init X

/-- An execution stabilizes to `b`: eventually all configurations are consensus configurations
with output `b`. -/
def StabilizesTo (E : Run P.Step) (b : Bool) : Prop :=
  ∀ᶠ t in atTop, IsConsensus P.O (E.st t) b

/-- Well-specification: for every input, all fair executions from `I(X)` stabilize to a common
value. -/
def WellSpecified : Prop :=
  ∀ X : Multiset Λ, 2 ≤ Multiset.card X →
    ∃ b, ∀ E : Run P.Step, E.st 0 = P.init X → E.EdgeFair → P.StabilizesTo E b

/-- Silence: every fair execution (from any configuration) is eventually constant. -/
def Silent : Prop := ∀ E : Run P.Step, E.EdgeFair → E.Silent

/-- Termination: a terminal configuration is reachable from every configuration. -/
def Termination : Prop := ∀ C, ∃ C', MReach P.T C C' ∧ Terminal P.T C'

/-- Consensus: from every initial configuration, all reachable terminal configurations are
consensus configurations with the same output. -/
def Consensus : Prop :=
  ∀ C, P.IsInitial C → ∃ b, ∀ C', MReach P.T C C' → Terminal P.T C' → IsConsensus P.O C' b

/-- `WS²`: well-specified silent protocols. -/
def WS2 : Prop := P.WellSpecified ∧ P.Silent

variable {P}

/-- Every configuration with at least two agents enables a transition. -/
theorem exists_step {C : Multiset Q} (hC : 2 ≤ Multiset.card C) : ∃ C', P.Step C C' := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card C)
  obtain ⟨C₁, rfl⟩ := Multiset.exists_cons_of_mem ha
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1
    (by simp at hC; omega : 0 < Multiset.card C₁)
  obtain ⟨C₂, rfl⟩ := Multiset.exists_cons_of_mem hb
  obtain ⟨p', q', ht⟩ := P.total a b
  refine ⟨(a ::ₘ b ::ₘ C₂) - _ + _, _, ht, ?_, rfl⟩
  simp only [Transition.pre, Multiset.insert_eq_cons]
  exact Multiset.cons_le_cons _ (Multiset.cons_le_cons _ (Multiset.zero_le _))

/-- A terminal configuration with at least two agents has a self-loop. -/
theorem Terminal.step_self {C : Multiset Q} (h : Terminal P.T C) (hC : 2 ≤ Multiset.card C) :
    P.Step C C := by
  obtain ⟨C', hC'⟩ := exists_step (P := P) hC
  exact h C' (.single hC') ▸ hC'

/-- Every target of a step has a successor. -/
theorem step_total {C C' : Multiset Q} (h : P.Step C C') : ∃ C'', P.Step C' C'' := by
  obtain ⟨t, -, ht⟩ := h
  exact exists_step (ht.card_eq ▸ ht.two_le_card)

/-- **Ranking functions.** If a well-founded measure `Φ` decreases whenever a non-silent
transition of `S` fires, then every (fair or unfair) execution of `P[S]` is silent. -/
theorem restrict_silent_of_measure {S : Set (Transition Q)} {β : Type*} [Preorder β]
    [WellFoundedLT β] (Φ : Multiset Q → β)
    (h : ∀ t ∈ S, ¬ t.Silent → ∀ C, t.pre ≤ C → Φ (C - t.pre + t.post) < Φ C) :
    ∀ E : Run (P.restrict S).Step, E.Silent := by
  intro E
  refine E.silent_of_wellFounded (r := fun x y => Φ x < Φ y)
    (InvImage.wf Φ wellFounded_lt) fun n hne => ?_
  obtain ⟨t, ht, hf⟩ := E.step n
  rcases ht with ht | ht
  · have hs : ¬ t.Silent := fun hs => hne (hf.eq_of_silent hs)
    rw [hf.2]
    exact h t ht hs _ hf.1
  · exact absurd (hf.eq_of_silent (silent_of_mem_idTrans ht)) hne

/-- **Silence = termination** (Proposition 19(a) of Blondin–Esparza–Jaax–Meyer). -/
theorem silent_iff_termination [Fintype Q] : P.Silent ↔ P.Termination := by
  unfold Silent Termination
  simp_rw [terminal_iff_isSilent]
  exact forall_edgeFair_silent_iff (fun C => MReach.finite C) fun _ _ h => step_total h

omit [DecidableEq Q] in
theorem card_init (X : Multiset Λ) : Multiset.card (P.init X) = Multiset.card X := by
  simp [init]

/-- **A silent protocol is well specified iff it satisfies Consensus** (Proposition 19(b) of
Blondin–Esparza–Jaax–Meyer). -/
theorem wellSpecified_iff_consensus [Fintype Q] (hs : P.Silent) :
    P.WellSpecified ↔ P.Consensus := by
  constructor
  · rintro hws C ⟨X, hX, rfl⟩
    obtain ⟨b, hb⟩ := hws X hX
    refine ⟨b, fun C' hC' hterm => ?_⟩
    have hcard : 2 ≤ Multiset.card C' := by rw [hC'.card_eq, card_init]; exact hX
    obtain ⟨E, hE0, hEf, hEC⟩ := exists_run_of_reach_isSilent hC'
      (terminal_iff_isSilent.1 hterm) (Terminal.step_self (P := P) hterm hcard)
    obtain ⟨t, h1, h2⟩ := ((hb E hE0 hEf).and hEC).exists
    exact h2 ▸ h1
  · intro hc X hX
    obtain ⟨b, hb⟩ := hc _ ⟨X, hX, rfl⟩
    refine ⟨b, fun E hE0 hEf => ?_⟩
    obtain ⟨n, hn⟩ := hs E hEf
    have hterm : Terminal P.T (E.st n) :=
      terminal_iff_isSilent.2 (hEf.globallyFair.isSilent_of_silent hn)
    have hcons := hb (E.st n) (hE0 ▸ E.reach n) hterm
    exact eventually_atTop.2 ⟨n, fun t ht => (hn t ht) ▸ hcons⟩

end MProtocol

end Cslib.PopulationProtocol
