/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/NetworkConstructors/Basic.lean
import Podc.Computability.Distributed.SelfStabilization.EdgeFair
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Network constructors (Michail–Spirakis)

A *network constructor* (NET) is a population protocol whose interacting agents also read and
write the binary state of the edge joining them (Michail and Spirakis, *Simple and efficient local
codes for distributed stable network construction*, PODC 2014). The agents are finite-state, start
in a common initial state, all edges start inactive, and an adversarial scheduler picks in every
step a pair of distinct agents (the interaction graph is complete). The *output* of a
configuration is the graph of active edges induced by the agents in output states.

## Main definitions

* `Protocol Q`: initial state `init`, output states `out`, transition function
  `δ : Q → Q → Bool → Q × Q × Bool` (states of the two agents and of their edge).
* `Config V Q`: agent states and a symmetric edge-state function `V → V → Bool`.
* `Protocol.interact P C u v`: the interaction of `u` (in the role of the first argument of `δ`)
  and `v`. The step relation `Protocol.Step` lets the scheduler choose both the pair and the
  orientation, which is the paper's semantics: a pair of states `a ≠ b` is matched against the rule
  given for `(a, b, c)` or for `(b, a, c)`, and if `a = b` with `δ(a, a, c) = (a', b', c')`, either
  agent may get `a'`.
* `Protocol.output P C`: the output subgraph (vertices: agents in output states; edges: active
  edges between them).
* `Protocol.Constructs P T`: every globally fair execution from the initial configuration has an
  output that stabilizes to a graph satisfying `T`.

## Main results

* `Protocol.constructs_of_reach`: to prove that a protocol constructs `T`, give a closed set `S` of
  configurations in which the output never changes and satisfies `T`, reachable from every
  configuration reachable from the initial one (the method used throughout the paper).
* `Protocol.not_constructs_of_unstable`: if some reachable configuration `C` is such that from
  every configuration reachable from `C`, two configurations with different outputs are reachable,
  then some globally fair execution never stabilizes its output.
* `TransitionSystem.exists_globallyFair_of_reach`: globally fair runs through any reachable
  configuration (prefixing a path to a globally fair run).
-/

open Filter Cslib.TransitionSystem

namespace Cslib

namespace TransitionSystem

variable {X : Type*} {R : X → X → Prop}

-- `Run.cons` (prepend one transition to a run) is defined in
-- `Podc.Computability.Distributed.SelfStabilization.EdgeFair`.

@[simp] theorem Run.cons_st_zero (x : X) (E : Run R) (h : R x (E.st 0)) :
    (Run.cons x E h).st 0 = x := rfl

@[simp] theorem Run.cons_st_succ (x : X) (E : Run R) (h : R x (E.st 0)) (t : ℕ) :
    (Run.cons x E h).st (t + 1) = E.st t := rfl

theorem Run.GloballyFair.cons {x : X} {E : Run R} {h : R x (E.st 0)} (hE : E.GloballyFair) :
    (Run.cons x E h).GloballyFair := by
  have key : ∀ c, (∃ᶠ t in atTop, (Run.cons x E h).st t = c) ↔ ∃ᶠ t in atTop, E.st t = c := by
    intro c
    simp only [frequently_atTop]
    constructor
    · intro H T
      obtain ⟨t, ht, hc⟩ := H (T + 1)
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact ⟨s, by omega, hc⟩
    · intro H T
      obtain ⟨t, ht, hc⟩ := H T
      exact ⟨t + 1, by omega, hc⟩
  intro a b hab ha
  rw [key] at ha ⊢
  exact hE a b hab ha

/-- A globally fair run passing through any configuration reachable from `x₀` (finite total
systems). -/
theorem exists_globallyFair_of_reach [Finite X] (htot : ∀ x, ∃ y, R x y) {x₀ x : X}
    (h : Reach R x₀ x) : ∃ E : Run R, E.st 0 = x₀ ∧ E.GloballyFair ∧ ∃ k, E.st k = x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨E, hE0, hE⟩ := exists_globallyFair htot x
    exact ⟨E, hE0, hE, 0, hE0⟩
  | head hxy _ ih =>
    obtain ⟨E, hE0, hE, k, hk⟩ := ih
    exact ⟨Run.cons _ E (hE0 ▸ hxy), rfl, hE.cons, k + 1, hk⟩

end TransitionSystem

namespace NetworkConstructor

/-- A network constructor: finite-state agents with a common initial state `init`, output states
`out`, and a transition function on (initiator state, responder state, edge state). -/
structure Protocol (Q : Type*) where
  /-- The initial state of every agent. -/
  init : Q
  /-- The output states. -/
  out : Q → Bool
  /-- The transition function: `δ a b c = (a', b', c')`. -/
  δ : Q → Q → Bool → Q × Q × Bool

/-- A configuration: the state of every agent and of every edge (`true` = active). -/
@[ext]
structure Config (V Q : Type*) where
  /-- Agent states. -/
  st : V → Q
  /-- Edge states (`true` = active); the value on the diagonal is irrelevant. -/
  edge : V → V → Bool
  /-- Edges are undirected. -/
  symm : ∀ u v, edge u v = edge v u

variable {V Q : Type*}

namespace Config

theorem injective_toProd : Function.Injective fun C : Config V Q => (C.st, C.edge) := by
  intro C D h
  simp only [Prod.mk.injEq] at h
  exact Config.ext h.1 h.2

instance [Finite V] [Finite Q] : Finite (Config V Q) :=
  Finite.of_injective _ injective_toProd

instance [Fintype V] [DecidableEq V] [DecidableEq Q] : DecidableEq (Config V Q) :=
  fun C D => decidable_of_iff (C.st = D.st ∧ C.edge = D.edge)
    ⟨fun h => Config.ext h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- The graph of active edges. -/
def active (C : Config V Q) : SimpleGraph V where
  Adj u v := u ≠ v ∧ C.edge u v = true
  symm := ⟨fun u v h => ⟨h.1.symm, C.symm u v ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem active_adj {C : Config V Q} {u v : V} :
    C.active.Adj u v ↔ u ≠ v ∧ C.edge u v = true := Iff.rfl

end Config

namespace Protocol

variable (P : Protocol Q) [DecidableEq V]

/-- The initial configuration: all agents in `init`, all edges inactive. -/
def initConfig : Config V Q where
  st _ := P.init
  edge _ _ := false
  symm _ _ := rfl

/-- Interaction of `u` (initiator, first argument of `δ`) with `v` (responder). -/
def interact (C : Config V Q) (u v : V) : Config V Q where
  st x := if x = u then (P.δ (C.st u) (C.st v) (C.edge u v)).1
    else if x = v then (P.δ (C.st u) (C.st v) (C.edge u v)).2.1 else C.st x
  edge x y := if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then (P.δ (C.st u) (C.st v) (C.edge u v)).2.2
    else C.edge x y
  symm x y := by
    by_cases h : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    · have h' : (y = u ∧ x = v) ∨ (y = v ∧ x = u) := by tauto
      simp only [h, h', ite_true]
    · have h' : ¬((y = u ∧ x = v) ∨ (y = v ∧ x = u)) := by tauto
      simp only [h, h', ite_false, C.symm]

/-- One step: some pair of distinct agents interacts (in some orientation). -/
def Step (C C' : Config V Q) : Prop := ∃ u v, u ≠ v ∧ C' = P.interact C u v

/-- Reachability. -/
abbrev Reachable : Config V Q → Config V Q → Prop := Reach P.Step

/-- The output graph: agents in output states and the active edges between them. -/
def output (C : Config V Q) : (⊤ : SimpleGraph V).Subgraph where
  verts := {u | P.out (C.st u) = true}
  Adj u v := u ≠ v ∧ C.edge u v = true ∧ P.out (C.st u) = true ∧ P.out (C.st v) = true
  adj_sub h := h.1
  edge_vert h := h.2.2.1
  symm := ⟨fun u v h => ⟨h.1.symm, C.symm u v ▸ h.2.1, h.2.2.2, h.2.2.1⟩⟩

omit [DecidableEq V] in
theorem output_eq_of {C D : Config V Q} (hst : ∀ u, P.out (C.st u) = P.out (D.st u))
    (he : C.edge = D.edge) : P.output C = P.output D := by
  ext u
  · simp [output, hst]
  · simp [output, hst, he]

/-- `P` *constructs* the graph class `T`: in every globally fair execution from the initial
configuration, the output stabilizes to a graph in `T` (Definition 2 of Michail–Spirakis). -/
def Constructs (T : (⊤ : SimpleGraph V).Subgraph → Prop) : Prop :=
  ∀ E : Run P.Step, E.st 0 = P.initConfig → E.GloballyFair →
    ∃ H, T H ∧ ∀ᶠ t in atTop, P.output (E.st t) = H

section lemmas

variable {P}

@[simp] theorem interact_st_left (C : Config V Q) (u v : V) :
    (P.interact C u v).st u = (P.δ (C.st u) (C.st v) (C.edge u v)).1 := by
  simp [interact]

@[simp] theorem interact_st_right (C : Config V Q) {u v : V} (h : u ≠ v) :
    (P.interact C u v).st v = (P.δ (C.st u) (C.st v) (C.edge u v)).2.1 := by
  simp [interact, h.symm]

theorem interact_st_other (C : Config V Q) {u v x : V} (hu : x ≠ u) (hv : x ≠ v) :
    (P.interact C u v).st x = C.st x := by
  simp [interact, hu, hv]

@[simp] theorem interact_edge_uv (C : Config V Q) (u v : V) :
    (P.interact C u v).edge u v = (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 := by
  simp [interact]

@[simp] theorem interact_edge_vu (C : Config V Q) (u v : V) :
    (P.interact C u v).edge v u = (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 := by
  simp [interact]

theorem interact_edge_other (C : Config V Q) {u v x y : V}
    (h : ¬((x = u ∧ y = v) ∨ (x = v ∧ y = u))) :
    (P.interact C u v).edge x y = C.edge x y := by
  simp only [interact, h, ite_false]

/-- An interaction whose rule is ineffective leaves the configuration unchanged. -/
theorem interact_eq_self (C : Config V Q) {u v : V}
    (h : P.δ (C.st u) (C.st v) (C.edge u v) = (C.st u, C.st v, C.edge u v)) :
    P.interact C u v = C := by
  ext x
  · simp only [interact, h]
    split_ifs <;> simp_all
  · simp only [interact, h]
    split_ifs with hxy
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact C.symm _ _
    · rfl

theorem step_of_ne {C : Config V Q} {u v : V} (h : u ≠ v) : P.Step C (P.interact C u v) :=
  ⟨u, v, h, rfl⟩

theorem reachable_of_ne {C : Config V Q} {u v : V} (h : u ≠ v) :
    P.Reachable C (P.interact C u v) :=
  Relation.ReflTransGen.single (step_of_ne h)

/-- Every configuration has a successor when there are two agents. -/
theorem step_total [Nontrivial V] (C : Config V Q) : ∃ C', P.Step C C' := by
  obtain ⟨u, v, h⟩ := exists_pair_ne V
  exact ⟨_, step_of_ne h⟩

end lemmas

/-- **Proof method for constructors.** If `S` is closed, the output is constant along every path
inside `S` and satisfies `T`, and `S` is reachable from every configuration reachable from the
initial one, then `P` constructs `T`. -/
theorem constructs_of_reach [Finite V] [Finite Q] {T : (⊤ : SimpleGraph V).Subgraph → Prop}
    (S : Set (Config V Q)) (hS : IsTrap P.Step S)
    (hout : ∀ C D, C ∈ S → P.Step C D → P.output D = P.output C)
    (hT : ∀ C ∈ S, T (P.output C))
    (hreach : ∀ C, P.Reachable P.initConfig C → ∃ D ∈ S, P.Reachable C D) :
    P.Constructs T := by
  intro E hE0 hfair
  have hev := hfair.eventually_mem hS (fun C hC => hreach C (hE0 ▸ hC))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hev
  refine ⟨P.output (E.st t₀), hT _ (ht₀ t₀ le_rfl), eventually_atTop.2 ⟨t₀, fun s hs => ?_⟩⟩
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ s hs ih => rw [hout _ _ (ht₀ s hs) (E.step s), ih]

/-- Globally fair executions exist (on at least two agents), so `Constructs` is never vacuous. -/
theorem exists_fair_execution [Finite V] [Finite Q] [Nontrivial V] :
    ∃ E : Run (P.Step (V := V)), E.st 0 = P.initConfig ∧ E.GloballyFair :=
  exists_globallyFair step_total _

/-- **Refutation method.** If from a reachable configuration `C`, every reachable configuration
can still reach two configurations with different outputs, then some globally fair execution does
not stabilize its output; in particular `P` constructs no graph class. -/
theorem not_constructs_of_unstable [Finite V] [Finite Q] [Nontrivial V]
    {T : (⊤ : SimpleGraph V).Subgraph → Prop} {C : Config V Q}
    (hC : P.Reachable P.initConfig C)
    (h : ∀ D, P.Reachable C D →
      ∃ A B, P.Reachable D A ∧ P.Reachable D B ∧ P.output A ≠ P.output B) :
    ¬ P.Constructs T := by
  intro hc
  obtain ⟨E, hE0, hfair, k, hk⟩ := exists_globallyFair_of_reach step_total hC
  obtain ⟨H, -, hH⟩ := hc E hE0 hfair
  obtain ⟨D, hD⟩ := exists_frequently_eq E.st
  obtain ⟨t, ht, hDt⟩ := frequently_atTop.1 hD k
  obtain ⟨A, B, hA, hB, hAB⟩ := h D (hk ▸ hDt ▸ E.reach_of_le ht)
  have hA' := ((hfair.frequently_of_reach hD hA).and_eventually hH).exists
  have hB' := ((hfair.frequently_of_reach hD hB).and_eventually hH).exists
  obtain ⟨_, rfl, hA''⟩ := hA'
  obtain ⟨_, rfl, hB''⟩ := hB'
  exact hAB (hA''.trans hB''.symm)

end Protocol

end NetworkConstructor

end Cslib
