import Papers.PODC2023.PPDoubleExpThresholds.Stable
import Podc.Computability.Distributed.PopulationProtocols.Multiset.Basic

/-!
# Population protocols (Section 3) and almost self-stabilisation (Definition 7)

A population protocol is `PP = (Q, δ, I, O)` with a finite set of states `Q`, transitions
`δ ⊆ Q⁴` (written `(q, r ↦ q', r')`, reusing `Cslib.PopulationProtocol.Transition`), input states
`I ⊆ Q` and accepting states `O ⊆ Q`. Configurations are nonempty multisets of states. We write
`C → C'` if `C = C'` or some transition fires (so `→` is left-total). A configuration has output
`true` if all its agents are in `O`, output `false` if none is, and no output otherwise.

`PP` decides `φ : ℕ^I → Bool` if every fair run (global fairness, Section 3) from an initial
configuration `C ∈ ℕ^I`, `|C| > 0`, stabilises to `φ(C)`. Theorems 1 and 2 are about *unary*
predicates of the number of agents, `DecidesCount`.
-/

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem

/-- A population protocol `(Q, δ, I, O)` (Section 3). -/
structure PProtocol (Q : Type*) where
  /-- The transitions `(q, r ↦ q', r')`. -/
  δ : Set (Transition Q)
  /-- Input states. -/
  I : Set Q
  /-- Accepting states. -/
  O : Set Q

namespace PProtocol

variable {Q : Type*} [DecidableEq Q] (PP : PProtocol Q)

/-- `C → C'`: either `C = C'`, or a transition of `δ` fires. -/
def Step (C C' : Multiset Q) : Prop := C = C' ∨ MStep PP.δ C C'

open Classical in
/-- The output of a configuration: `true` if all agents are accepting, `false` if none is,
undefined otherwise. -/
noncomputable def out (C : Multiset Q) : Option Bool :=
  if ∀ q ∈ C, q ∈ PP.O then some true else if ∀ q ∈ C, q ∉ PP.O then some false else none

/-- `C` is an initial configuration: nonempty and only input states. -/
def IsInitial (C : Multiset Q) : Prop := 0 < Multiset.card C ∧ ∀ q ∈ C, q ∈ PP.I

/-- `PP` decides `φ`: every fair run from an initial configuration `C` stabilises to `φ(C)`. -/
def Decides (φ : Multiset Q → Bool) : Prop :=
  ∀ E : Run PP.Step, PP.IsInitial (E.st 0) → E.GloballyFair →
    StabilisesTo PP.out E (φ (E.st 0))

/-- `PP` decides the unary predicate `φ` of the number of agents. -/
def DecidesCount (φ : ℕ → Bool) : Prop := PP.Decides fun C => φ (Multiset.card C)

open Classical in
/-- **Definition 7** (almost self-stabilising), for a protocol deciding the unary predicate `φ`:
every fair run started at a configuration `C ∈ ℕ^Q` with `C(I) ≥ |Q|` stabilises to `φ(|C|)`. -/
def AlmostSelfStabilising [Fintype Q] (φ : ℕ → Bool) : Prop :=
  ∀ E : Run PP.Step, Fintype.card Q ≤ Multiset.card ((E.st 0).filter (· ∈ PP.I)) →
    E.GloballyFair → StabilisesTo PP.out E (φ (Multiset.card (E.st 0)))

end PProtocol

end Podc.PPDoubleExpThresholds
