import Cslib.Computability.Distributed.PopulationProtocols.Nondet
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Population protocols on graphs (Chen–Chen, PODC 2020, Section 2)

Hsueh-Ping Chen and Ho-Lin Chen, *Self-Stabilizing Leader Election in Regular Graphs*,
PODC 2020, Section 2.

* A protocol (`GProtocol Q`, the shared nondeterministic model `Cslib.PopulationProtocol.NProtocol`
  of `Cslib.Computability.Distributed.PopulationProtocols.Nondet`) has a **nondeterministic** transition function
  `δ : Q → Q → Set (Q × Q)`: `(r, s) ∈ δ p q` iff an initiator in state `p` and a responder in state
  `q` may move to `(r, s)`. Randomized rules of the paper ("`u ← RandState`", "randomly do …") are
  modelled by their support, which is all that matters under global fairness and, for finite state
  spaces, for "probability 1" statements (`Cslib.Computability.Distributed.SelfStabilization.Markov`).
* A configuration is `V → Q`; a step lets two **adjacent** nodes `u, v` of the communication graph
  `G` interact, `u` as initiator, `v` as responder (`GProtocol.Step`, i.e.
  `NProtocol.StepOn G.Adj`). Both orders are scheduled. Runs and global fairness are those of
  `Cslib.TransitionSystem`.
* `OutputStable`, `ValidStable` (output-stable with exactly one leader), `SolvesSSLE` (paper's
  definition: every globally fair execution reaches a valid output-stable configuration), and
  `SelfStab` (from every configuration a valid output-stable configuration is reachable).
* `solvesSSLE_iff`: `SolvesSSLE ↔ SelfStab` (finite state space, at least one edge), and
  `selfStab_iff_selfStabilizes`: `SelfStab` is `Cslib.TransitionSystem.SelfStabilizes` for the set
  of valid output-stable configurations.
* `derc_lemma`: Lemma 2.1 (detect-error-and-random-change), with the hypotheses that the paper
  states only in the surrounding text made explicit.
-/

open Finset Cslib.PopulationProtocol Cslib.TransitionSystem

namespace SSLERegular

export Cslib.PopulationProtocol (upd upd_left upd_right upd_other)

namespace TS

export Cslib.TransitionSystem (Run IsTrap)

/-- A predicate on a finite type as a finset. -/
noncomputable def setOf {X : Type*} [Fintype X] (S : X → Prop) : Finset X := by
  classical exact Finset.univ.filter S

open Classical in
lemma setOf_eq_toFinset {X : Type*} [Fintype X] (S : X → Prop) :
    setOf S = {x | S x}.toFinset := by
  simp [setOf]

end TS

/-- A population protocol with nondeterministic (support of randomized) transitions. -/
abbrev GProtocol := Cslib.PopulationProtocol.NProtocol

variable {V Q : Type*} [DecidableEq V]

namespace GProtocol

export Cslib.PopulationProtocol (numLeaders)

variable (G : SimpleGraph V) (P : GProtocol Q)

/-- One interaction of two adjacent nodes (`u` initiator, `v` responder). -/
abbrev Step : (V → Q) → (V → Q) → Prop := P.StepOn G.Adj

/-- Reachability. -/
abbrev Reachable : (V → Q) → (V → Q) → Prop := Reach (P.Step G)

/-- The output never changes again (the shared `NProtocol.OutputStable` along the edges of
`G`). -/
abbrev OutputStable (out : Q → Bool) (C : V → Q) : Prop :=
  NProtocol.OutputStable P G.Adj out C

/-- Valid output-stable configuration: output-stable with exactly one leader. -/
def ValidStable [Fintype V] (out : Q → Bool) (C : V → Q) : Prop :=
  P.OutputStable G out C ∧ numLeaders out C = 1

/-- **SSLE (paper's definition, Section 2.1–2.2).** From any initial configuration, every globally
fair execution reaches a valid output-stable configuration. -/
def SolvesSSLE [Fintype V] (out : Q → Bool) : Prop :=
  ∀ E : TS.Run (P.Step G), E.GloballyFair → ∃ T, P.ValidStable G out (E.st T)

/-- Reachability form: from every configuration a valid output-stable one is reachable. -/
def SelfStab [Fintype V] (out : Q → Bool) : Prop :=
  ∀ C : V → Q, ∃ D, P.ValidStable G out D ∧ P.Reachable G C D

variable {G P}

lemma validStable_closed [Fintype V] {out : Q → Bool} :
    IsTrap (P.Step G) (P.ValidStable G out) := by
  intro C D hC hCD
  refine ⟨NProtocol.isTrap_outputStable out hC.1 hCD, ?_⟩
  rw [hC.1.numLeaders_eq (Relation.ReflTransGen.single hCD), hC.2]

/-- `SelfStab` is self-stabilization (`Cslib.TransitionSystem.SelfStabilizes`) to the closed set
of valid output-stable configurations. -/
lemma selfStab_iff_selfStabilizes [Fintype V] {out : Q → Bool} :
    P.SelfStab G out ↔ SelfStabilizes (P.Step G) (P.ValidStable G out) :=
  (selfStabilizes_iff_of_isTrap validStable_closed).symm

/-- `SolvesSSLE` (global fairness) is equivalent to `SelfStab` (reachability), for finite state
spaces, nonempty transition sets and graphs with at least one edge. -/
theorem solvesSSLE_iff [Fintype V] [Finite Q] (hedge : ∃ u v, G.Adj u v)
    (hδ : ∀ p q, (P.δ p q).Nonempty) (out : Q → Bool) :
    P.SolvesSSLE G out ↔ P.SelfStab G out :=
  globallyFair_iff_reach (NProtocol.exists_stepOn hedge hδ) validStable_closed

/-- **Lemma 2.1 (Detect-Error-and-Random-Change Lemma)**, with explicit hypotheses.
`err` is the set of error-detected configurations. The paper's two conditions are `hcases`; the
facts it uses but states only in the surrounding prose are `hex` (a valid output-stable
configuration exists, Lemma 3.1/4.1) and `herr` (an error-detected configuration can reach every
configuration). -/
theorem derc_lemma [Fintype V] {out : Q → Bool} (err : (V → Q) → Prop)
    (hex : ∃ C, P.ValidStable G out C) (herr : ∀ C, err C → ∀ D, P.Reachable G C D)
    (hcases : ∀ C, ¬ P.ValidStable G out C →
      (∃ D, err D ∧ P.Reachable G C D) ∨ ∃ D, P.ValidStable G out D ∧ P.Reachable G C D) :
    P.SelfStab G out :=
  exists_reach_of_err (fun C hC => hex.imp fun E hE => ⟨hE, herr C hC E⟩) hcases

/-- Variant of Lemma 2.1 where error-detected configurations need only reach *some* valid
output-stable configuration. -/
theorem derc_lemma' [Fintype V] {out : Q → Bool} (err : (V → Q) → Prop)
    (herr : ∀ C, err C → ∃ D, P.ValidStable G out D ∧ P.Reachable G C D)
    (hcases : ∀ C, ¬ P.ValidStable G out C →
      (∃ D, err D ∧ P.Reachable G C D) ∨ ∃ D, P.ValidStable G out D ∧ P.Reachable G C D) :
    P.SelfStab G out :=
  exists_reach_of_err (err := err) herr hcases

/-- If no valid output-stable configuration is reachable from `C`, the protocol does not solve
SSLE: some globally fair execution from `C` never reaches one. -/
theorem not_solvesSSLE_of [Fintype V] [Finite Q] (hedge : ∃ u v, G.Adj u v)
    (hδ : ∀ p q, (P.δ p q).Nonempty) {out : Q → Bool} (C : V → Q)
    (hC : ∀ D, P.Reachable G C D → ¬ P.ValidStable G out D) :
    ∃ E : TS.Run (P.Step G), E.st 0 = C ∧ E.GloballyFair ∧ ∀ t, ¬ P.ValidStable G out (E.st t) :=
  exists_globallyFair_forall_not_mem (NProtocol.exists_stepOn hedge hδ) hC

end GProtocol

end SSLERegular
