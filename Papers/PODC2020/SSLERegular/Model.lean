import Papers.PODC2020.SSLERegular.Fairness
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Population protocols on graphs (Chen–Chen, PODC 2020, Section 2)

Hsueh-Ping Chen and Ho-Lin Chen, *Self-Stabilizing Leader Election in Regular Graphs*,
PODC 2020, Section 2.

* A protocol (`GProtocol Q`) has a **nondeterministic** transition function
  `δ : Q → Q → Set (Q × Q)`: `(r, s) ∈ δ p q` iff an initiator in state `p` and a responder in state
  `q` may move to `(r, s)`. Randomized rules of the paper ("`u ← RandState`", "randomly do …") are
  modelled by their support, which is all that matters under global fairness and, for finite state
  spaces, for "probability 1" statements (`Fairness.lean`).
* A configuration is `V → Q`; a step lets two **adjacent** nodes `u, v` of the communication graph
  `G` interact, `u` as initiator, `v` as responder (`GProtocol.Step`). Both orders are scheduled.
* `OutputStable`, `ValidStable` (output-stable with exactly one leader), `SolvesSSLE` (paper's
  definition: every globally fair execution reaches a valid output-stable configuration), and
  `SelfStab` (from every configuration a valid output-stable configuration is reachable).
* `solvesSSLE_iff`: `SolvesSSLE ↔ SelfStab` (finite state space, at least one edge).
* `derc_lemma`: Lemma 2.1 (detect-error-and-random-change), with the hypotheses that the paper
  states only in the surrounding text made explicit.
-/

open Finset

namespace SSLERegular

-- CSLib candidate
/-- A population protocol with nondeterministic (support of randomized) transitions. -/
structure GProtocol (Q : Type*) where
  /-- Possible outcomes `(initiator, responder)` of an interaction. -/
  δ : Q → Q → Set (Q × Q)

variable {V Q : Type*} [DecidableEq V]

/-- The configuration after initiator `u` and responder `v` take the states `o`. -/
def upd (C : V → Q) (u v : V) (o : Q × Q) : V → Q :=
  Function.update (Function.update C u o.1) v o.2

lemma upd_left (C : V → Q) {u v : V} (h : u ≠ v) (o : Q × Q) : upd C u v o u = o.1 := by
  simp [upd, h]

@[simp] lemma upd_right (C : V → Q) (u v : V) (o : Q × Q) : upd C u v o v = o.2 := by
  simp [upd]

lemma upd_other (C : V → Q) {u v x : V} (hu : x ≠ u) (hv : x ≠ v) (o : Q × Q) :
    upd C u v o x = C x := by
  simp [upd, hu, hv]

namespace GProtocol

variable (G : SimpleGraph V) (P : GProtocol Q)

/-- One interaction of two adjacent nodes (`u` initiator, `v` responder). -/
def Step (C D : V → Q) : Prop :=
  ∃ u v, G.Adj u v ∧ ∃ o ∈ P.δ (C u) (C v), D = upd C u v o

/-- Reachability. -/
abbrev Reachable : (V → Q) → (V → Q) → Prop := TS.Reach (P.Step G)

/-- The output never changes again. -/
def OutputStable (out : Q → Bool) (C : V → Q) : Prop :=
  ∀ D, P.Reachable G C D → ∀ v, out (D v) = out (C v)

/-- Number of leaders. -/
def numLeaders [Fintype V] (out : Q → Bool) (C : V → Q) : ℕ :=
  (Finset.univ.filter fun v => out (C v) = true).card

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

lemma outputStable_closed {out : Q → Bool} :
    TS.Closed (P.Step G) (P.OutputStable G out) := by
  intro C D hC hCD E hDE v
  rw [hC E (Relation.ReflTransGen.head hCD hDE) v, hC D (Relation.ReflTransGen.single hCD) v]

lemma numLeaders_eq_of_outputStable [Fintype V] {out : Q → Bool} {C D : V → Q}
    (hC : P.OutputStable G out C) (h : P.Reachable G C D) : numLeaders out D = numLeaders out C := by
  unfold numLeaders
  congr 1
  ext v
  simp [hC D h v]

lemma validStable_closed [Fintype V] {out : Q → Bool} :
    TS.Closed (P.Step G) (P.ValidStable G out) := by
  intro C D hC hCD
  refine ⟨outputStable_closed C D hC.1 hCD, ?_⟩
  rw [numLeaders_eq_of_outputStable hC.1 (Relation.ReflTransGen.single hCD), hC.2]

lemma step_total (hedge : ∃ u v, G.Adj u v) (hδ : ∀ p q, (P.δ p q).Nonempty) (C : V → Q) :
    ∃ D, P.Step G C D := by
  obtain ⟨u, v, huv⟩ := hedge
  obtain ⟨o, ho⟩ := hδ (C u) (C v)
  exact ⟨_, u, v, huv, o, ho, rfl⟩

-- CSLib candidate
/-- `SolvesSSLE` (global fairness) is equivalent to `SelfStab` (reachability), for finite state
spaces, nonempty transition sets and graphs with at least one edge. -/
theorem solvesSSLE_iff [Fintype V] [Finite Q] (hedge : ∃ u v, G.Adj u v)
    (hδ : ∀ p q, (P.δ p q).Nonempty) (out : Q → Bool) :
    P.SolvesSSLE G out ↔ P.SelfStab G out :=
  TS.fair_iff_reach (step_total hedge hδ) validStable_closed

-- CSLib candidate
/-- **Lemma 2.1 (Detect-Error-and-Random-Change Lemma)**, with explicit hypotheses.
`err` is the set of error-detected configurations. The paper's two conditions are `hcases`; the
facts it uses but states only in the surrounding prose are `hex` (a valid output-stable
configuration exists, Lemma 3.1/4.1) and `herr` (an error-detected configuration can reach every
configuration). -/
theorem derc_lemma [Fintype V] {out : Q → Bool} (err : (V → Q) → Prop)
    (hex : ∃ C, P.ValidStable G out C) (herr : ∀ C, err C → ∀ D, P.Reachable G C D)
    (hcases : ∀ C, ¬ P.ValidStable G out C →
      (∃ D, err D ∧ P.Reachable G C D) ∨ ∃ D, P.ValidStable G out D ∧ P.Reachable G C D) :
    P.SelfStab G out := by
  intro C
  by_cases hC : P.ValidStable G out C
  · exact ⟨C, hC, Relation.ReflTransGen.refl⟩
  · rcases hcases C hC with ⟨D, hD, hCD⟩ | h
    · obtain ⟨E, hE⟩ := hex
      exact ⟨E, hE, hCD.trans (herr D hD E)⟩
    · exact h

/-- Variant of Lemma 2.1 where error-detected configurations need only reach *some* valid
output-stable configuration. -/
theorem derc_lemma' [Fintype V] {out : Q → Bool} (err : (V → Q) → Prop)
    (herr : ∀ C, err C → ∃ D, P.ValidStable G out D ∧ P.Reachable G C D)
    (hcases : ∀ C, ¬ P.ValidStable G out C →
      (∃ D, err D ∧ P.Reachable G C D) ∨ ∃ D, P.ValidStable G out D ∧ P.Reachable G C D) :
    P.SelfStab G out := by
  intro C
  by_cases hC : P.ValidStable G out C
  · exact ⟨C, hC, Relation.ReflTransGen.refl⟩
  · rcases hcases C hC with ⟨D, hD, hCD⟩ | h
    · obtain ⟨E, hE, hDE⟩ := herr D hD
      exact ⟨E, hE, hCD.trans hDE⟩
    · exact h

/-- If no valid output-stable configuration is reachable from `C`, the protocol does not solve
SSLE: some globally fair execution from `C` never reaches one. -/
theorem not_solvesSSLE_of [Fintype V] [Finite Q] (hedge : ∃ u v, G.Adj u v)
    (hδ : ∀ p q, (P.δ p q).Nonempty) {out : Q → Bool} (C : V → Q)
    (hC : ∀ D, P.Reachable G C D → ¬ P.ValidStable G out D) :
    ∃ E : TS.Run (P.Step G), E.st 0 = C ∧ E.GloballyFair ∧ ∀ t, ¬ P.ValidStable G out (E.st t) := by
  obtain ⟨E, hE0, hE⟩ := TS.exists_globallyFair (step_total hedge hδ) C
  exact ⟨E, hE0, hE, fun t => hC _ (hE0 ▸ E.reach_of_le (Nat.zero_le t))⟩

end GProtocol

end SSLERegular
