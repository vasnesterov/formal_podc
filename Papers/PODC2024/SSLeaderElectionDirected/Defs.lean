import Mathlib
import Cslib.Computability.Distributed.SelfStabilization.Daemon
import Cslib.Foundations.Combinatorics.Digraph.Walk

/-!
# Self-stabilization (Definition 1) and the maximum ancestor distance

Altisen, Cournier, Defalque, Devismes, *On Self-stabilizing Leader Election in Directed Networks*,
PODC 2024 (HAL hal-04434345v4).

An arc `G.Adj q p` means that `q` is a *predecessor* of `p` (`p` reads `q`); the ancestors of `p`
are the `q` with `G.Reachable q p`, and `‖q, p‖ ≤ n` is `Relation.RelatesWithinSteps G.Adj q p n`.

* `MADLe G α` : every ancestor of every node is at distance `≤ α`, i.e. `α ≥ MAD` (the maximum
  ancestor distance); `mad G` is the least such `α`.
* `SelfStab Exec SP` : Definition 1 — a *nonempty* set of legitimate configurations exists for the
  class `Exec` (a daemon) and the specification `SP`. It is the library notion
  `Cslib.SelfStabilization.SelfStabilizing` (`selfStab_iff`).
-/

namespace Papers.PODC2024.SSLeaderElectionDirected

open Relation Cslib.SelfStabilization

variable {V Q : Type*}

/-- Definition 1 (self-stabilization) for a class of executions `Exec` and a specification `SP`
(a predicate on executions in `Ext∞` form): some nonempty set `L` of configurations is reached by
every execution and every execution starting in `L` satisfies `SP`. -/
def SelfStab (Exec : (ℕ → V → Q) → Prop) (SP : (ℕ → V → Q) → Prop) : Prop :=
  ∃ L : Set (V → Q), L.Nonempty ∧ IsLegitimate Exec SP L

/-- Definition 1 is the library's self-stabilization (the nonemptiness of `L` is automatic). -/
theorem selfStab_iff [Nonempty (V → Q)] {Exec : Set (ℕ → V → Q)} {SP : (ℕ → V → Q) → Prop} :
    SelfStab Exec SP ↔ SelfStabilizing Exec SP :=
  selfStabilizing_iff_exists_nonempty.symm

variable (G : Digraph V)

/-- `α ≥ MAD`: every ancestor `q` of every node `p` satisfies `‖q, p‖ ≤ α`. -/
def MADLe (α : ℕ) : Prop := ∀ q p, G.Reachable q p → RelatesWithinSteps G.Adj q p α

variable {G}

theorem MADLe.mono {α β : ℕ} (h : MADLe G α) (hαβ : α ≤ β) : MADLe G β :=
  fun q p hqp => RelatesWithinSteps.mono hαβ (h q p hqp)

/-- Paths in a finite digraph can be shortened to length `≤ |V| - 1`. -/
theorem madLe_card [Fintype V] : MADLe G (Fintype.card V - 1) := fun _ _ h =>
  h.relatesWithinSteps

/-- The maximum ancestor distance `MAD` of a finite digraph: the least `α` with `MADLe G α`. -/
noncomputable def mad [Fintype V] (G : Digraph V) : ℕ :=
  @Nat.find (fun α => MADLe G α) (Classical.decPred _) ⟨_, madLe_card⟩

theorem madLe_mad [Fintype V] : MADLe G (mad G) :=
  @Nat.find_spec (fun α => MADLe G α) (Classical.decPred _) ⟨_, madLe_card⟩

theorem mad_le [Fintype V] {α : ℕ} (h : MADLe G α) : mad G ≤ α :=
  @Nat.find_min' (fun α => MADLe G α) (Classical.decPred _) ⟨_, madLe_card⟩ _ h

theorem madLe_iff [Fintype V] {α : ℕ} : MADLe G α ↔ mad G ≤ α :=
  ⟨mad_le, fun h => madLe_mad.mono h⟩

end Papers.PODC2024.SSLeaderElectionDirected
