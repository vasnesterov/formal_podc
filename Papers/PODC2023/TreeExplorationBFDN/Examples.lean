import Papers.PODC2023.TreeExplorationBFDN.Idle

/-!
# Concrete trees

Small rooted trees on `Fin (n+1)` given by a parent table, used for counterexamples and for the
non-vacuity checks.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

section Decidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ}

instance (c : Config V k) (x : V) : Decidable (IsOpen T c x) := by
  unfold IsOpen; infer_instance

instance (c : Config V k) (x : V) : Decidable (IsCand T c x) := by
  unfold IsCand; infer_instance

instance (act : Finset (Fin k)) (c : Config V k) (na : Fin k → V) (i : Fin k) :
    Decidable (ReanchorOK T act c na i) := by
  unfold ReanchorOK; split <;> infer_instance

instance (c : Config V k) (tgt : Fin k → V) (i : Fin k) (w : V) :
    Decidable (FreeDangling T c tgt i w) := by
  unfold FreeDangling; infer_instance

instance (act : Finset (Fin k)) (c : Config V k) (na tgt : Fin k → V) (i : Fin k) :
    Decidable (MoveOK T act c na tgt i) := by
  unfold MoveOK; split
  · split <;> infer_instance
  · infer_instance

instance (c : Config V k) : Decidable (Terminal T c) := by
  unfold Terminal; infer_instance

end Decidable

/-- The graph of a parent table. -/
def tableGraph {n : ℕ} (p : Fin (n + 1) → Fin (n + 1)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun a b => a ≠ 0 ∧ p a = b

instance {n : ℕ} (p : Fin (n + 1) → Fin (n + 1)) : DecidableRel (tableGraph p).Adj := by
  unfold tableGraph; infer_instance

/-- The rooted tree of a parent table with given depths (root `0`). -/
def tableTree {n : ℕ} (p : Fin (n + 1) → Fin (n + 1)) (dp : Fin (n + 1) → ℕ) (h0 : p 0 = 0)
    (hd0 : dp 0 = 0) (hdp : ∀ v, v ≠ 0 → dp (p v) + 1 = dp v) : (tableGraph p).RootedTree where
  root := 0
  parent := p
  depth := dp
  parent_root := h0
  depth_root := hd0
  depth_parent := hdp
  adj_parent := by
    intro v hv
    show (SimpleGraph.fromRel fun a b => a ≠ 0 ∧ p a = b).Adj v (p v)
    rw [fromRel_adj]
    refine ⟨fun h => ?_, Or.inl ⟨hv, rfl⟩⟩
    have := hdp v hv; rw [← h] at this; omega

/-- The star with two leaves: root `0`, leaves `1`, `2`. -/
def star3 : (tableGraph ![(0 : Fin 3), 0, 0]).RootedTree :=
  tableTree ![0, 0, 0] ![0, 1, 1] rfl rfl (by decide)

/-- The tree of the Claim 1 counterexample: root `0` with children `1`, `2`; a path
`1 – 3 – 5 – 6` and a path `2 – 4` (depth 4). -/
def claim1Tree : (tableGraph ![(0 : Fin 7), 0, 0, 1, 2, 3, 5]).RootedTree :=
  tableTree ![0, 0, 0, 1, 2, 3, 5] ![0, 1, 1, 2, 2, 3, 4] rfl rfl (by decide)

end Podc.TreeExplorationBFDN
