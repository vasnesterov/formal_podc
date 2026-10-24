import Podc.Computability.Distributed.NetworkConstructors.Graph
import Mathlib

/-!
# Network construction problems (Section 3.2)

The target graph classes of Michail–Spirakis, as predicates on the output subgraph
`H : (⊤ : SimpleGraph V).Subgraph` of a configuration (vertices: agents in output states; edges:
active edges between them). Degrees are `(H.neighborSet v).ncard`; `n = Fintype.card V`.
-/

namespace Podc.NetworkConstructors

variable {V : Type*} [Fintype V]

/-- *Global line* (spanning line): a connected graph on all `n` agents in which 2 nodes have degree
1 and `n − 2` nodes have degree 2. -/
def IsSpanningLine (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  H.verts = Set.univ ∧ H.Connected ∧
    ∃ a b, a ≠ b ∧ (H.neighborSet a).ncard = 1 ∧ (H.neighborSet b).ncard = 1 ∧
      ∀ v, v ≠ a → v ≠ b → (H.neighborSet v).ncard = 2

/-- *Cycle cover*: every output agent has degree 2 (a collection of node-disjoint cycles spanning
the output agents). -/
def IsCycleCover (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  ∀ v ∈ H.verts, (H.neighborSet v).ncard = 2

/-- *Global star* (spanning star): a connected graph on all `n` agents in which one node (the
center) has degree `n − 1` and the `n − 1` other nodes have degree 1. -/
def IsSpanningStar (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  H.verts = Set.univ ∧ H.Connected ∧
    ∃ c, (H.neighborSet c).ncard = Fintype.card V - 1 ∧ ∀ v ≠ c, (H.neighborSet v).ncard = 1

/-- *Global ring* (spanning ring): a connected graph on all `n` agents in which every node has
degree 2. -/
def IsSpanningRing (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  H.verts = Set.univ ∧ H.Connected ∧ ∀ v, (H.neighborSet v).ncard = 2

/-- The conclusion of Theorem 12 (Protocol kRC): a connected spanning network in which at least
`n − k + 1` nodes have degree `k` and each of the remaining `l ≤ k − 1` nodes (the set `D`) has
degree at least `l − 1` and at most `k − 1`. -/
def IsAlmostRegular (k : ℕ) (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  H.verts = Set.univ ∧ H.Connected ∧
    ∃ D : Finset V, D.card ≤ k - 1 ∧ (∀ v ∉ D, (H.neighborSet v).ncard = k) ∧
      ∀ v ∈ D, D.card - 1 ≤ (H.neighborSet v).ncard ∧ (H.neighborSet v).ncard ≤ k - 1

/-- *`c`-cliques*: the output is a disjoint union of `⌊n/c⌋` cliques of order `c` each: it has
`c ⌊n/c⌋` vertices, adjacency is transitive (off the diagonal), and every vertex has degree
`c − 1`. -/
def IsCliquePartition (c : ℕ) (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  H.verts.ncard = c * (Fintype.card V / c) ∧
    (∀ v ∈ H.verts, (H.neighborSet v).ncard = c - 1) ∧
    ∀ u v w, H.Adj u v → H.Adj v w → u ≠ w → H.Adj u w

open Cslib.NetworkConstructor in
/-- A spanning line from a configuration whose active graph is a tree with all degrees in
`{1, 2}` (protocols in which every state is an output state). -/
theorem isSpanningLine_output [DecidableEq V] {Q : Type*} {P : Protocol Q} (hout : ∀ q, P.out q = true)
    {C : Config V Q} (hconn : C.active.Connected)
    (hacyc : C.active.IsAcyclic) (hdeg : ∀ v, C.deg v = 1 ∨ C.deg v = 2) :
    IsSpanningLine (P.output C) := by
  have htree : C.active.IsTree := ⟨hconn, hacyc⟩
  have hsum : ∑ v, C.deg v + 2 = 2 * Fintype.card V := by
    have h := htree.card_edgeFinset
    simp_rw [Config.deg_eq_degree]
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    omega
  set A := Finset.univ.filter fun v => C.deg v = 1 with hA
  have hAcard : A.card = 2 := by
    have : ∀ v, C.deg v + (if C.deg v = 1 then 1 else 0) = 2 := by
      intro v; rcases hdeg v with h | h <;> simp [h]
    have h2 : ∑ v, (C.deg v + (if C.deg v = 1 then 1 else 0)) = 2 * Fintype.card V := by
      rw [Finset.sum_congr rfl (fun v _ => this v)]; simp [mul_comm]
    rw [Finset.sum_add_distrib, Finset.sum_boole] at h2
    simp only [Nat.cast_id] at h2
    rw [hA]
    omega
  obtain ⟨a, b, hab, hAab⟩ := Finset.card_eq_two.1 hAcard
  have hmem : ∀ v, C.deg v = 1 ↔ v = a ∨ v = b := by
    intro v
    have := congrArg (v ∈ ·) hAab
    simpa [hA] using this
  refine ⟨Protocol.output_verts_univ hout C, (Protocol.output_connected_iff hout C).2 hconn,
    a, b, hab, ?_, ?_, fun v hva hvb => ?_⟩
  · rw [Protocol.ncard_neighborSet_output hout]; exact (hmem a).2 (.inl rfl)
  · rw [Protocol.ncard_neighborSet_output hout]; exact (hmem b).2 (.inr rfl)
  · rw [Protocol.ncard_neighborSet_output hout]
    exact (hdeg v).resolve_left fun h => by rcases (hmem v).1 h with h | h <;> contradiction

end Podc.NetworkConstructors
