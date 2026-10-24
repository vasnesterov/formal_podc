/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/NetworkConstructors/Graph.lean
import Podc.Computability.Distributed.NetworkConstructors.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Active graphs of network constructors

Tools for the reachability proofs of network constructors (Michail–Spirakis, PODC 2014):

* `TransitionSystem.exists_reach_of_measure`: reaching a goal by decreasing a well-founded measure
  while keeping an invariant (the shape of all "from every reachable configuration we can reach a
  stable one" arguments).
* `Config.deg`: the number of active edges at an agent, and how one interaction changes the active
  graph (`interact_active_*`) and the degrees (`deg_interact_*`).
* Reachability in `G ⊔ edge u v` (`reachable_sup_edge_iff`) and in `G \ edge u v`
  (`Reachable.sdiff_edge`): what happens to connected components when one edge is activated or
  deactivated.
-/

open Cslib.TransitionSystem

namespace Cslib

namespace TransitionSystem

variable {X α : Type*} {R : X → X → Prop}

/-- Reach a configuration satisfying `good` by repeatedly decreasing a well-founded measure while
preserving an invariant. -/
theorem exists_reach_of_measure [Preorder α] [WellFoundedLT α] (Inv good : X → Prop) (f : X → α)
    (h : ∀ x, Inv x → ¬ good x → ∃ y, Reach R x y ∧ Inv y ∧ f y < f x) :
    ∀ x, Inv x → ∃ y, Reach R x y ∧ Inv y ∧ good y := by
  intro x
  induction hx : f x using WellFoundedLT.induction generalizing x with
  | _ a ih =>
    intro hinv
    by_cases hg : good x
    · exact ⟨x, .refl, hinv, hg⟩
    · obtain ⟨y, hxy, hy, hlt⟩ := h x hinv hg
      obtain ⟨z, hyz, hz, hgz⟩ := ih (f y) (hx ▸ hlt) y rfl hy
      exact ⟨z, hxy.trans hyz, hz, hgz⟩

end TransitionSystem

end Cslib

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v x y : V}

/-- Reachability after adding the edge `uv`. -/
theorem reachable_sup_edge_iff :
    (G ⊔ edge u v).Reachable x y ↔ G.Reachable x y ∨ (G.Reachable x u ∧ G.Reachable v y) ∨
      (G.Reachable x v ∧ G.Reachable u y) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .inl .rfl
    | @cons a b c hab _ ih =>
      rcases (sup_adj _ _ _ _).1 hab with hab | hab
      · have hab' : G.Reachable a b := hab.reachable
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl (hab'.trans h)
        · exact .inr (.inl ⟨hab'.trans h1, h2⟩)
        · exact .inr (.inr ⟨hab'.trans h1, h2⟩)
      · rw [edge_adj] at hab
        rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact .inr (.inl ⟨.rfl, h⟩)
          · exact .inr (.inl ⟨.rfl, h2⟩)
          · exact .inl h2
        · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact .inr (.inr ⟨.rfl, h⟩)
          · exact .inl h2
          · exact .inr (.inr ⟨.rfl, h2⟩)
  · have hle : G ≤ G ⊔ edge u v := le_sup_left
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono hle
    · by_cases huv : u = v
      · subst huv; exact (h1.trans h2).mono hle
      · have : (G ⊔ edge u v).Adj u v := (sup_adj _ _ _ _).2 (.inr ((edge_adj _ _ _ _).2 ⟨.inl ⟨rfl, rfl⟩, huv⟩))
        exact (h1.mono hle).trans (this.reachable.trans (h2.mono hle))
    · by_cases huv : u = v
      · subst huv; exact (h1.trans h2).mono hle
      · have : (G ⊔ edge u v).Adj v u := (sup_adj _ _ _ _).2 (.inr ((edge_adj _ _ _ _).2 ⟨.inr ⟨rfl, rfl⟩, Ne.symm huv⟩))
        exact (h1.mono hle).trans (this.reachable.trans (h2.mono hle))

/-- After deleting the edge `uv`, a vertex that was connected to `y` is still connected to `y`,
or to `u`, or to `v`. -/
theorem Reachable.sdiff_edge (h : G.Reachable x y) :
    (G \ edge u v).Reachable x y ∨ (G \ edge u v).Reachable x u ∨
      (G \ edge u v).Reachable x v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .inl .rfl
  | @cons a b c hab _ ih =>
    by_cases he : (edge u v).Adj a b
    · rw [edge_adj] at he
      rcases he.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact .inr (.inl .rfl)
      · exact .inr (.inr .rfl)
    · have hab' : (G \ edge u v).Reachable a b := ((sdiff_adj _ _ _ _).2 ⟨hab, he⟩).reachable
      rcases ih with h | h | h
      · exact .inl (hab'.trans h)
      · exact .inr (.inl (hab'.trans h))
      · exact .inr (.inr (hab'.trans h))

end SimpleGraph

namespace Cslib.NetworkConstructor

variable {V Q : Type*}

namespace Config

variable [Fintype V] [DecidableEq V]

/-- The degree of an agent: the number of active edges at it. -/
def deg (C : Config V Q) (u : V) : ℕ := (Finset.univ.filter fun v => v ≠ u ∧ C.edge u v = true).card

instance (C : Config V Q) : DecidableRel C.active.Adj := fun _ _ => by
  simp only [active_adj]; infer_instance

theorem deg_eq_degree (C : Config V Q) (u : V) : C.deg u = C.active.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, deg]
  congr 1
  ext v
  simp [ne_comm]

end Config

namespace Protocol

variable [DecidableEq V] {P : Protocol Q} {C : Config V Q} {u v : V}

theorem interact_active_of_edge_eq (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = C.edge u v) :
    (P.interact C u v).active = C.active := by
  ext x y
  simp only [Config.active_adj]
  by_cases hxy : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [h]
    · simp [h, C.symm x y]
  · rw [interact_edge_other C hxy]

theorem interact_active_of_edge_true (huv : u ≠ v)
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = true) :
    (P.interact C u v).active = C.active ⊔ SimpleGraph.edge u v := by
  ext x y
  simp only [Config.active_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  by_cases hxy : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [h, huv]
    · simp [h, huv.symm]
  · rw [interact_edge_other C hxy]
    tauto

theorem interact_active_of_edge_false
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = false) :
    (P.interact C u v).active = C.active \ SimpleGraph.edge u v := by
  ext x y
  simp only [Config.active_adj, SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
  by_cases hxy : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [h]; tauto
    · simp [h, C.symm x y]; tauto
  · rw [interact_edge_other C hxy]
    tauto

theorem interact_edge_of_edge_eq (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = C.edge u v) :
    (P.interact C u v).edge = C.edge := by
  ext x y
  by_cases hxy : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [h]
    · simp [h, C.symm x y]
  · rw [interact_edge_other C hxy]

variable [Fintype V]

theorem deg_interact_other {x : V} (hu : x ≠ u) (hv : x ≠ v) :
    (P.interact C u v).deg x = C.deg x := by
  unfold Config.deg
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [interact_edge_other C (by tauto)]

theorem deg_interact_of_edge_eq {x : V}
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = C.edge u v) :
    (P.interact C u v).deg x = C.deg x := by
  simp only [Config.deg, interact_edge_of_edge_eq h]

/-- Activating an inactive edge `uv` increases the degrees of `u` and `v` by one. -/
theorem deg_interact_activate_left (huv : u ≠ v) (h0 : C.edge u v = false)
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = true) :
    (P.interact C u v).deg u = C.deg u + 1 := by
  unfold Config.deg
  rw [← Finset.card_insert_of_notMem (a := v) (by simp [h0])]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hy : y = v
  · subst hy; simp [h, huv.symm]
  · rw [interact_edge_other C (by tauto)]
    tauto

theorem deg_interact_activate_right (huv : u ≠ v) (h0 : C.edge u v = false)
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = true) :
    (P.interact C u v).deg v = C.deg v + 1 := by
  unfold Config.deg
  rw [← Finset.card_insert_of_notMem (a := u) (by simp [C.symm v u, h0])]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hy : y = u
  · subst hy; simp [h, huv]
  · rw [interact_edge_other C (by tauto)]
    tauto

/-- Deactivating an active edge `uv` decreases the degrees of `u` and `v` by one. -/
theorem deg_interact_deactivate_left (huv : u ≠ v) (h1 : C.edge u v = true)
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = false) :
    (P.interact C u v).deg u + 1 = C.deg u := by
  unfold Config.deg
  rw [← Finset.card_insert_of_notMem (a := v) (by simp [h])]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hy : y = v
  · subst hy; simp [h1, huv.symm]
  · rw [interact_edge_other C (by tauto)]
    tauto

theorem deg_interact_deactivate_right (huv : u ≠ v) (h1 : C.edge u v = true)
    (h : (P.δ (C.st u) (C.st v) (C.edge u v)).2.2 = false) :
    (P.interact C u v).deg v + 1 = C.deg v := by
  unfold Config.deg
  rw [← Finset.card_insert_of_notMem (a := u) (by simp [h])]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hy : y = u
  · subst hy; simp [C.symm v y, h1, huv]
  · rw [interact_edge_other C (by tauto)]
    tauto

omit [DecidableEq V] [Fintype V] in
/-- When every state is an output state, the output graph is (a copy of) the active graph. -/
def outputIso (hout : ∀ q, P.out q = true) (C : Config V Q) : (P.output C).coe ≃g C.active where
  toEquiv := Equiv.subtypeUnivEquiv (fun u => hout (C.st u))
  map_rel_iff' {a b} := by
    change C.active.Adj a.1 b.1 ↔ (P.output C).Adj a.1 b.1
    simp [output, hout]

omit [DecidableEq V] [Fintype V] in
theorem output_connected_iff (hout : ∀ q, P.out q = true) (C : Config V Q) :
    (P.output C).Connected ↔ C.active.Connected := by
  rw [SimpleGraph.Subgraph.connected_iff']
  exact (outputIso hout C).connected_iff

omit [DecidableEq V] [Fintype V] in
theorem output_neighborSet (C : Config V Q) (v : V) :
    (P.output C).neighborSet v =
      {w | v ≠ w ∧ C.edge v w = true ∧ P.out (C.st v) = true ∧ P.out (C.st w) = true} := rfl

theorem ncard_neighborSet_output (hout : ∀ q, P.out q = true) (C : Config V Q) (v : V) :
    ((P.output C).neighborSet v).ncard = C.deg v := by
  rw [output_neighborSet, Config.deg, ← Set.ncard_coe_finset]
  congr 1
  ext w
  simp [hout, ne_comm]

omit [DecidableEq V] [Fintype V] in
theorem output_verts_univ (hout : ∀ q, P.out q = true) (C : Config V Q) :
    (P.output C).verts = Set.univ := by
  ext; simp [output, hout]

end Protocol

end Cslib.NetworkConstructor
