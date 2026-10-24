import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Graph lemmas for Protocol kRC (Theorem 12)

Small facts about reachability after deleting an edge, used in the correctness proof of
Protocol 8 (kRC) of Michail–Spirakis:

* `reachable_sdiff_edge_of_reachable`: deleting an edge on a cycle preserves reachability;
* `reachable_sdiff_edge_of_not_reachable`: deleting an edge in another component does too;
* `exists_adj_reachable_sdiff_edge`: a finite connected component in which every vertex has two
  distinct neighbours contains an edge on a cycle (a non-bridge).
-/

namespace Podc.NetworkConstructors.KRC

open SimpleGraph

variable {V : Type*}

-- CSLib candidate
/-- Deleting an edge `ab` whose endpoints stay connected preserves reachability. -/
theorem reachable_sdiff_edge_of_reachable {G : SimpleGraph V} {a b x y : V}
    (hab : (G \ edge a b).Reachable a b) (h : G.Reachable x y) :
    (G \ edge a b).Reachable x y := by
  have hnb : ¬ G.IsBridge s(a, b) := by rw [isBridge_iff]; exact not_not.2 hab
  exact h.reachable_deleteEdges_of_not_isBridge hnb

-- CSLib candidate
/-- Deleting an edge `ab` whose endpoints are not reachable from `y` does not change what is
reachable from `y`. -/
theorem reachable_sdiff_edge_of_not_reachable {G : SimpleGraph V} {a b y z : V}
    (ha : ¬ G.Reachable y a) (hb : ¬ G.Reachable y b) (h : G.Reachable y z) :
    (G \ edge a b).Reachable y z := by
  rcases h.sdiff_edge (u := a) (v := b) with h | h | h
  · exact h
  · exact absurd (h.mono sdiff_le) ha
  · exact absurd (h.mono sdiff_le) hb

-- CSLib candidate
/-- In a finite graph, if every vertex reachable from `a` has two distinct neighbours, then the
component of `a` contains an edge that is not a bridge. -/
theorem exists_adj_reachable_sdiff_edge [Finite V] {G : SimpleGraph V} {a : V}
    (h : ∀ x, G.Reachable a x → ∃ y z, y ≠ z ∧ G.Adj x y ∧ G.Adj x z) :
    ∃ x y, G.Reachable a x ∧ G.Adj x y ∧ (G \ edge x y).Reachable x y := by
  classical
  by_contra hne
  push Not at hne
  set c := G.connectedComponentMk a with hc
  have hmem : ∀ {x}, x ∈ c.supp ↔ G.Reachable a x := by
    intro x
    rw [ConnectedComponent.mem_supp_iff, hc, ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hacyc : c.toSimpleGraph.IsAcyclic := by
    rw [isAcyclic_iff_forall_adj_isBridge]
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [isBridge_iff]
    intro hr
    have hxy' : G.Adj x y := hxy
    apply hne x y (hmem.1 hx) hxy'
    let f : (c.toSimpleGraph.deleteEdges {s(⟨x, hx⟩, ⟨y, hy⟩)}) →g (G \ edge x y) :=
      { toFun := Subtype.val
        map_rel' := by
          rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
          simp only [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff, Subtype.mk.injEq] at hpq
          have hpq' : G.Adj p q := hpq.1
          simp only [sdiff_adj, edge_adj]
          refine ⟨hpq', ?_⟩
          rintro ⟨h1, -⟩
          apply hpq.2
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact .inl ⟨rfl, rfl⟩
          · exact .inr ⟨rfl, rfl⟩ }
    exact hr.map f
  have htree : c.toSimpleGraph.IsTree := ⟨c.connected_toSimpleGraph, hacyc⟩
  obtain ⟨y, z, hyz, hy, hz⟩ := h a .rfl
  have hya : y ∈ c.supp := hmem.2 hy.reachable
  have haa : a ∈ c.supp := hmem.2 .rfl
  have : Nontrivial c.supp := ⟨⟨⟨a, haa⟩, ⟨y, hya⟩, fun h => hy.ne (congrArg Subtype.val h)⟩⟩
  have : Fintype c.supp := Fintype.ofFinite _
  obtain ⟨⟨v, hv⟩, hdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
  rw [degree_eq_one_iff_existsUnique_adj] at hdeg
  obtain ⟨y, z, hyz, hy, hz⟩ := h v (hmem.1 hv)
  have hy' : y ∈ c.supp := hmem.2 ((hmem.1 hv).trans hy.reachable)
  have hz' : z ∈ c.supp := hmem.2 ((hmem.1 hv).trans hz.reachable)
  obtain ⟨w, -, hw⟩ := hdeg
  have e1 := hw ⟨y, hy'⟩ hy
  have e2 := hw ⟨z, hz'⟩ hz
  exact hyz (congrArg Subtype.val (e1.trans e2.symm))

end Podc.NetworkConstructors.KRC
