import Papers.PODC2016.GreedySpanner.MST
import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# `mstWeight` is the weight of a minimum spanning tree

Sanity check of the definition `mstWeight` (minimum weight of a spanning subgraph with the same
connected components): the minimum is attained by an acyclic subgraph, so for a connected graph it
is the minimum weight of a spanning tree, i.e. `w(MST(G))` in the paper.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A minimum-weight spanning subgraph can be chosen acyclic (a minimum spanning forest). -/
theorem exists_isAcyclic_isSpanningSub (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) :
    ∃ T, IsSpanningSub G T ∧ T.IsAcyclic ∧ wt w T = mstWeight G w := by
  obtain ⟨T, ⟨hT, hTw⟩, hmin⟩ := Set.exists_min_image
    {T | IsSpanningSub G T ∧ wt w T = mstWeight G w} (fun T => T.edgeSet.ncard)
    (Set.toFinite _) (exists_wt_eq_mstWeight G w)
  refine ⟨T, hT, fun v c hc => ?_, hTw⟩
  cases c with
  | nil => exact Walk.not_isCycle_nil hc
  | @cons _ b _ hvb c' =>
  have he : s(v, b) ∈ (Walk.cons hvb c').edges := by simp
  obtain ⟨p, -, hpe, -, -⟩ := hc.exists_path_of_mem_edges he
  set T₀ := T.deleteEdges {s(v, b)}
  have hsub : ∀ f ∈ p.edges, f ∈ T₀.edgeSet := fun f hf => by
    rw [edgeSet_deleteEdges]
    exact ⟨(Walk.cons hvb c').edges_subset_edgeSet (hpe f hf).1, (hpe f hf).2⟩
  have hreach : T₀.Reachable v b := ⟨p.transfer T₀ hsub⟩
  have hT₀ : IsSpanningSub G T₀ := by
    refine ⟨(deleteEdges_le _).trans hT.1, fun a a' haa' => reachable_of_forall_adj ?_ (hT.2 a a' haa')⟩
    intro x y hxy
    by_cases hxy' : s(x, y) = s(v, b)
    · rcases Sym2.eq_iff.mp hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hreach
      · exact hreach.symm
    · exact (deleteEdges_adj.mpr ⟨hxy, by simpa using hxy'⟩).reachable
  have hw : wt w T₀ = mstWeight G w :=
    le_antisymm (hTw ▸ wt_mono (deleteEdges_le _)) (mstWeight_le_wt hT₀)
  have hlt : T₀.edgeSet.ncard < T.edgeSet.ncard := by
    refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
    rw [edgeSet_deleteEdges]
    exact Set.sdiff_singleton_ssubset.mpr hvb
  exact absurd (hmin T₀ ⟨hT₀, hw⟩) (not_le.mpr hlt)

-- CSLib candidate
/-- For a connected graph, `mstWeight` is the minimum weight of a spanning tree. -/
theorem mstWeight_eq_iInf_isTree (hG : G.Connected) (w : Sym2 V → ℝ≥0) :
    mstWeight G w = ⨅ (T : SimpleGraph V) (_ : T ≤ G) (_ : T.IsTree), wt w T := by
  refine le_antisymm (le_iInf fun T => le_iInf fun hle => le_iInf fun htree =>
    mstWeight_le_wt ⟨hle, fun u v _ => htree.connected.preconnected u v⟩) ?_
  obtain ⟨T, hT, hac, hw⟩ := exists_isAcyclic_isSpanningSub G w
  have : Nonempty V := hG.nonempty
  have htree : T.IsTree := ⟨⟨fun u v => hT.2 u v (hG.preconnected u v)⟩, hac⟩
  exact (iInf_le_of_le T (iInf_le_of_le hT.1 (iInf_le_of_le htree le_rfl))).trans hw.le

end GreedySpanner
