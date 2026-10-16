import Papers.PODC2016.GreedySpanner.Basic

/-!
# Lemma 3: the only `t`-spanner of the greedy `t`-spanner is itself

The proof follows the paper: if `e ∈ H \ H'`, take a shortest path `P` in `H'` between the
endpoints of `e` (weight `≤ t · w(e)`) and let `e'` be the edge of `P ∪ {e}` examined last by the
greedy algorithm. All other edges of the cycle `P ∪ {e}` were added before `e'`, and they form a
walk between the endpoints of `e'` of weight `≤ w(P) ≤ t · w(e) ≤ t · w(e')`, so `e'` would have been
rejected.

The hypothesis `t ≥ 1` of the paper is not needed for this lemma.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} {G H H' : SimpleGraph V} {w : Sym2 V → ℝ≥0} {t : ℝ≥0}

-- CSLib candidate
/-- **Lemma 3** of Filtser–Solomon: let `H` be the greedy `t`-spanner of `(G, w)` (any execution
of Algorithm 1). If `H'` is a `t`-spanner of `(H, w)`, then `H' = H`. -/
theorem lemma3 [Finite V] (hH : IsGreedySpanner G w t H) (hH' : IsWSpanner H H' w t) :
    H' = H := by
  classical
  obtain ⟨L, ⟨hnd, hLG, hsort⟩, rfl⟩ := hH
  refine le_antisymm hH'.1 fun u v huv => ?_
  by_contra hne
  have he : s(u, v) ∈ greedySet w t L := ((fromEdgeSet_adj _).mp huv).1
  have hd : H'.wdist w u v ≤ t * w s(u, v) := hH'.wdist_le_of_adj huv
  have hreach : H'.Reachable u v := reachable_of_wdist_lt_top
    (hd.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top))
  obtain ⟨P, hP, hPw⟩ := exists_isPath_wlength_eq (w := w) hreach
  rw [← hPw] at hd
  have hPA : ∀ f ∈ P.edges, f ∈ greedySet w t L := fun f hf =>
    mem_greedySet_of_mem_edgeSet (edgeSet_mono hH'.1 (P.edges_subset_edgeSet hf))
  have hPe : s(u, v) ∉ P.edges := fun h => hne (P.edges_subset_edgeSet h)
  -- all edges of the cycle `P ∪ {uv}` are added edges, hence listed in `L`
  have hA : ∀ f ∈ s(u, v) :: P.edges, f ∈ greedySet w t L := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact hPA f hf
  have hinL : ∀ f ∈ s(u, v) :: P.edges, f ∈ L := fun f hf => greedySet_subset L (hA f hf)
  -- the edge `e'` examined last
  obtain ⟨e', he'S, he'max⟩ := (s(u, v) :: P.edges).toFinset.exists_max_image (L.idxOf ·)
    ⟨s(u, v), by simp⟩
  rw [List.mem_toFinset] at he'S
  have hlt : ∀ f ∈ s(u, v) :: P.edges, f ≠ e' → L.idxOf f < L.idxOf e' := fun f hf hfe =>
    lt_of_le_of_ne (he'max f (List.mem_toFinset.mpr hf))
      (fun h => hfe ((List.idxOf_inj (hinL f hf)).mp h))
  by_cases hcase : e' = s(u, v)
  · -- `uv` itself is last: it would have been rejected
    subst hcase
    have := lt_wlength_of_mem_greedySet hnd he P fun f hf =>
      ⟨hPA f hf, hlt f (List.mem_cons_of_mem _ hf) (fun h => hPe (h ▸ hf))⟩
    exact absurd hd (not_le.mpr this)
  · -- `e' ∈ P` is last: replace it by `uv` in the cycle
    have he'P : e' ∈ P.edges := (List.mem_cons.mp he'S).resolve_left hcase
    rw [Walk.edges_eq_map_darts, List.mem_map] at he'P
    obtain ⟨d, hd_mem, rfl⟩ := he'P
    obtain ⟨P₁, P₂, hPeq⟩ := Walk.exists_eq_append_cons_of_mem_darts hd_mem
    have hedges : P.edges = P₁.edges ++ d.edge :: P₂.edges := by
      rw [hPeq, Walk.edges_append, Walk.edges_cons]
      rfl
    have hnodup := hP.isTrail.edges_nodup
    rw [hedges] at hnodup
    have hd1 : d.edge ∉ P₁.edges := fun h =>
      (List.disjoint_of_nodup_append hnodup h) (List.mem_cons_self ..)
    have hd2 : d.edge ∉ P₂.edges := (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
    let Q : (greedy w t L).Walk d.fst d.snd :=
      (P₁.reverse.mapLe hH'.1).append (Walk.cons huv (P₂.reverse.mapLe hH'.1))
    have hQedges : Q.edges = P₁.edges.reverse ++ s(u, v) :: P₂.edges.reverse := by
      simp [Q, Walk.edges_append, Walk.edges_reverse]
    have hmemP : ∀ f, f ∈ P₁.edges ∨ f ∈ P₂.edges → f ∈ P.edges := by
      intro f hf
      rw [hedges]
      rcases hf with hf | hf
      · exact List.mem_append_left _ hf
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    have hde : d.edge = s(d.fst, d.snd) := rfl
    have hd_add : s(d.fst, d.snd) ∈ greedySet w t L :=
      hde ▸ hPA d.edge (hedges ▸ List.mem_append_right _ (List.mem_cons_self ..))
    have key := lt_wlength_of_mem_greedySet hnd hd_add Q fun f hf => by
      rw [hQedges, List.mem_append, List.mem_cons, List.mem_reverse, List.mem_reverse] at hf
      rcases hf with hf | rfl | hf
      · exact ⟨hPA f (hmemP f (Or.inl hf)), hde ▸ hlt f (List.mem_cons_of_mem _ (hmemP f (Or.inl hf)))
          (fun h => hd1 (h ▸ hf))⟩
      · exact ⟨he, hde ▸ hlt _ (List.mem_cons_self ..) (Ne.symm hcase)⟩
      · exact ⟨hPA f (hmemP f (Or.inr hf)), hde ▸ hlt f (List.mem_cons_of_mem _ (hmemP f (Or.inr hf)))
          (fun h => hd2 (h ▸ hf))⟩
    -- weights: `w(uv) ≤ w(e')` by the order of the scan
    have hw : w s(u, v) ≤ w d.edge :=
      weight_le_of_idxOf_lt hsort (hinL _ (List.mem_cons_self ..)) (hinL _ he'S)
        (hlt _ (List.mem_cons_self ..) (Ne.symm hcase))
    have hQw : Q.wlength w = P₁.wlength w + w s(u, v) + P₂.wlength w := by
      simp [Q, Walk.wlength, Walk.edges_append, Walk.edges_reverse, List.sum_reverse, add_assoc]
    have hPw' : P.wlength w = P₁.wlength w + w d.edge + P₂.wlength w := by
      simp [Walk.wlength, hedges, add_assoc]
    have : Q.wlength w ≤ t * w s(d.fst, d.snd) := by
      calc Q.wlength w ≤ P.wlength w := by
            rw [hQw, hPw']; gcongr
        _ ≤ t * w s(u, v) := hd
        _ ≤ t * w s(d.fst, d.snd) := by rw [← hde]; gcongr
    exact absurd this (not_le.mpr key)

end GreedySpanner
