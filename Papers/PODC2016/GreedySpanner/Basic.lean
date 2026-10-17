import Podc.Graph.Spanner.Greedy
import Cslib.Foundations.Combinatorics.SimpleGraph.ShortestWalks

/-!
# The greedy spanner: model (Filtser–Solomon, PODC 2016, Section 2)

A weighted graph is a `G : SimpleGraph V` together with `w : Sym2 V → ℝ≥0` (CSLib convention: only
the values on edges matter); distances are CSLib's `wdist` (in `ℝ≥0∞`, `⊤` = disconnected).
The stretch `t` is a real number (`t : ℝ≥0`, `1 ≤ t` where needed).

The model is the shared greedy-spanner library `Podc/Graph/Spanner/{Weighted,Greedy}.lean`
(namespace `SimpleGraph`):

* `IsWSpanner G H w t` — `H ≤ G` and `δ_H(u, v) ≤ t · δ_G(u, v)` for all `u, v`;
  `isWSpanner_of_adj` — the local criterion of Section 2.
* `greedySpanner w t L` — **Algorithm 1**: scan the list `L` of edges and add `e = {u, v}` iff
  `δ_H(u, v) > t · w(e)` for the current `H` (`greedySpanner_eq_foldl` below: literally the paper's
  loop); `greedySpannerEdges w t L` — the kept edges, in scan order.
* `IsGreedyOrder G w L` — `L` lists every edge of `G` exactly once, in non-decreasing order of
  weight (ties in arbitrary order). `IsGreedySpanner G w t H` — `H` is the output of *some*
  execution of Algorithm 1 (the paper's "the greedy `t`-spanner" = an arbitrary execution).
* `IsGreedySpanner.isWSpanner` — the output is a `t`-spanner; the two scan properties used in all
  proofs are `lt_wlength_of_mem_greedySpannerEdges` and `exists_walk_of_not_mem_greedySpannerEdges`.

This file adds the total weight `wt w H` of a graph.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} {G H : SimpleGraph V} {w : Sym2 V → ℝ≥0}

/-- **Algorithm 1** (`Greedy(G, t)`) as written in the paper: starting from `E(H) = ∅`, scan `L`
and insert `e` into `E(H)` iff `t · w(e) < δ_H(e)`. -/
theorem greedySpanner_eq_foldl (t : ℝ≥0) (L : List (Sym2 V)) :
    greedySpanner w t L = fromEdgeSet (L.foldl (fun A e => open Classical in
      if (t : ℝ≥0∞) * w e < (fromEdgeSet A).wdistS w e then insert e A else A) ∅) := by
  classical
  suffices {e | e ∈ greedySpannerEdges w t L} = L.foldl (fun A e =>
      if (t : ℝ≥0∞) * w e < (fromEdgeSet A).wdistS w e then insert e A else A) ∅ by
    rw [greedySpanner, this]
  induction L using List.reverseRecOn with
  | nil => ext; simp [greedySpannerEdges]
  | append_singleton L e ih =>
    rw [greedySpannerEdges_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih,
      greedySpanner]
    split_ifs <;> ext <;> simp [or_comm]

/-! ### Weight of a graph -/

/-- Total weight `w(H) = ∑_{e ∈ E(H)} w(e)`. -/
noncomputable def wt [Fintype V] (w : Sym2 V → ℝ≥0) (H : SimpleGraph V) : ℝ≥0∞ :=
  ∑ e : Sym2 V, H.edgeSet.indicator (fun e => (w e : ℝ≥0∞)) e

lemma wt_mono [Fintype V] {H₁ H₂ : SimpleGraph V} (h : H₁ ≤ H₂) : wt w H₁ ≤ wt w H₂ :=
  Finset.sum_le_sum fun e _ =>
    Set.indicator_le_indicator_of_subset (edgeSet_mono h) (fun _ => zero_le) e

lemma sum_indicator_union_singleton [Fintype V] (g : Sym2 V → ℝ≥0∞) {S : Set (Sym2 V)}
    {f : Sym2 V} (hf : f ∉ S) :
    ∑ e : Sym2 V, (S ∪ {f}).indicator g e = ∑ e : Sym2 V, S.indicator g e + g f := by
  classical
  rw [Set.indicator_union_of_disjoint (Set.disjoint_singleton_right.mpr hf)]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [Set.indicator_apply]

end GreedySpanner
