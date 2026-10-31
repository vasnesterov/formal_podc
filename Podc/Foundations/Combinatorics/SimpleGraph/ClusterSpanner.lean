import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner
import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/ClusterSpanner.lean

/-!
# Cluster spanners (Peleg–Schäffer)

The classical criterion behind clustering-based spanner constructions (Baswana–Sen and its
relatives): partition the vertices into clusters of small diameter in `H` and keep, for every pair of
adjacent clusters, at least one edge of `G` between them. Then `H` is a `(2ℓ + 1)`-spanner.

Staged for Bitton–Emek–Izumi–Kutten (PODC 2019, `Papers/PODC2019/LocalMessageReduction/`), where it
is Lemma 4.4 (citing Peleg–Schäffer 1989).

## Main results

* `SimpleGraph.isSpanner_of_clusters`: if `H ≤ G`, every two vertices of the same cluster are at
  `H`-distance `≤ ℓ`, and every `G`-edge between two different clusters is "covered" by an `H`-edge
  between the same two clusters, then `H` is a `(2ℓ + 1)`-spanner of `G`.

The clusters are given by a labelling `c : V → ι` (the partition into fibres). The diameter
hypothesis is on `H`-distances, which is weaker than (implied by) a bound on the diameter of the
induced subgraph `H[C]`.
-/

namespace SimpleGraph

variable {V ι : Type*} {G H : SimpleGraph V}

/-- **Cluster spanner lemma** (Peleg–Schäffer; Lemma 4.4 of Bitton–Emek–Izumi–Kutten, PODC 2019).
Let `c : V → ι` label the clusters of a partition of `V`. If `H ≤ G`, any two vertices with the same
label are at `H`-distance at most `ℓ`, and for every edge `xy` of `G` joining two different clusters
`H` contains an edge `x'y'` with `x'` in the cluster of `x` and `y'` in the cluster of `y`, then
`H` is a `(2ℓ + 1)`-spanner of `G`. -/
theorem isSpanner_of_clusters (c : V → ι) (ℓ : ℕ) (hHG : H ≤ G)
    (hdiam : ∀ x y, c x = c y → H.edist x y ≤ ℓ)
    (hcross : ∀ x y, G.Adj x y → c x ≠ c y →
      ∃ x' y', c x' = c x ∧ c y' = c y ∧ H.Adj x' y') :
    G.IsSpanner H (2 * ℓ + 1) := by
  refine ⟨hHG, edist_le_mul_of_adj (by omega) (fun x y hxy => ?_)⟩
  by_cases hc : c x = c y
  · calc H.edist x y ≤ ℓ := hdiam x y hc
      _ ≤ ((2 * ℓ + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
  · obtain ⟨x', y', hx', hy', hadj⟩ := hcross x y hxy hc
    calc H.edist x y ≤ H.edist x x' + H.edist x' y := H.edist_triangle
      _ ≤ H.edist x x' + (H.edist x' y' + H.edist y' y) := by gcongr; exact H.edist_triangle
      _ ≤ ℓ + (1 + ℓ) := by
          gcongr
          · exact hdiam x x' hx'.symm
          · exact (edist_eq_one_iff_adj.mpr hadj).le
          · exact hdiam y' y hy'
      _ = ((2 * ℓ + 1 : ℕ) : ℕ∞) := by push_cast; ring

end SimpleGraph
