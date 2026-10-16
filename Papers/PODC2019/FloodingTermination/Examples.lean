import Papers.PODC2019.FloodingTermination.Compute

/-!
# Examples from the paper

All termination times, eccentricities and diameters below are computed by `decide` through the
verified simulation of `Compute.lean`.

* `figure_7_as_drawn` — the graph of Figure 7 *as drawn* has `e = 3`, `d = 5` and termination time
  `7 < e + d + 1 = 9`, so it does **not** witness sharpness of Theorem 3.7, contrary to the caption
  ("`7 = 2 + 4 + 1 = e + d + 1`").
* `figure_7_without_i` — after deleting the pendant node `i`, the caption's numbers `e = 2`, `d = 4`,
  `T = 7 = e + d + 1` are correct.
* `petersen_sharp`, `triangle_sharp` — the Petersen graph (from every node) and the triangle attain
  `e + d + 1 = 2d + 1`, so the bound of Theorem 3.7 is sharp.
* Small examples of the introduction: cube, path, 5- and 6-cycles.
* `lemma_3_3_needs_connected`, `lemma_3_4_needs_connected` — Lemmas 3.3 and 3.4 fail without
  connectivity.
-/

namespace FloodingTermination.Examples

open SimpleGraph

/-- The simple graph on `Fin n` with the given (undirected) edge list. -/
def ofEdges {n : ℕ} (l : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ l

instance {n : ℕ} (l : List (Fin n × Fin n)) : DecidableRel (ofEdges l).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ l ∨ (b, a) ∈ l)))

/-- The graph of Figure 7, as drawn: a 5-cycle `b – a – c – e – d – b` with pendant paths
`b – f – g` and `d – h – i`. Vertices: `b = 0, a = 1, c = 2, e = 3, d = 4, f = 5, g = 6, h = 7,
i = 8`. -/
abbrev fig7 : SimpleGraph (Fin 9) :=
  ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (4, 7), (7, 8)]

/-- Figure 7 without the node `i` (`i = 8` deleted). -/
abbrev fig7' : SimpleGraph (Fin 8) :=
  ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (4, 7)]

/-- The Petersen graph: outer 5-cycle `0..4`, inner pentagram `5..9`, spokes `i – i+5`. -/
abbrev petersen : SimpleGraph (Fin 10) :=
  ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

/-- The triangle. -/
abbrev triangle : SimpleGraph (Fin 3) := ofEdges [(0, 1), (1, 2), (2, 0)]

/-- The 3-cube (vertices = bit vectors, adjacent iff they differ in one bit). -/
abbrev cube : SimpleGraph (Fin 8) :=
  ofEdges [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7),
    (6, 7)]

/-- The path `a – b – c – d` of Figure 2 (`a = 0`, `b = 1`, …). -/
abbrev path4 : SimpleGraph (Fin 4) := ofEdges [(0, 1), (1, 2), (2, 3)]

abbrev cycle5 : SimpleGraph (Fin 5) := ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

abbrev cycle6 : SimpleGraph (Fin 6) := ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]

/-- Figure 7 as drawn: termination time `7`, eccentricity of `b` is `3`, diameter `5`; so the
example is not sharp for Theorem 3.7 (`7 < 3 + 5 + 1`). -/
theorem figure_7_as_drawn :
    IsTerminationTime fig7 0 7 ∧ fig7.eccent 0 = 3 ∧ fig7.diam = 5 := by
  refine ⟨by rw [isTerminationTime_succ_iff]; decide, eccent_eq_of_roundSet ?_ ?_,
    diam_eq_of_roundSet ?_ ?_⟩
  · decide
  · exact ⟨8, by decide⟩
  · decide
  · exact ⟨6, 8, by decide⟩

/-- Figure 7 without `i`: termination time `7 = e + d + 1` with `e = 2`, `d = 4`, as the caption
says. -/
theorem figure_7_without_i :
    IsTerminationTime fig7' 0 7 ∧ fig7'.eccent 0 = 2 ∧ fig7'.diam = 4 := by
  refine ⟨by rw [isTerminationTime_succ_iff]; decide, eccent_eq_of_roundSet ?_ ?_,
    diam_eq_of_roundSet ?_ ?_⟩
  · decide
  · exact ⟨6, by decide⟩
  · decide
  · exact ⟨6, 3, by decide⟩

/-- The Petersen graph: from every node, flooding takes `5 = 2d + 1 = e + d + 1` rounds. -/
theorem petersen_sharp :
    (∀ v, IsTerminationTime petersen v 5) ∧ (∀ v, petersen.eccent v = 2) ∧ petersen.diam = 2 := by
  refine ⟨fun v => by rw [isTerminationTime_succ_iff]; revert v; decide,
    fun v => eccent_eq_of_roundSet ?_ ?_, diam_eq_of_roundSet ?_ ?_⟩
  · revert v; decide
  · revert v; decide
  · decide
  · exact ⟨0, 2, by decide⟩

/-- The triangle (Figure 3): `3 = 2d + 1 = e + d + 1` rounds. -/
theorem triangle_sharp :
    IsTerminationTime triangle 0 3 ∧ triangle.eccent 0 = 1 ∧ triangle.diam = 1 := by
  refine ⟨by rw [isTerminationTime_succ_iff]; decide, eccent_eq_of_roundSet ?_ ?_,
    diam_eq_of_roundSet ?_ ?_⟩
  · decide
  · exact ⟨1, by decide⟩
  · decide
  · exact ⟨0, 1, by decide⟩

/-- Introduction / Figure 1: on the cube flooding stops after `3 = d` rounds. -/
theorem cube_time : IsTerminationTime cube 0 3 := by
  rw [isTerminationTime_succ_iff]; decide

/-- Figure 2: on the path `a – b – c – d`, flooding from `b` stops after `2 = ecc(b)` rounds. -/
theorem path4_time : IsTerminationTime path4 1 2 := by
  rw [isTerminationTime_succ_iff]; decide

/-- Figure 6: 3 rounds on the 6-cycle and 5 rounds on the 5-cycle. -/
theorem cycles_time : IsTerminationTime cycle6 0 3 ∧ IsTerminationTime cycle5 0 5 := by
  constructor <;> (rw [isTerminationTime_succ_iff]; decide)

/-! ### Connectivity is needed in Section 3

The paper states Lemmas 3.3 and 3.4 for "a graph `G`"; they need `G` connected (as assumed in the
abstract). -/

/-- Two nodes, no edges. -/
abbrev twoIsolated : SimpleGraph (Fin 2) := ofEdges []

/-- Source `0` isolated, plus an edge `1 – 2`. -/
abbrev isolatedPlusEdge : SimpleGraph (Fin 3) := ofEdges [(1, 2)]

lemma not_reachable_of_isolated {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (huv : u ≠ v)
    (hu : ∀ x, ¬ G.Adj u x) : ¬ G.Reachable u v := by
  rintro ⟨p⟩
  exact hu _ (p.adj_snd (Walk.not_nil_of_ne huv))

/-- Lemma 3.3 fails for disconnected graphs: `twoIsolated` has no ec nodes, but node `1` lies in
no round-set. -/
theorem lemma_3_3_needs_connected :
    (∀ g, ¬ IsEC twoIsolated 0 g) ∧ ¬ ∀ v, ∃! j, v ∈ roundSet twoIsolated 0 j := by
  have hno : ∀ a b : Fin 2, ¬ twoIsolated.Adj a b := by decide
  refine ⟨fun g ⟨g', _, _, _, hadj⟩ => hno g g' hadj, fun h => ?_⟩
  obtain ⟨j, hj, -⟩ := h 1
  exact not_reachable_of_isolated (by decide) (by decide) (reachable_of_mem_roundSet hj)

/-- Lemma 3.4 fails for disconnected graphs: `isolatedPlusEdge` is bipartite, but `1` is an ec node
(both `1` and `2` are at distance `∞` from the source `0`). -/
theorem lemma_3_4_needs_connected :
    isolatedPlusEdge.IsBipartite ∧ IsEC isolatedPlusEdge 0 1 := by
  refine ⟨⟨Coloring.mk (fun v => if v = 1 then 0 else 1) ?_⟩, 2, by decide, by decide, ?_, by decide⟩
  · intro u v; revert u v; decide
  · rw [edist_eq_top_of_not_reachable (not_reachable_of_isolated (by decide) (by decide)),
      edist_eq_top_of_not_reachable (not_reachable_of_isolated (by decide) (by decide))]

end FloodingTermination.Examples
