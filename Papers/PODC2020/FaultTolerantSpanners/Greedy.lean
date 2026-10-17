import Papers.PODC2020.FaultTolerantSpanners.LBC
import Podc.Graph.Spanner.FaultTolerantGreedy

/-!
# Algorithm 3: the modified greedy algorithm (Section 3.2 of Dinitz–Robelle, PODC'20)

The edges of `G` are given as a list `L` of ordered pairs (`(u, v)` stands for the edge `{u, v}`),
in arbitrary order; every edge of `G` must occur in `L` (in at least one orientation) and every
entry of `L` must be an edge of `G`. Starting from the empty graph, the algorithm scans `L` and adds
the edge `(u, v)` to the current graph `H` iff a decision procedure `dec H u v` answers YES. This
generic greedy scheme is `SimpleGraph.greedyGraph dec L` (the list of added edges, in insertion
order, is `greedyEdges dec L`); it and its correctness for any decision procedure that answers NO
only when no small fault set separates `u, v` (`greedyGraph_isVFTSpanner`,
`greedyGraph_isEFTSpanner`) are in `Podc/Graph/Spanner/FaultTolerantGreedy.lean`, shared with
Bodwin–Patel (PODC'19).

* `modifiedGreedy O k f L` — **Algorithm 3**: `dec H u v := lbc O H u v (2k - 1) f` (Algorithm 2
  with `t = 2k - 1`, `α = f`, run on the current `H`, unweighted).
* `modifiedGreedyEdge O k f L` — the EFT variant (edge version of Algorithm 2).

Main results: **Theorem 5** `modifiedGreedy_isVFTSpanner` (plus `modifiedGreedyEdge_isEFTSpanner`).
-/

open Finset SimpleGraph

namespace FaultTolerantSpanners

variable {V : Type*}

/-! ### Algorithm 3 -/

variable [DecidableEq V]

/-- **Algorithm 3** (modified greedy, vertex faults): scan `L`, adding `(u, v)` iff Algorithm 2 with
`t = 2k - 1`, `α = f` answers YES on the current graph. -/
def modifiedGreedy (O : ShortPathOracle V) (k f : ℕ) (L : List (V × V)) : SimpleGraph V :=
  greedyGraph (fun H u v => lbc O H u v (2 * k - 1) f) L

/-- Algorithm 3 for edge faults (using the edge version of Algorithm 2). -/
def modifiedGreedyEdge (O : ShortPathOracle V) (k f : ℕ) (L : List (V × V)) : SimpleGraph V :=
  greedyGraph (fun H u v => lbcEdge O H u v (2 * k - 1) f) L

variable [Fintype V]

/-- **Theorem 5 of Dinitz–Robelle.** For every correct BFS oracle and every order `L` of the edges,
Algorithm 3 returns an `f`-VFT `(2k - 1)`-spanner of `G`. -/
theorem modifiedGreedy_isVFTSpanner {O : ShortPathOracle V} (hO : O.Spec) {G : SimpleGraph V}
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsVFTSpanner G (modifiedGreedy O k f L) f (2 * k - 1) := by
  refine greedyGraph_isVFTSpanner (by omega) ?_ hLG hL
  intro H u v hno F hF hu hv
  by_contra hlt
  rw [not_le] at hlt
  have := lbc_eq_true_of_isLengthCut hO ⟨hu, hv, hlt⟩ hF
  simp [this] at hno

/-- **Theorem 5, edge version**: Algorithm 3 with the edge version of Algorithm 2 returns an
`f`-EFT `(2k - 1)`-spanner. -/
theorem modifiedGreedyEdge_isEFTSpanner {O : ShortPathOracle V} (hO : O.Spec)
    {G : SimpleGraph V} {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsEFTSpanner G (modifiedGreedyEdge O k f L) f (2 * k - 1) := by
  refine greedyGraph_isEFTSpanner (by omega) ?_ hLG hL
  intro H u v hno F hF
  by_contra hlt
  rw [not_le] at hlt
  have := (lbcEdge_correct hO H u v (2 * k - 1) f).1 ⟨F, hlt, hF⟩
  simp [this] at hno

end FaultTolerantSpanners
