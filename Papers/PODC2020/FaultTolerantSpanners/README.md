# Efficient and Simple Algorithms for Fault-Tolerant Spanners

Michael Dinitz, Caleb Robelle. *Efficient and Simple Algorithms for Fault-Tolerant Spanners.*
PODC 2020, pp. 493–500. DOI [10.1145/3382734.3405735](https://doi.org/10.1145/3382734.3405735),
arXiv [2002.10889](https://arxiv.org/abs/2002.10889) (v2, used here).

## Status

**Done: the whole sequential part (Sections 2–4), with no `sorry` or `axiom`.** `lean_verify` on the
main theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
The distributed part (Section 5, Theorems 11–15) is **skipped**. It rests on black boxes: padded
decompositions [DK11], Baswana–Sen [BS07] and the [DK11] reduction, all with "w.h.p." guarantees.

No error in the paper invalidates its results. There are a few minor slips and imprecisions (a wrong
equality in the proof of Lemma 3, and `f = o(n)` should be `kf = o(n)` in Lemma 7). The asymptotic
Lemma 7 / Theorem 8 are replaced by explicit, non-asymptotic statements. Theorem 8 is proved with the
explicit constant 32. See `differencies.md`.

Rough token spend: about 0.6M tokens in total (paper agent and 3 subagents).

## Model

The algorithms are sequential and deterministic, except for the choice of BFS path.

* **Graphs.** A graph is a `SimpleGraph V` on a `Fintype V` with `n = |V|`.
* **Unweighted distances.** `edist` takes values in `ℕ∞`, with `⊤` meaning unreachable.
* **Weighted distances.** Weights are `w : Sym2 V → ℝ≥0`. Distances are `wdist` in `ℝ≥0∞`: the
  infimum, over all walks, of the total weight.
* **Vertex faults.** `G \ F` for a vertex set `F` is `G.deleteVerts F`: same vertex type, all edges
  touching `F` removed. For `u, v ∉ F` its distances are those of `G[V \ F]`.
* **Edge faults.** For edge faults, Mathlib's `deleteEdges` is used.
* **Edge order.** The input order of the edges is a list `L : List (V × V)` of ordered pairs. Every
  entry is an edge, and every edge occurs in at least one orientation. For Algorithm 4 the list is
  also sorted by weight.
* **BFS.** "Run BFS to find a path of length ≤ t in G \ F" is an arbitrary *short-path oracle*
  `O : ShortPathOracle V` that satisfies `O.Spec`: it returns some walk of length `≤ t` if one
  exists, and `none` otherwise. All theorems hold for every such oracle, so for every choice of path.
  `ShortPathOracle.exists_spec` shows that such an oracle exists.
* **Running times.** Running times (Theorem 4's `O((m+n)α)`, Theorem 9) are not formalized. Only the
  structure is captured: Algorithm 2 makes at most `α + 1` oracle calls by construction.

## Theorem ↔ Lean map

Files: `LBC.lean`, `Greedy.lean`, `Size.lean`, `SizeArith.lean`, `Weighted.lean`, `Main.lean`. Graph
infrastructure is in `Cslib/Foundations/Combinatorics/SimpleGraph/`.

| Paper | Lean |
|---|---|
| Def. 1 (f-VFT / f-EFT t-spanner) | `SimpleGraph.IsVFTSpanner`, `IsEFTSpanner` (unweighted); `IsWeightedVFTSpanner`, `IsWeightedEFTSpanner` |
| Lemma 3 (check only edges) | unweighted: `isVFTSpanner_iff`, `isEFTSpanner_iff`; weighted: `isWeightedVFTSpanner_iff` (full iff), `isWeightedVFTSpanner_of_adj`, `isWeightedEFTSpanner_of_adj`, `wdist_le_mul_of_tight` |
| Algorithm 1 (exponential greedy) | not formalized (only described) |
| Length-t cut | `IsLengthCut`; edge version `IsEdgeLengthCut`; characterization `lt_edist_deleteVerts_iff`, `lt_edist_deleteEdges_iff` |
| Algorithm 2 | `lbc` (vertex version), `lbcEdge` (edge version), via the generic hitting-set loop `hitLoop` |
| **Theorem 4** | `lbc_correct` (YES part: `lbc_eq_true_of_isLengthCut`; NO part: `exists_isLengthCut_of_lbc`); `lbcEdge_correct` |
| Algorithm 3 | `modifiedGreedy` (generic scheme `greedy`, `greedyList`); EFT version `modifiedGreedyEdge` |
| **Theorem 5** | `modifiedGreedy_isVFTSpanner`; EFT version `modifiedGreedyEdge_isEFTSpanner` |
| Def. 2 (blocking set) | `SimpleGraph.IsBlockingSet` |
| **Lemma 6** | `modifiedGreedy_exists_blockingSet` (abstract core: `exists_blockingSet_of_cuts`) |
| **Lemma 7** | `SimpleGraph.IsBlockingSet.exists_dense_subgraph` (explicit: `|E(H)|·s(s-1) ≤ 2n(n-1)·|E(H')|` for `2Ds ≤ n`) |
| Moore bound (cited, [ADD+93]) | `SimpleGraph.NoShortCycles.ncard_edgeSet_le` (`|S| ≤ d^k ⇒ |E| ≤ d|S|`), `ncard_edgeSet_le_rpow` (`|E| ≤ n^{1+1/k} + n`) |
| **Theorem 8** | `modifiedGreedy_card_edges_le`: `|E(H)| ≤ 32 k f^{1-1/k} n^{1+1/k}`; sharper `modifiedGreedy_card_edges_le'`: `≤ 8 (2(2k-1)f)^{1-1/k} n^{1+1/k}` |
| Theorem 9 (running time) | not formalized |
| Algorithm 4 / **Theorem 10** | `modifiedGreedy_isWeightedVFTSpanner`, `modifiedGreedyWeighted_card_edges_le`; EFT: `modifiedGreedyEdge_isWeightedEFTSpanner` |
| Theorem 2 (summary) | `theorem2_unweighted`, `theorem2_weighted`, `exists_vft_spanner` |
| Theorems 11–15 (LOCAL/CONGEST) | skipped (out of scope) |

The non-vacuity check is `exists_sorted_edgeList`: valid sorted edge lists exist. It is used by
`exists_vft_spanner`.

## Assumptions

* `k ≥ 1` everywhere. Theorem 8 also needs `f ≥ 1`, as in the paper's Theorem 2.
* Stretch `t = 2k - 1 ≥ 1`. The local criteria (Lemma 3) need `t ≥ 1`.
* Size bound for edge faults: not formalized. The paper only asserts it ("essentially identical").

## Infrastructure (migrated to CSLib `Cslib/Foundations/Combinatorics/SimpleGraph/`; Mathlib candidates noted)

* `Spanner.lean` contains:
  * `deleteVerts` and walk transfer;
  * `Walk.interior`;
  * the cut characterizations;
  * `IsSpanner` / `IsVFTSpanner` / `IsEFTSpanner`;
  * the local stretch criterion.
* `WeightedSpanner.lean` contains:
  * `Walk.wlength` and `wdist` with the triangle inequality, monotonicity and symmetry;
  * weighted FT spanners;
  * the full Lemma 3.
* `Cycle.lean` contains `IsCycle.exists_path_of_mem_edges`: a cycle minus an edge is a path.
* `Girth.lean` contains `NoShortCycles`, path uniqueness below half the girth, and the
  **Moore bound**. This is a Mathlib candidate: Mathlib has `egirth` but no extremal girth bounds.
* `BlockingSet.lean` contains blocking sets, Lemma 7 by averaging over `s`-subsets, and its
  combination with the Moore bound.
* The generic frequency-approximation loop for hitting sets (`hitLoop`, `FinderSpec`, in `LBC.lean`)
  is also reusable.
