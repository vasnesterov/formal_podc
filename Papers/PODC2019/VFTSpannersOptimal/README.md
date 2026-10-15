# A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners

Greg Bodwin, Shyamal Patel. *A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners.*
PODC 2019. DOI [10.1145/3293611.3331588](https://doi.org/10.1145/3293611.3331588),
arXiv [1812.05778](https://arxiv.org/abs/1812.05778) (v2, used here).

## Status

**Done, with no `sorry` and no `axiom`.** `#print axioms` on all main theorems lists only `propext`,
`Classical.choice` and `Quot.sound`.

Formalized, for both vertex faults (VFT) and edge faults (EFT):

* Theorem 1 (main result), with explicit constants.
* Corollary 2.
* Lemmas 3 and 4.
* Correctness of the FT greedy algorithm.

Not formalized:

* The optimality claims, which rest on the lower bound of [BDPW18].
* The EFT lower-bound remark in the final paragraph.

**Findings** (details in `differencies.md`):

* Algorithm 1 read literally is wrong (genuine imprecision, low severity): the fault set may contain
  `u` or `v`. Lean counterexample: `literal_violates_corollary2`. It relies on the convention that
  the distance to a deleted vertex is `∞`.
* Minor imprecisions:
  * Theorem 1 is false as stated when `f = Ω(n)`, because `b(n/f, k+1)` can be `0` (genuine but
    cosmetic).
  * The proof swaps `n` and `m`.
  * The `(1+o(1))` factors with the ceiling `⌈n/2f⌉` hide a constant-factor slack.
  * Ties among equal weights need no special handling.

Rough token spend: about 0.2M tokens (paper agent and 1 subagent). The paper reuses the
Dinitz–Robelle infrastructure.

## Model

The model is weighted and sequential; the FT greedy algorithm runs in exponential time.

* **Graphs and weights.** A graph is `G : SimpleGraph V` on a `Fintype V`, with weights
  `w : Sym2 V → ℝ≥0`. Weighted distances are `wdist`, valued in `ℝ≥0∞` (`Cslib/Foundations/Combinatorics/SimpleGraph/WeightedSpanner.lean`).
* **Edge order.** The edge order is a list `L : List (V × V)` of ordered pairs. Every entry is an
  edge, every edge occurs in at least one orientation, and the list is sorted by weight
  (`L.Pairwise (w · ≤ w ·)`).
* **Algorithm 1.**
  * `ftGreedy w k f L` adds `(u, v)` iff some `F ∌ u, v` with `|F| ≤ f` vertices has
    `d_{H \ F}(u, v) > k · w(u, v)`.
  * `ftGreedyEdge` is the same with `F ∌ {u, v}` a set of `≤ f` edges.
  * Both are built on the generic scan `FaultTolerantSpanners.greedy` from
    `Papers/PODC2020/FaultTolerantSpanners/Greedy.lean`.
  * The test is a classical `decide`, so its exponential-time evaluation is not modelled.
* **The function `b(N, g)`.** `SimpleGraph.girthExtremal N g` is the maximum number of edges of a
  graph on `Fin N` with no cycle of length `≤ g` (`Cslib/Foundations/Combinatorics/SimpleGraph/GirthExtremal.lean`).

## Theorem ↔ Lean map

The files are `Blocking.lean`, `FTGreedy.lean`, `Counterexample.lean` and `Compare.lean`.

| Paper | Lean |
|---|---|
| Def. 2 (FT spanners) | `SimpleGraph.IsWeightedVFTSpanner`, `IsWeightedEFTSpanner` |
| Algorithm 1 | `ftGreedy` / `ftGreedyEdge` (tests `vftTest` / `eftTest`) |
| correctness ("obvious") | `ftGreedy_isWeightedVFTSpanner`, `ftGreedyEdge_isWeightedEFTSpanner` (any edge order) |
| Def. 3 (blocking set) | `SimpleGraph.IsBlockingSet` |
| **Lemma 3** | `ftGreedy_exists_blockingSet`, `ftGreedyEdge_exists_blockingSet` (abstract core: `exists_blockingSet_of_insertion`) |
| **Lemma 4** | `SimpleGraph.IsBlockingSet.exists_dense_subgraph_of_le` (`m·s(s-1) ≤ 2n(n-1)·|E(H')|` for `2fs ≤ n`), extremal form `IsBlockingSet.ncard_mul_le_girthExtremal` |
| `b(n, k)` | `SimpleGraph.girthExtremal` |
| **Theorem 1** | `ftGreedy_card_edges_le`, `ftGreedyEdge_card_edges_le`: `|E(H)| ≤ 32 f² · max(b(⌊n/2f⌋, k+1), 1)`; abstract form `IsBlockingSet.ncard_le_girthExtremal` |
| Moore bound `b(n, 2k) = O(n^{1+1/k})` | `girthExtremal_le_of_le_pow`, `girthExtremal_le_rpow` (`≤ N^{1+1/k} + N`) |
| **Corollary 2** | `ftGreedy_card_edges_le_rpow`, `ftGreedyEdge_card_edges_le_rpow`: stretch `2k-1` ⇒ `|E(H)| ≤ 16 f^{1-1/k} n^{1+1/k}` |
| non-vacuity | `exists_vft_spanner_ftGreedy` |
| literal Algorithm 1 is wrong | `ftGreedyLiteral_eq`, `literal_violates_corollary2` |
| comparison with Dinitz–Robelle | `dinitzRobelle_card_edges_le_girthExtremal`, `bodwinPatel_constant_le_dinitzRobelle` |

## Assumptions

* Theorem 1 assumes `k ≥ 1` (stretch) and `f ≥ 1`; the paper leaves `f ≥ 1` implicit. Corollary 2 assumes `k ≥ 1` and stretch
  `2k - 1`.
* Lemma 3 and Theorem 1 need the weight-sorted order. Correctness holds for any order.

## Relation to Dinitz–Robelle (PODC'20, `Papers/PODC2020/FaultTolerantSpanners`)

Both analyses go through the same shared lemmas:

1. A small blocking set gives a dense subgraph of girth `> t` (`exists_dense_subgraph_of_le`).
2. The dense subgraph gives a bound in terms of `b` (`ncard_le_girthExtremal`) or, through the Moore
   bound, in terms of `n^{1+1/k}`.

They differ only in the size of the blocking set:

* **Bodwin–Patel** (this paper):
  * Algorithm: the exact FT greedy, in exponential time, for any stretch `k`, weighted.
  * Blocking set: size `f·|E|`.
  * Bound: `32 f² max(b(⌊n/2f⌋, k+1), 1)`; for stretch `2k-1`, `16 f^{1-1/k} n^{1+1/k}`.
* **Dinitz–Robelle**:
  * Algorithm: polynomial time, through the length-bounded-cut approximation. Only odd stretch
    `2k-1`. The LBC test ignores weights, which are used only for the edge order.
  * Blocking set: size `(2k-1)f·|E|`, i.e. `f` replaced by `(2k-1)f`.
  * Bound: `32((2k-1)f)² max(b(⌊n/2(2k-1)f⌋, 2k), 1)` (`dinitzRobelle_card_edges_le_girthExtremal`,
    proved here; neither paper states it). The Moore form is `32 k f^{1-1/k} n^{1+1/k}`.

So Bodwin–Patel's upper bound is smaller, by a factor of about `2k` in the Moore form, and applies
to every stretch. This compares upper-bound constants only: it is not a proven separation between
the two algorithms' outputs. Dinitz–Robelle is stronger in running time, and is the one that comes with distributed
variants. Neither output is a subgraph of the other in general; Dinitz–Robelle note this.

## CSLib / Mathlib candidates

Already migrated to CSLib (Mathlib candidates):
* `Cslib/Foundations/Combinatorics/SimpleGraph/GirthExtremal.lean`: `girthExtremal`, `NoShortCycles.of_embedding`, the Moore bounds
  for `b`, and the blocking-set bounds.
* `IsBlockingSet.exists_dense_subgraph_of_le` in `Cslib/Foundations/Combinatorics/SimpleGraph/BlockingSet.lean`, generalized here to
  any cycle-length bound `t`.

Still in this folder (CSLib candidates):
* `exists_blockingSet_of_insertion` and `greedyList_sublist` (`Blocking.lean`), together with the
  generic greedy scan from the PODC'20 folder. These should move to CSLib (`Cslib/Foundations/Combinatorics/SimpleGraph/`) once a third
  greedy-spanner paper needs them.
