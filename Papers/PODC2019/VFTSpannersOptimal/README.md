# Vertex Fault Tolerant Spanners — PODC 2019

Greg Bodwin, Shyamal Patel. *A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners.* PODC
2019. DOI [10.1145/3293611.3331588](https://doi.org/10.1145/3293611.3331588). Formalized version: arXiv
[1812.05778](https://arxiv.org/abs/1812.05778) v2.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 1 (the FT greedy spanner has `O(f² · b(n/f, k+1))` edges) and
Corollary 2 (`O(f^{1−1/k} n^{1+1/k})` edges for stretch `2k−1`) hold, with explicit constants, for both
vertex and edge faults. There are only imprecisions. The literal fault test of Algorithm 1 lets the
fault set contain the edge's own endpoints, and Theorem 1's bound degenerates to `0` when `f > n/2`.

## Mistakes in the paper

* **Algorithm 1, read literally, outputs the whole graph; low-severity imprecision.** The test asks
  for a set `F` of `≤ f` vertices with `dist_{H\F}(u, v) > k·w(u, v)`, but does not require
  `u, v ∉ F`. Taking `F = {u}` makes the distance `∞`, so for `f ≥ 1` every edge is added. On `K_n`
  with `f = 1` and stretch 3 the output has `n(n−1)/2` edges, which contradicts Corollary 2's
  `O(n^{3/2})`. The proof of Lemma 3 clearly uses `F ⊆ V \ {u, v}`, so the intended algorithm is
  unambiguous, and we formalize that. The counterexample assumes that the distance to a deleted
  vertex is `∞`; if it is read as undefined, the literal test is merely ill-posed.
  (`literal_violates_corollary2`)
* **Theorem 1 is false as stated for large `f` (`f > n/2`); cosmetic.** The proof dismisses the
  regime `f = Ω(n)` as "trivially `O(n²)`". But once `n/f < 2`, `b(n/f, k+1) = 0`, so the stated
  bound is `0` even though `H` has edges. With floor rounding this happens for `f > n/2`, with ceiling rounding for `f ≥ n`.
  We prove `|E(H)| ≤ 32 f² · max(b(⌊n/2f⌋, k+1), 1)` for all `n` and all `f, k ≥ 1`.
  (`ftGreedy_card_edges_le`)
* **Lemma 4's `(1 + o(1))` factors hide slack.** Sampling `⌈n/2f⌉` vertices and writing the
  probabilities as `(1+o(1))/(4f²)` and `(1+o(1))/(8f³)` is only asymptotic, under the lemma's
  hypothesis `f = o(n)`. For small `n/f` the edge probability can be well below `1/(4f²)` (e.g.
  `1/(2f(4f−1))` for `n = 4f`); the triple probability never exceeds `1/(8f³)`. We prove the exact,
  non-asymptotic counting version, sampling `s` vertices with `2fs ≤ n`.
* **Small slips.**
  * The proof of Theorem 1 swaps `n` and `m` ("`n` edges and `m` nodes").
  * `f ≥ 1` is used but left implicit.
  * The edge-fault case is only asserted to be "essentially identical". We prove it via a vertex
    blocking set, which also explains the closing remark that edge blocking sets give nothing more.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A finite simple graph with non-negative real edge weights; weighted distances in `ℝ≥0∞`. This is a
  sequential, centralized algorithm, and its running time is not modelled.
* The edge order is any weight-sorted list of edges. Ties are arbitrary and duplicates harmless.
* Algorithm 1 (`ftGreedy`) adds `(u, v)` iff some set of `≤ f` vertices *avoiding `u, v`* stretches
  the current `u`–`v` distance beyond `k·w(u, v)`. The edge-fault variant is `ftGreedyEdge`.
* `b(N, g)` is the maximum number of edges of a graph on `N` vertices with no cycle of length `≤ g`
  (CSLib `SimpleGraph.girthExtremal`). The Moore bound `b(N, 2k) ≤ N^{1+1/k} + N` is proved.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Correctness of FT greedy (any order) | `ftGreedy_isWeightedVFTSpanner`, `ftGreedyEdge_isWeightedEFTSpanner` | `FTGreedy.lean` |
| Lemma 3 (blocking set of size `f·\|E\|`) | `ftGreedy_exists_blockingSet`, `ftGreedyEdge_exists_blockingSet` | `FTGreedy.lean` |
| Lemma 4 (dense subgraph of high girth) | `SimpleGraph.IsBlockingSet.exists_dense_subgraph_of_le` | CSLib `Cslib/Foundations/Combinatorics/SimpleGraph/BlockingSet.lean` |
| Theorem 1 (`≤ 32 f² max(b(⌊n/2f⌋, k+1), 1)`) | `ftGreedy_card_edges_le`, `ftGreedyEdge_card_edges_le` | `FTGreedy.lean` |
| Corollary 2 (`≤ 16 f^{1−1/k} n^{1+1/k}`) | `ftGreedy_card_edges_le_rpow`, `ftGreedyEdge_card_edges_le_rpow` | `FTGreedy.lean` |
| Literal Algorithm 1 is wrong | `ftGreedyLiteral_eq`, `literal_violates_corollary2` | `Counterexample.lean` |
| Comparison with Dinitz–Robelle (PODC'20) | `dinitzRobelle_card_edges_le_girthExtremal`, `bodwinPatel_constant_le_dinitzRobelle` | `Compare.lean` |

The comparison runs both analyses through the same blocking-set lemmas. Dinitz–Robelle's blocking set
is larger by a factor `2k−1`, so their upper bound is about `2k` times weaker in the Moore form. This
compares upper-bound constants only, not the algorithms' outputs; Dinitz–Robelle's advantage is
polynomial running time.

**Not formalized.** The optimality claims, which rest on the lower bound of [BDPW18], and the
edge-fault lower-bound remark.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `exists_vft_spanner_ftGreedy`. The generic greedy scheme
(`SimpleGraph.greedyGraph`, its correctness, and blocking sets from insertion histories
`exists_blockingSet_of_insertion`) is shared with [Dinitz–Robelle](../../PODC2020/FaultTolerantSpanners)
in `Cslib/Foundations/Combinatorics/SimpleGraph/FaultTolerantGreedy.lean`. Weighted spanners, blocking sets and `b(N, g)`
are in CSLib (`Cslib/Foundations/Combinatorics/SimpleGraph/{WeightedSpanner,BlockingSet,GirthExtremal}.lean`).
