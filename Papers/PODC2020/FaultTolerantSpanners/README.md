# Efficient Fault-Tolerant Spanners — PODC 2020

Michael Dinitz, Caleb Robelle. *Efficient and Simple Algorithms for Fault-Tolerant Spanners.* PODC 2020.
DOI [10.1145/3382734.3405735](https://doi.org/10.1145/3382734.3405735). Formalized version: arXiv
[2002.10889](https://arxiv.org/abs/2002.10889) v2.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** The sequential part (Sections 2–4) holds as stated. The modified greedy
algorithm, which uses the length-bounded-cut approximation (Algorithm 2), outputs an `f`-VFT
`(2k−1)`-spanner with `O(k f^{1−1/k} n^{1+1/k})` edges, weighted and unweighted. We prove it with the
explicit constant 32. We found only two minor slips, both in proofs.

## Mistakes in the paper

No substantive errors. Two minor slips, neither affecting any statement:

* **Lemma 3 (weighted), "if" direction, case `p = 1`.** The paper writes
  `d_{H\F}(u, v) = w(u, v) = d_{G\F}(u, v)`, but `H` need not contain the edge `uv`. What holds, and
  suffices, is `d_{H\F}(u, v) ≤ t·w(u, v)` by hypothesis. We prove the full iff by a different
  argument. A non-tight edge has a strictly lighter walk made of strictly lighter edges, so strong
  induction on the number of lighter edges applies; no shortest paths are needed
  (`isWeightedVFTSpanner_iff`).
* **Lemma 7 assumes `f = o(n)`, but the estimate
  `s(s−1)/(n(n−1)) ≥ (1−o(1))/(4((2k−1)f)²)` needs `kf = o(n)`,** since `k` may grow with `n`.
  Harmless, because Theorem 8 is trivial when `kf = Ω(n)`. We replace the asymptotic lemma by exact
  counting over all `s`-subsets: if `|B| ≤ D·m` and `2Ds ≤ n`, some `s`-set carries a subgraph of
  girth `> 2k` with `m·s(s−1) ≤ 2n(n−1)·|E(H′)|`. A case split at `n < 8(2k−1)f` replaces "if
  `f = Ω(n)` the theorem is trivial".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Sequential, deterministic algorithms on a finite simple graph. Distances are unweighted in `ℕ∞`, or
  weighted with weights `≥ 0` in `ℝ≥0∞`; `⊤` means unreachable.
* `G \ F` keeps the vertex type and deletes all edges at `F`. For `u, v ∉ F` this gives the same
  distances as `G[V \ F]`.
* The edge order is any list of the edges, in either orientation, with duplicates allowed. For
  Algorithm 4 it is sorted by weight.
* "Run BFS to find a path of length `≤ t` in `G \ F`" is an arbitrary oracle that returns some short
  walk if one exists. All theorems hold for every such oracle, i.e. for every choice of path.
* Running times are not modelled. Structurally, Algorithm 2 makes at most `α + 1` oracle calls.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3 (check only edges) | `SimpleGraph.isVFTSpanner_iff`, `SimpleGraph.isWeightedVFTSpanner_iff` | CSLib `Spanner.lean`, `WeightedSpanner.lean` |
| Theorem 4 (length-bounded cut approximation) | `lbc_correct`, `lbcEdge_correct` | `LBC.lean` |
| Theorem 5 (Algorithm 3 is an FT spanner) | `modifiedGreedy_isVFTSpanner`, `modifiedGreedyEdge_isEFTSpanner` | `Greedy.lean` |
| Lemma 6 (blocking set of size `(2k−1)f·\|E\|`) | `modifiedGreedy_exists_blockingSet` | `Size.lean` |
| Lemma 7 (exact form) | `SimpleGraph.IsBlockingSet.exists_dense_subgraph` | CSLib `BlockingSet.lean` |
| Moore bound (cited) | `SimpleGraph.NoShortCycles.ncard_edgeSet_le_rpow` (`\|E\| ≤ n^{1+1/k} + n`) | CSLib `Girth.lean` |
| Theorem 8 (`≤ 32 k f^{1−1/k} n^{1+1/k}`) | `modifiedGreedy_card_edges_le`; sharper `modifiedGreedy_card_edges_le'` | `Size.lean` |
| Theorem 10 (weighted) | `modifiedGreedy_isWeightedVFTSpanner`, `modifiedGreedyWeighted_card_edges_le`, `modifiedGreedyEdge_isWeightedEFTSpanner` | `Weighted.lean` |
| Theorem 2 (summary, without running time) | `theorem2_unweighted`, `theorem2_weighted`, `exists_vft_spanner` | `Main.lean` |

The sharper form is `8 (2(2k−1)f)^{1−1/k} n^{1+1/k}`. CSLib files are in
`Cslib/Foundations/Combinatorics/SimpleGraph/`.

**Not formalized.**
* The distributed results (Section 5, Theorems 11–15). They rest on black boxes with w.h.p.
  guarantees: padded decompositions, Baswana–Sen, and the [DK11] reduction.
* Running times (Theorem 4's `O((m+n)α)`, Theorem 9), and Algorithm 1 (motivation only).
* The size bound for *edge* faults, which the paper only asserts to be "essentially identical". EFT
  correctness is formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: valid oracles (`ShortPathOracle.exists_spec`) and weight-sorted edge lists
(`exists_sorted_edgeList`) exist, and `exists_vft_spanner` combines them. The Moore bound, which the
paper cites, is proved. The spanner, girth and blocking-set infrastructure is in CSLib
`Cslib/Foundations/Combinatorics/SimpleGraph/{Spanner,WeightedSpanner,Girth,BlockingSet}.lean`. The
generic greedy scheme (`SimpleGraph.greedyGraph`, its correctness `greedyGraph_isVFTSpanner` /
`greedyGraph_isWeightedVFTSpanner` and EFT analogues, blocking sets from insertion histories
`exists_blockingSet_of_insertion`, `exists_sorted_edgeList`) is in
`Podc/Graph/Spanner/FaultTolerantGreedy.lean`, shared with
[Bodwin–Patel](../../PODC2019/VFTSpannersOptimal).
