# Message Reduction in LOCAL — PODC 2019

Shimon Bitton, Yuval Emek, Taisuke Izumi, Shay Kutten. *Message Reduction in the LOCAL Model is a Free
Lunch.* PODC 2019. DOI [10.1145/3293611.3331582](https://doi.org/10.1145/3293611.3331582). Formalized
version: arXiv [1909.08369](https://arxiv.org/abs/1909.08369) v1; numbering follows it.

**Verdict: ❌ False claim.** The size bound of Theorem 1.2 and Lemma 4.7 is false for algorithm
`Sampler` as written: `|S|` is `Õ(n^{1+δ+ε})`, not `Õ(n^{1+δ})` (`ε = 1/h`). The stretch analysis
holds: we prove the deterministic core of Theorem 4.6 (stretch `2·3^k − 1`), Lemmas 4.4 and 4.5, and the
probabilistic core of Lemma 4.3 for one node, including the adaptive trials. The headline claims
survive: the abstract's spanner (constant stretch, `O(n^{1+ε})` edges and messages, `O(1)` rounds) and
the message-reduction scheme (Theorem 1.3). The corrected size equals the message bound the paper already
uses.

## Mistakes in the paper

* **Theorem 1.2 and Lemma 4.7 (size `Õ(n^{1+δ})`) are false.** In every trial of `Cluster_j`, every
  node samples `s_j = c² n^{2^j δ + ε} log³ n` edges and keeps one edge per queried neighbour in `F_v`.
  The test `|F_v| < c n^{2^j δ} log n` (Pseudocode 2, line 4) is made only *between* trials, so the
  last trial can add up to `s_j` edges. The proof of Lemma 4.7 counts `O(n^{2^j δ} log³ n)` edges per
  trial and node, dropping the factor `n^ε`. Counterexample: `k = 1`, `h = 2` (`δ = 1/3`, `ε = 1/2`),
  `G = K_n`, any constant `c ≥ 1`. In the first trial of level 0 every node draws `≈ c² n^{5/6} log³ n`
  of its `n − 1` edges, and all distinct draws enter `S`. A node hits at least `s/2` distinct
  neighbours on average, and an edge is counted at most twice. So, by a reverse Markov argument, with
  probability `≥ 1/8` this single trial already puts `≥ n·s/8 ≈ n^{11/6}` edges into `S`. For all large
  `n` this exceeds `C · n^{4/3} · log^D n`, for any `C`, `D`. So `|S| = Õ(n^{1+δ})` fails with
  probability `≥ 1/8`, not `n^{−c}` (`theorem_1_2_size_false`, `first_trial_large`). The correct bound
  is `|F_v| < τ_j + s_j` (`Setup.card_F_lt`). Summed over the levels (with Lemma 4.1) this gives
  `|S| = Õ(n^{1+δ+ε})`, the same as the message complexity. Theorem 1.2 holds after this change of the
  size bound, or after capping `F_v` at the threshold inside a trial. Theorem 1.3 / Lemma 6.1 are
  unaffected: they set `ε = δ` and only need `|S| = Õ(n^{1+2δ})`.
* **Lemma 4.3's volume classes miss volume 1 (proof slip).** Class `x` is defined by
  `|E_j(v,u)| ∈ (n^{xε}, n^{(x+1)ε}]`, which excludes neighbours with a single edge. At level 0
  (simple `G_0`) these are *all* neighbours, so the maximum class need not carry `m_i/2h` of the
  volume. With the classes `[n^{xε}, n^{(x+1)ε})` the proof goes through. We also needed the unstated
  `α ≥ 6` for `⌊(β−1)α/β⌋ ≥ α/3`; it holds for the paper's `α`. Lemma 4.3 is proved for one node, with the
  `2h` adaptive trials and the union bound made explicit (`Setup.lemma_4_3_node`). The paper's
  "abuse of probabilistic arguments" is harmless here: each trial fails with probability
  `≤ |N|(1 − θ)^s` conditionally on any history.
* **Typos and small slips.**
  - `V' = ⋃_{1≤j≤k−1} V'_j` (before Lemma 4.5) should range over `0 ≤ j ≤ k`, as the proof of
    Theorem 4.6 uses ("any node in `G_k` is unclustered").
  - Theorem 1.2 allows `h = 0`, but `ε = 1/h`.
  - The prose says a node joins a center in `N̂_j(v)` (an edge of `F_v`); Pseudocode 2, line 19, uses any
    edge of `F = ⋃ F_u`. The stretch proof works with either rule; we formalize the pseudocode.
  - The proof of Lemma 4.5 speaks of a spanning tree of "height" `3^j − 1`; its induction bounds the
    diameter, which is what the lemma states.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The centralized algorithm of Sections 3–4 (`Sampler`, `Cluster_j`) on a finite simple graph `G_0`.
  The distributed implementation (Section 5: synchronous LOCAL with unique edge IDs, broadcast-convergecast
  in clusters) and the simulation scheme (Section 6) are not formalized.
* Stretch (`Hierarchy.lean`): a `Run G k` is **any outcome** of the coins, given by merge maps, center
  marks and the edge sets `F_a` of all levels, subject to the postconditions of Pseudocode 2. Level-`j`
  nodes are identified with their root vertex, and the multigraph `G_j` is represented by the original
  edges between clusters. So parallel edges are exactly the paper's `E_j(a, b)`. Theorem 4.6 is proved
  for every run that satisfies the conclusions of Lemmas 4.2/4.3 (every node light or with a queried
  center; every level-`k` node light). This is the paper's own split into "whp facts" and a
  deterministic argument.
* Randomness: finite uniform sample spaces with probabilities by counting (CSLib `uprob`). Lemma 4.3
  (`Lemma43.lean`) models one node `v` with an arbitrary multigraph neighbourhood (volumes
  `1 ≤ vol u < b^L`). The `L` adaptive trials draw from the current `X_v`. Each sample is a uniform
  number in `Fin M`, `M = (vol N)!`, decoded into an exactly uniform edge of the current `X_v`
  (`uprob_decode`). The bound is unconditional over the whole adaptive process.
* Size counterexample: the first trial of `Cluster_0` on a simple graph. Every node samples `s` of its
  incident edges uniformly with replacement; we count the query edges, which all lie in `S`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 4.4 (Peleg–Schäffer cluster spanner) | `SimpleGraph.isSpanner_of_clusters` | `Podc/Foundations/Combinatorics/SimpleGraph/ClusterSpanner.lean` |
| Lemma 4.5 (cluster diameter `≤ 3^j − 1` in `Ind_H`) | `Run.lemma_4_5` | `Hierarchy.lean` |
| Lemmas 4.2+4.3 ⇒ unclustered nodes are light | `Run.light_of_unclustered` | `Hierarchy.lean` |
| Theorem 4.6 (stretch `2·3^k − 1`, deterministic core) | `Run.theorem_4_6` | `Hierarchy.lean` |
| Lemma 4.3 (one node: light or heavy, failure `≤ L·|N|·(1−θ)^s`) | `Setup.lemma_4_3_node` | `Lemma43.lean` |
| Lemma 4.3, deterministic peeling over the `2h` classes | `Setup.light_or_heavy_of_good` | `Lemma43.lean` |
| Lemma 4.3, one trial / groups / class volumes | `Setup.uprob_not_good_le`, `volOf_group_ge`, `subset_or_le_card_of_hit`, `exists_heavy_class` | `Lemma43.lean`, `Trial.lean` |
| Lemma 4.3 parameters (`τ ≤ α/3`, `α ≥ 6`, `(1−θ)^s ≤ n^{−c/6}`) | `lemma_4_3_parameters` | `Parameters.lean` |
| Lemma 4.2 (bound `(1−p)^m ≤ n^{−c}`) | `lemma_4_2_bound` | `Parameters.lean` |
| Lemma 4.7 / Theorem 1.2 size: **false** | `theorem_1_2_size_false`, `first_trial_large` | `SizeCounterexample.lean` |
| Lemma 4.7 corrected (per node `|F_v| < τ + s`; exponent `1+δ+ε`) | `Setup.card_F_lt`, `size_exponent` | `Lemma43.lean`, `Parameters.lean` |
| `p̂_{j−1} = n^{−(2^j−1)δ}`, `1 − (2^k−1)δ = 2^k δ` | `prod_p`, `one_sub_mul_delta` | `Parameters.lean` |

**Not formalized.** Lemma 4.1 (Chernoff concentration of `n_j`) and the union bound over all nodes and
levels. Section 5 (round/message complexity of the LOCAL implementation, Theorem 5.1) and Section 6
(Lemma 6.1, Theorem 1.3; the second scheme relies on Derbel et al.).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `Run.trivialRun` satisfies all run axioms and the hypotheses of
Theorem 4.6, and `lemma_4_3_parameters` shows that the paper's parameters satisfy the hypotheses of
`Setup.lemma_4_3_node`. Spanners are CSLib's `SimpleGraph.IsSpanner` (`Cslib.Foundations.Combinatorics.SimpleGraph.Spanner`).
CSLib candidate: `Podc/Foundations/Combinatorics/SimpleGraph/ClusterSpanner.lean`.
