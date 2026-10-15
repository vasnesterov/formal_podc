# Brief Announcement: Sinkless Orientation Made Trivial

Alexandre Nolin (Télécom SudParis; also Inria, Institut Polytechnique de Paris, CISPA).
*Brief Announcement: Sinkless Orientation Made Trivial.* PODC 2026, pp. 333–336.
DOI [10.1145/3796701.3815953](https://doi.org/10.1145/3796701.3815953). Open-access PDF on HAL
(hal-05678283). No arXiv / full version was found, so the 4-page brief announcement is used.

## Status

**Done.** The deterministic part of the paper is formalized, with no `sorry` and no `axiom`.
The main theorems use only `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`):
Theorem 2.1, Lemma 2.2, Lemma 2.3, Theorem 1.1 (deterministic) and the tightness remark after
Theorem 2.1.

**Findings.** No error affects the results. There are only minor slips and remarks (see
`differencies.md`):
* the "in particular" part of Lemma 2.2 says "degree `δ`" instead of "degree `< δ`";
* the hypothesis `r ≥ 1` of Lemma 2.2 is redundant (harmless);
* the definition of `k`-sinksparse says "distance `≥ k`", while the proof gives `> k` (we
  formalize `> k`);
* Section 3's "`max(ε deg(v), 1)` incoming and outgoing edges for every node" is meant for graphs of
  minimum degree `δ ≥ 3`; read literally for arbitrary graphs it fails at degree-1 nodes
  (`no_orientation_in_and_out_single_edge`, a remark, not an error).

Not formalized: the randomized part of Theorem 1.1 and Corollary 1.2 (they rely on the external
reductions of Ghaffari–Su and Ghaffari et al.), CONGEST message sizes for Algorithm 2, and the cited
`Ω(log n)` lower bounds.

Approximate token spend: about 0.6M (paper agent and 3 subagents: Lemma 2.2, flooding run, lower bound).

## Model

* **Graphs.** `G : SimpleGraph V`. Theorem 2.1 and Lemma 2.3 hold for any `V`. Lemma 2.2 needs
  `[Finite V]` and Theorem 1.1 needs `[Fintype V]`, with `n = Fintype.card V`. The degree is
  `deg G v = (G.neighborSet v).ncard`.
* **Orientations.** `Orientation G` has a relation `out u v` ("`uv` is oriented `u → v`") that
  holds only on edges and gives every edge exactly one direction. A *sink* has no outgoing edge. A
  *`δ`-sink* is a sink of degree `≥ δ`. *`k`-sinksparse* means distinct sinks are at distance
  `> k`.
* **Distributed model.** Deterministic, synchronous, fault-free LOCAL. Identifiers are unique
  (`id : V → ℕ` injective; node names in `V` also serve as identifiers), and every node knows `n`.
  * A `T`-round algorithm is captured by **locality**. An orientation algorithm
    `A : ∀ G : SimpleGraph V, Orientation G` is `R`-local (`IsLocal A R`) if the direction of
    every edge `uv` depends only on the edges incident to nodes at distance `< R` from `u`
    (`GAgree`), which is exactly what `u` learns in `R` rounds. Since `A` is a function of the
    whole graph on `V`, a rule may also depend on the global identifier set `V` (not only `n`):
    slightly more than standard LOCAL, harmless for our explicit algorithms, and it strengthens
    the lower bound.
  * `IsLocalRel` is the same notion for transformations that also take an orientation as local
    input. `IsLocal.comp` composes the two.
  * Theorem 2.1 is in addition implemented as an explicit `k`-round broadcast algorithm in CSLib's
    synchronous SET-LOCAL model (`Cslib.LocallyIterative`), with `O(log n)`-bit states.
  * CONGEST message sizes are otherwise not formalized.
* **Randomness.** None. The randomized results are not formalized.

## Theorem ↔ Lean map

| Paper | Lean (namespace `SinklessOrientation`) | File |
|---|---|---|
| sink, `δ`-sink, `k`-sinksparse | `Orientation.IsSink`, `IsDeltaSink`, `NoDeltaSink`, `IsSinkSparse` | `Basic.lean` |
| LOCAL rounds | `GAgree`, `IsLocal`, `IsLocalRel`, `IsLocal.comp` | `Basic.lean` |
| Theorem 2.1, orientation by `(m_v, d_v, ID_v)` | `minId`, `leader`, `minDist`, `key`, `keyLt`, `minIdOrientation` | `MinId.lean` |
| Theorem 2.1, correctness | `minIdOrientation_isSinkSparse` (non-minima are not sinks: `minIdOrientation_not_isSink`) | `MinId.lean` |
| Theorem 2.1, `O(k)` rounds | `minIdOrientation_isLocal` (`k+1` rounds); explicit flooding `floodAlg`, `floodAlg_run`, `floodAlg_orientation`, `theorem_2_1` | `MinId.lean`, `MinIdRun.lean` |
| Tightness remark after Theorem 2.1 | `sinkSparse_lower_bound`, `sinkSparse_rounds_ge` (see below) | `LowerBound.lean` |
| Lemma 2.2 | `lemma_2_2` (stronger: `lemma_2_2'`; counting core: `card_cball_ge_of_not_hasBackEdges`) | `Lemma22.lean` |
| Lemma 2.2, "in particular" | `lemma_2_2_clog`, `lemma_2_2_of_card_le` | `Lemma22.lean` |
| cycle in a ball ⇔ non-tree edge of the BFS ball | `hasBackEdges_of_containsCycle`, `containsCycle_of_hasBackEdges` | `Lemma22.lean` |
| Algorithm 2 | `par`, `anc`, `lowSet`, `ntSet`, `RepPath`, `RepCycle`, `repair`, `repairOrientation` | `Reorient.lean` |
| Lemma 2.3, correctness | `lemma_2_3` (paper's hypotheses; `Main.lean`), `lemma_2_3_core` | `Main.lean`, `Reorient.lean` |
| Lemma 2.3, `O(k)` rounds | `repairOrientation_isLocal` (`2h+1` rounds, `h = ⌊k/2⌋`) | `Reorient.lean` |
| Algorithm 1 | `sinklessAlg` (`k = 4⌈log_{δ−1} n⌉`) | `Main.lean` |
| **Theorem 1.1** (deterministic) | `theorem_1_1`: no `δ`-sinks, and `16⌈log_δ n⌉ + 2` rounds; also `sinklessAlg_noDeltaSink`, `sinklessAlg_isLocal` (`8⌈log_{δ−1} n⌉ + 2`) | `Main.lean` |
| Theorem 1.1 (randomized), Corollary 1.2 | not formalized | — |
| Section 3, `max(ε deg, 1)` phrasing | `no_orientation_in_and_out_single_edge` (remark: literal reading fails at degree 1) | `Main.lean` |

### Tightness of Theorem 2.1

The paper says only that the bound "is obviously tight, even in Local", by a standard argument.
`sinkSparse_lower_bound` proves it. Let `A` be a `T`-local algorithm with `2T + 2 ≤ k`, and let `V`
have `2T + 2 + 3k` distinct nodes. Then some path on `k + 1` nodes (all other nodes isolated) gets
two sinks from `A`. So `k`-sinksparse orientations need about `k/2` rounds, while `k + 1` suffice.

The proof is the classical reflection argument. On a path with `k + 1` nodes, a `k`-sinksparse
orientation has exactly one sink, so it has no internal source. A `T`-round algorithm orients an
edge the same way in a block of IDs and in its mirror image. Placing a block, its reversal and the
block again on a line therefore forces a source.

## Infrastructure / CSLib candidates

* `Basic.lean` (CSLib candidate): edist helpers, plus `GAgree`, `IsLocal`, `IsLocalRel` and
  `IsLocal.comp`. `GAgree.symm`, `GAgree.edist_eq` and `GAgree.mono` give locality by agreement
  of radius-`R` views. This is reusable for other LOCAL upper or lower bounds with edge outputs.
* `Lemma22.lean` (CSLib candidates, marked):
  * a cycle in a ball exists iff the BFS ball has a non-tree edge;
  * counting core: a ball of radius `r` without low-degree nodes and without non-tree edges has at
    least `1 + δ ∑_{i<r} (δ−1)^i` nodes. This is a Moore-type bound for balls, which complements
    CSLib's `Girth.lean`.
* `Reorient.lean`: BFS parent pointers `par G s` and ancestors `anc` for a possibly disconnected
  graph. CSLib's `Connected.bfsTree` needs connectivity.
