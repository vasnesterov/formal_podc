# Byzantine Consensus under Local Broadcast — PODC 2019

Muhammad Samir Khan, Syed Shalan Naqvi, Nitin H. Vaidya. *Exact Byzantine Consensus on Undirected Graphs
under Local Broadcast Model.* PODC 2019. DOI
[10.1145/3293611.3331619](https://doi.org/10.1145/3293611.3331619). Formalized version: arXiv
[1903.11677](https://arxiv.org/abs/1903.11677) v2 (full version with appendices).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The characterization holds for every graph with at least two nodes: under
local broadcast, consensus tolerating `f` Byzantine faults is solvable iff the minimum degree is
`≥ 2f` and the graph is `(⌊3f/2⌋+1)`-connected. Theorem 4.1 (necessity) is false only in the degenerate
single-node case `n = 1, f = 0`. The sufficiency proof has fixable gaps: step (b) needs simple paths,
and Observation B.1 is used in an unstated direction.

## Mistakes in the paper

* **Theorem 4.1 / Lemma A.2 are false for the single-node graph.** The paper uses West's definition:
  `k`-connected requires `n > k`. With `n = 1`, `f = 0` (allowed by the standing assumption `f < n`),
  consensus is trivial, since the node decides its own input. But the graph is not 1-connected. The
  proof of Lemma A.2 starts "not `(⌊3f/2⌋+1)`-connected ⇒ there is a vertex cut of size
  `≤ ⌊3f/2⌋`". This misses complete graphs with `n ≤ ⌊3f/2⌋ + 1`, which have no cut. For `f ≥ 1`,
  Lemma A.1 (degree `≥ 2f`) excludes them; for `f = 0` only the single-node graph remains. The same
  case breaks the §4 remark that the complete graph on `2f + 1` nodes satisfies the conditions "for
  any `f`". We prove the statement under `n ≥ 2`. The hypothesis `f < n` is also needed: for
  `n = 1`, `f = 1` consensus is solvable but the minimum degree is `0 < 2`.
  (`not_theorem_4_1_single_node`, `not_degree_single_node`; repaired: `theorem_4_1`)
* **Step (b) of Algorithm 1 needs simple paths; proof gap.** The paper lets `P_uv` be an arbitrary
  `uv`-path avoiding `F`, and its paths are walks. If `P_wv` repeats a node `x`, then `x` discards
  the value forwarded back to it by rule (iii). So `v` receives nothing along `P_wv` and wrongly puts
  `w` into `N_v`, even when `w` flooded `0`. The step "`v` receives 0 along `P_wv` and correctly puts
  `w` in `Z_v`" in Lemma 5.3 then fails. With simple paths, which Lemma 5.4 provides, the proof goes
  through.
* **Observation B.1 is used in an unstated direction.** It states soundness: a value received along
  a fault-free path is the origin's value. Lemma 5.3 also needs completeness: along every fault-free
  *simple* path the value *does* arrive within the phase's `n` rounds. This depends on the default
  message `(1, ⊥)` and on the round in which each path prefix is accepted. For a faulty originator,
  "the value it floods" must be defined, as what its first-round transmission says about `⊥`. We
  prove both directions.
* **Smaller gaps.**
  * Lemma 5.3 applies Lemma 5.5 to faulty `w`, but Lemma 5.5 is stated only for non-faulty nodes;
    its proof works for any `w`.
  * Lemma A.1's cover is described inconsistently: item 4 and the figure orient the `F²`–`W` edges
    oppositely. The executions need item 4's version.
  * Lemma A.2's cover edges are only "deduced from Figure 3"; we give them explicitly.
  * Both covers tacitly need each Byzantine node to be simulated by a *single* cover node, so that
    it can still broadcast.
  * Lemma 5.4 cites Menger, but it follows from the definition of connectivity.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finite node set with a simple undirected graph known to all nodes. Synchronous lock-step rounds
  (CSLib `LockStep`). Protocols are deterministic and history-based, and may use any message type.
* Local broadcast is a restriction on both sides. Honest protocols send the same message to all
  neighbours. The Byzantine adversary (static set, `|B| ≤ f`: the shared threshold structure
  `atMost f` of `Cslib/Computability/Distributed/Byzantine/LockStep/Parallel.lean`) also broadcasts, but is otherwise arbitrary (covers
  adaptive, rushing adversaries).
* Consensus (§3): termination, agreement (the shared `Problem.Termination`, `Problem.Agreement`),
  and validity (output = input of some non-faulty node); binary values.
* Impossibility quantifies over all broadcast protocols. Possibility uses Algorithm 1, with phases for
  every `F` with `|F| ≤ f` in an arbitrary fixed order, `n` flooding rounds each, and rules (i)–(iv).
  Ambiguities (ordering within a transmission, ties in step (c)) are resolved deterministically, and
  the proof works for every choice of simple paths in step (b). Byzantine nodes may send arbitrary,
  even contradictory, sets of pairs.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorems 4.1 + 5.1 (for `f < n`, `n ≥ 2`) | `consensus_iff` | `Main.lean` |
| Lemmas A.1, A.2 | `lemmaA1`, `lemmaA2` | `Necessity.lean` |
| Theorem 4.1 (with `n ≥ 2`) | `theorem_4_1` | `Necessity.lean` |
| Theorem 4.1 false for `n = 1` | `not_theorem_4_1_single_node`, `not_degree_single_node` | `Counterexample.lean` |
| Observation B.1 (both directions) | `floodInv` | `Flooding.lean` |
| Lemmas 5.2, 5.3 | `lemma_5_2`, `lemma_5_3` | `Phase.lean` |
| Lemmas 5.4, 5.5 | `exists_selSpec`, `pathsExist` | `Paths.lean` |
| Theorem 5.1 (Algorithm 1 correct) | `theorem_5_1`, `alg1_solves` | `Sufficiency.lean` |
| §2 remark: complete graph ⇔ `n ≥ 2f+1` | `complete_iff` | `Main.lean` |

**Not formalized.** Theorem 5.6 / Appendix C (the `O(n)`-round algorithm for `2f`-connected graphs) and
Section 6 / Appendix D (the hybrid model with equivocating faults).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The necessity proofs are FLM-style covers with two copies per node, done once in
`three_scenarios`. Menger's theorem (vertex version) and the fan lemma were formalized for this paper,
since Mathlib has none: `SimpleGraph.menger`, `SimpleGraph.fan` in CSLib
`Cslib/Foundations/Combinatorics/SimpleGraph/Menger.lean`, with connectivity in
`VertexConnectivity.lean` next to it; removing vertices without changing the vertex type is CSLib's
`SimpleGraph.deleteVerts` (`Spanner.lean`). The round model is CSLib's `LockStep` (delivery lemmas
`deliver_honest`/`deliver_byz` from `Cslib/Computability/Distributed/Byzantine/LockStep/Parallel.lean`).
