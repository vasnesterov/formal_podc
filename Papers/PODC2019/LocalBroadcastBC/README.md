# Exact Byzantine Consensus on Undirected Graphs under Local Broadcast Model

Muhammad Samir Khan, Syed Shalan Naqvi, Nitin H. Vaidya. *Exact Byzantine Consensus on Undirected
Graphs under Local Broadcast Model.* PODC 2019, pp. 327–336. DOI
[10.1145/3293611.3331619](https://doi.org/10.1145/3293611.3331619), arXiv
[1903.11677](https://arxiv.org/abs/1903.11677) (v2, the full version with appendices; used here).

## Status

**Done. No `sorry` or `axiom`.** `lean_verify` on `consensus_iff`, `theorem_4_1`, `theorem_5_1`,
`complete_iff` and `not_theorem_4_1_single_node` shows only `propext`, `Classical.choice` and
`Quot.sound`. `lake build Papers.PODC2019.LocalBroadcastBC.Main` succeeds without warnings
(apart from the generic "imports Mathlib … module system" notice).

The main result (Sections 4–5: minimum degree `≥ 2f` and `(⌊3f/2⌋+1)`-connectivity are necessary
and sufficient) is formalized completely, including the algorithm (flooding with rules (i)–(iv),
steps (b), (c)) and Menger's theorem.

**The main result is correct**, with one missing hypothesis. Theorem 4.1 (and Lemma A.2) is false
in the degenerate case `n = 1`, `f = 0`, the single-node graph (Lean counterexample
`not_theorem_4_1_single_node`). It holds for all `n ≥ 2`.
Lemma A.2's proof only handles graphs with a small vertex cut; the case "`G` complete with
`n ≤ ⌊3f/2⌋+1`" is covered by Lemma A.1 only for `f ≥ 1`. There are also smaller gaps: step (b)
must use *simple* paths, and the completeness half of Observation B.1 is used but not stated. All
details are in `differencies.md`.

Not formalized: Theorem 5.6 / Appendix C (an `O(n)`-round algorithm for `2f`-connected graphs) and
Section 6 / Appendix D (the hybrid model with equivocating faults).

Rough token spend: about 0.6M tokens (paper agent plus one subagent for Menger's theorem).

## Model (explicit choices)

* **Network.** A finite node type `V` (`n = |V|`) with a Mathlib `SimpleGraph V` (undirected, no
  loops). Every node knows `G`: the algorithm is a function of `G`.
* **Synchrony.** CSLib's synchronous lock-step model `Cslib.Byzantine.LockStep`: deterministic,
  history-based protocols (`Protocol.send p x h q`, `Protocol.decide p x h`), static Byzantine set,
  reliable links, `Decides` = first decision.
* **Local broadcast** (`Model.lean`). The model is the restriction in which *every* message is
  received identically by all neighbours of its sender:
  * honest protocols broadcast (`IsBroadcast alg`: `send p x h q` does not depend on `q`);
  * the Byzantine adversary broadcasts (`IsLocalBroadcast s`: `adv r p q` does not depend on `q`).
  The adversary is otherwise arbitrary: its messages are an arbitrary function of the round, which
  for deterministic protocols covers adaptive, rushing adversaries.
  `SolvesLB G alg Z spec`, `SolvableLB G Z spec` (some broadcast protocol, with any message type in
  the universe of `V`, solves `spec` against all admissible Byzantine sets).
* **Faults.** Threshold adversary `atMost f` (`|B| ≤ f`, as `Set.ncard`).
* **Specification** (`Consensus`, Section 3): termination, validity ("the output of each
  non-faulty node is the input of some non-faulty node"), agreement. Inputs and outputs are `Bool`.
  For binary values this is CSLib's `BA` (`consensus_iff_BA`).
* **Connectivity** (`Cslib/Foundations/Combinatorics/SimpleGraph/VertexConnectivity.lean`). West's definition, as in the paper:
  `G.IsVertexConnected k` iff `k < n` and removing fewer than `k` vertices does not disconnect `G`
  (`ReachableAvoiding`).
* **Algorithm 1** (`Algorithm.lean`). Messages are sets of pairs `(b, Π)` (`Msg V`). A Byzantine
  node may send any set, even infinite or containing both `(0, Π)` and `(1, Π)`. Phases: one for
  every `F` with `|F| ≤ f`, in an arbitrary fixed order (`phases f`). Each phase has `n` flooding
  rounds. Rules (i)–(iv) and the default message `(1, ⊥)` are as in the paper. Step (b) uses an
  arbitrary path selection `sel` with `SelSpec` (simple `uv`-paths excluding `F`); the correctness
  theorem holds for every such `sel`. Step (c) is as in the paper; "node-disjoint `A_v v`-paths"
  may be walks, as in the paper. Remaining ambiguities are resolved deterministically (see
  `differencies.md`). Nodes decide `γ` after all `|phases| · n` rounds.

## Theorem ↔ Lean map

Files: `Model.lean`, `Necessity.lean`, `Counterexample.lean`, `Algorithm.lean`, `Phase.lean`,
`Flooding.lean`, `Paths.lean`, `Sufficiency.lean`, `Main.lean`. Namespace `LocalBroadcastBC`.
Graph infrastructure in `Cslib/Foundations/Combinatorics/SimpleGraph/{VertexConnectivity,Menger}.lean` (namespace `SimpleGraph`).

| Paper | Lean |
|---|---|
| Model (§3), local broadcast | `IsBroadcast`, `IsLocalBroadcast`, `SolvesLB`, `SolvableLB`, `atMost`, `Consensus` |
| `k`-connectivity (§3) | `SimpleGraph.IsVertexConnected`, `SimpleGraph.ReachableAvoiding` |
| Menger / fan lemma (§3, [West]) | `SimpleGraph.menger`, `SimpleGraph.fan`, `SimpleGraph.IsVertexConnected.fan` (`Cslib/Foundations/Combinatorics/SimpleGraph/Menger.lean`) |
| Covering networks of Appendix A | `CoverSystem'.lbScenario`, `CoverSystem'.LBLift`, `CoverSystem'.decides_lbScenario_iff`, `twoCopy`, `twoCopy_lift`, `three_scenarios` |
| Lemma A.1 | `lemmaA1` |
| Lemma A.2 | `lemmaA2` (no vertex cut of size `≤ ⌊3f/2⌋`) |
| **Theorem 4.1** (necessity) | `theorem_4_1` (with the extra hypothesis `2 ≤ n`) |
| counterexample to literal Thm 4.1 / Lemma A.2 | `not_theorem_4_1_single_node` (`n = 1`, `f = 0`); `not_degree_single_node` (`f < n` is needed) |
| Algorithm 1 | `alg1` (`readVal`, `newVal` = rules (i)–(iv), `recv`, `Zset`, `sets` = cases 1–4, `Accepts`, `update` = steps (b)–(c), `phases`) |
| Observation B.1 (+ completeness) | `FloodOutcome`, `floodInv`, `floodOutcome`; flooded value `fv` |
| Lemma 5.2 | `lemma_5_2` |
| Lemma 5.3 | `lemma_5_3` (with `zset_eq`) |
| Lemma 5.4 | `exists_selSpec` (`SelSpec`) |
| Lemma 5.5 | `pathsExist` (`PathsExist`, `DisjointPaths`; cases `disjointPaths_fan`, `disjointPaths_degree`) |
| **Theorem 5.1** (sufficiency) | `theorem_5_1`, `alg1_solves` |
| Theorems 4.1 + 5.1 | **`consensus_iff`**: for `f < n`, `n ≥ 2`, `SolvableLB G (atMost f) Consensus ↔ 2f ≤ δ(G) ∧ G.IsVertexConnected (⌊3f/2⌋+1)` |
| §2 remark: complete graph ⇔ `n ≥ 2f+1` | `complete_iff`, `top_isVertexConnected` |

## Proof notes

* **Necessity.** Both lemmas are FLM-style covers with two copies of every node
  (`twoCopy c xq` on `V × Bool`; `c u i v` is the copy of the neighbour `v` that copy `(u, i)` listens
  to). All Byzantine nodes are *single* nodes of the cover, so the simulating adversary is a local
  broadcast adversary (`lbScenario`, `hist_lbScenario`). `three_scenarios` does the
  `E₁/E₂/E₃` argument once; Lemmas A.1 and A.2 only define `c`, the inputs and three lifts, and
  check the lift conditions by case analysis.
* **Flooding.** `floodInv` is an induction over the `n` rounds of a phase. It tracks, for every
  non-faulty node, which paths `K` have been accepted, when (round `|K| - 1`), and with which value
  (the value `fv K.head` flooded by the first node, if all other nodes of `K` are non-faulty).
  The default message `(1, ⊥)` in round 0 is what fixes the timing for faulty originators.
* **Sufficiency.** `Phase.lean` proves Lemmas 5.2/5.3 for an abstract `FloodOutcome`.
  `Sufficiency.lean` chains the phases: a validity invariant, then agreement from the phase with
  `F = B` onwards.

## Infrastructure and CSLib candidates

* `Cslib/Foundations/Combinatorics/SimpleGraph/VertexConnectivity.lean` (new, now in CSLib): `ReachableAvoiding`, `Separates`,
  `IsVertexConnected`.
* `Cslib/Foundations/Combinatorics/SimpleGraph/Menger.lean` (new, now in CSLib, ~600 lines): Menger's theorem (vertex, set
  version) by Göring's proof, implemented by *merging* an edge on the same vertex type; the fan lemma.
  Mathlib has no vertex Menger theorem.
* `Model.lean`: local broadcast predicates on top of CSLib `LockStep`, and the covering lemma with
  single-copy Byzantine nodes (`CoverSystem'.lbScenario`, `decides_lbScenario_iff`). **CSLib
  candidate** as an addition to `LockStep/Cover.lean`.
* `Paths.lean`: `restrictGraph` (delete all edges at a vertex set) and walk transfer
  (`exists_walk_restrictGraph`). Small **CSLib candidate**, together with the walk-to-list lemmas
  `walk_support_spec`, `ne_head_of_mem_internal`, `ne_last_of_mem_internal`.
