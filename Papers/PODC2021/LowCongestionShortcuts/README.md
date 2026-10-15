# Low-Congestion Shortcuts for Graphs Excluding Dense Minors (PODC 2021)

Mohsen Ghaffari, Bernhard Haeupler. *Low-Congestion Shortcuts for Graphs Excluding Dense Minors.*
PODC 2021, pp. 213–221, DOI 10.1145/3465084.3467935; full version arXiv:2008.03091v1 (formalized; numbering
follows it). Cited below as [GH21].

## Status

**Complete for the combinatorial core; no `sorry`, no axioms** (main theorems checked with `lean_verify`: only
`propext`, `Classical.choice`, `Quot.sound`).

- **Theorem 3.1** (main theorem): proved, with block number `8δ + 1` instead of `8δ` (the paper's case (I)
  forgets the block containing the root). Congestion `8δD` as in the paper. Holds for every `δ ≥ δ(G)`. The literal
  `8δ`-block statement is false on the one-vertex graph (`theorem_3_1_literal_false_singleton`).
- **Observation 2.6**: proved under the extra hypothesis that every block contains a vertex of its part; **as stated
  in the paper it is false** (Lean counterexample). The paper's own shortcuts satisfy the hypothesis.
- **Observation 2.7**: proved with congestion `c(⌊log₂ n⌋ + 1)` instead of `c log₂ n` (one more halving round).
- **Theorem 1.2** (existential): every connected `n`-vertex graph with diameter `≤ D` admits shortcuts with
  congestion `8δD(⌊log₂ n⌋ + 1)` and dilation `(8δ + 1)(2D + 1)` (even tree-restricted), `δ = δ(G)`.
- **Lemma 3.2** (lower bound): not formalized (needs planarity / Euler's formula, absent from Mathlib). We found that
  the **construction in its proof violates the claimed diameter bound**: for `δ' = 5, D' = 12` it has diameter ≥ 15
  (Lean proof that two vertices are at distance exactly 15). Repairable by rescaling (numerical evidence only).
- Not formalized (distributed algorithms / cited results / other graph parameters): Lemma 1.1 [Tho01], Lemma 2.8
  [HHW18, HIZ16a], Theorem 1.5, Corollaries 1.4, 1.6, 1.7, 3.4, Lemma 3.3 (genus/treewidth bounds; no genus or
  treewidth theory in Mathlib), Lemma 1.3.

See `differencies.md` for all deviations.

## Model (explicit)

Purely graph-theoretic; no distributed model is formalized (the paper's CONGEST algorithms come from cited work).
- `G : SimpleGraph V`, `V` finite. "Diameter `D`": `G.Connected` and `∀ u v, G.dist u v ≤ D`.
- Rooted spanning tree of depth `≤ D`: `G.RootedTree` (root, parent pointers, depths; `T.DepthLE D`).
- Parts: `P : ι → Finset V`, pairwise disjoint, each inducing a connected subgraph (`G.IsParts P`).
- Shortcut: `H : ι → Finset (Sym2 V)` (edge sets). Congestion `≤ c` (`CongestionLE`): every edge of `G` lies in at
  most `c` of the `H i`. Dilation `≤ d` (`DilationLE`): any two vertices of `P i ∪ V(H i)` are joined by a path of
  length `≤ d` in `G[P i] + H i`. Blocks (`numBlocks`): number of connected components of `(P i ∪ V(H i), H i)`.
- Minor density: `G.MinorDensityLE δ` — every minor `H` (branch-set model) has `|E(H)| ≤ δ |V(H)|`;
  `G.minorDensity` = sup (attained) of `|E(H)|/|V(H)|`.
- Randomness: the probabilistic-method step (independent Bernoulli(`1/(4D)`) choice of parts) is a weighted sum over
  all subsets with explicit product weights (`Bernoulli.lean`), no measure theory.

## Theorem ↔ Lean map

| Paper | Lean | File |
|---|---|---|
| Def. 2.2 (shortcut, congestion, dilation) | `SimpleGraph.CongestionLE`, `SimpleGraph.DilationLE`, `partGraph` | `Cslib/Foundations/Combinatorics/SimpleGraph/Shortcut.lean` |
| Def. 2.3 (tree-restricted, blocks) | `RootedTree.Restricts`, `numBlocks`, `BlocksMeetPart` | `Cslib/Foundations/Combinatorics/SimpleGraph/Shortcut.lean` |
| Def. 2.4 / 2.5 (admitting (partial) shortcuts) | `AdmitsTreeShortcuts`, `AdmitsPartialTreeShortcuts` | `Cslib/Foundations/Combinatorics/SimpleGraph/Shortcut.lean` |
| minors, `δ(G)` (Sec. 1.1) | `MinorModel`, `IsMinor`, `MinorDensityLE`, `minorDensity` | `Cslib/Foundations/Combinatorics/SimpleGraph/Minor.lean` |
| Observation 2.6 | `LowCongestionShortcuts.observation_2_6` | `Observations.lean` |
| Obs. 2.6 is false as stated | `observation_2_6_counterexample` | `Observations.lean` |
| Observation 2.7 | `observation_2_7` | `Observations.lean` |
| **Theorem 3.1** | `theorem_3_1` (`δ ≥ δ(G)`), `theorem_3_1_minorDensity` | `Theorems.lean` |
| overcongested edges `O` (greedy) | `exists_stable` | `Overcongested.lean` |
| representatives `r_(e,P_i)` | `exists_rep` (topmost) | `Overcongested.lean` |
| case (I): shortcut, congestion, blocks | `shortcut`, `card_filter_mem_shortcut_le`, `numBlocks_shortcut_le`, `blocksMeetPart_shortcut` | `Overcongested.lean` |
| case (II): minor `B_{P'}` is a minor | `branch_connected`, `branch_disjoint`, `present_adj`, `card_present_le` | `DenseMinor.lean` |
| case (II): `Pr[potentially present] ≥ 3/4` | `exists_blocker` | `DenseMinor.lean` |
| case (II): expectation / contradiction | `caseII_false`, `final_arith` | `Main.lean` |
| Thm 3.1 literal (`8δ` blocks) false | `theorem_3_1_literal_false_singleton` | `Literal.lean` |
| **Theorem 1.2** | `theorem_1_2` (`δ = δ(G)`), `theorem_1_2_of_minorDensityLE` | `Theorems.lean` |
| Lemma 3.2 construction, diameter claim | `LowerBound.lbGraph`, `paperGraph_dist_eq`, `paperGraph_not_diam_le` | `LowerBoundGraph.lean` |

## Infrastructure built (migrated to CSLib `Cslib/Foundations/Combinatorics/SimpleGraph/`)

- `RootedTree.lean`: rooted spanning trees via parent pointers + depth; iterates of `parent`, tree edges
  (`edge_injective`), `climb` (climb along a set of tree edges) with induction principle.
- `BFSTree.lean`: BFS trees; `exists_rootedTree_depthLE` (diameter `≤ D` ⇒ spanning tree of depth `≤ D`).
- `Minor.lean`: minor models, `IsMinor` (refl, trans, subgraphs/copies/isos), minor density
  (`MinorDensityLE`, `minorDensity`, attained, `minorDensity_le_iff`), `half_le` (an edge ⇒ `δ ≥ 1/2`),
  `bipartite_card_le` (bipartite minors from branch sets — the workhorse of density arguments).
- `Shortcut.lean`, `ShortcutLemmas.lean`: shortcut definitions (congestion, dilation, blocks, (partial) admittance)
  and the generic block ⇒ dilation lemma `RootedTree.dilationLE_of_numBlocks_le`.
- Paper folder, reusable: `Bernoulli.lean` (independent Bernoulli subsets as finite sums: `sum_bernWeight_indicator`,
  probabilistic method); `LowerBoundGraph.le_add_dist_of_lipschitz` (Lipschitz-potential lower bounds on `dist`).

The graph infrastructure has been migrated to CSLib (`Cslib/Foundations/Combinatorics/SimpleGraph/*`; `Minor.lean` and
`BFSTree.lean` are even Mathlib-level). **Remaining CSLib candidates:** `Bernoulli.lean`,
`le_add_dist_of_lipschitz`.

## Effort

Roughly 0.6M tokens in total (main agent ≈ 0.35M, three subagents ≈ 0.25M: minor API, Observations + BFS trees,
Lemma 3.2 counterexample). About 2200 lines of Lean.
