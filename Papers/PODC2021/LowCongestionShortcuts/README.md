# Low-Congestion Shortcuts for Graphs Excluding Dense Minors — PODC 2021

Mohsen Ghaffari, Bernhard Haeupler. *Low-Congestion Shortcuts for Graphs Excluding Dense Minors.* PODC 2021,
pp. 213–221. DOI [10.1145/3465084.3467935](https://doi.org/10.1145/3465084.3467935). Formalized version: full
version arXiv:2008.03091v1 (numbering follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main result is proved: Theorem 3.1, and hence the existential Theorem 1.2.
The block count is `8δ + 1` instead of `8δ`, and the literal `8δ` fails on the one-vertex graph. Case (II) of the
proof has three errors, all repaired. Observation 2.6 is false as stated, but only for shortcuts with useless tree edges far from the part; the evident
condition that every block meets its part fixes it. Observation 2.7 needs one more
halving round. The construction in the proof of the lower bound (Lemma 3.2) does not have the claimed diameter.

## Mistakes in the paper

### ⚠️ Theorem 3.1 (block count `8δ`)
The proof of Theorem 3.1 only bounds the block count by `8δ + 1`, and the literal `8δ` is false on the
one-vertex graph, where `δ(G) = 0` but the part `{v}` always has one block
(`theorem_3_1_literal_false_singleton`).

**Impact.** An off-by-one: we prove the theorem with `8δ + 1` blocks (`theorem_3_1`), so Theorem 1.2 gets
dilation `(8δ + 1)(2D + 1)` instead of `8δ(2D + 1)`. Whether `8δ` holds for non-degenerate graphs is left open.

**Details.** In case (I), the blocks of `P_i` are counted by their topmost vertices. The proof counts only
overcongested edges `(e, P_i) ∈ B`, but the topmost vertex of a block can also be the root, which has no
parent edge and is never overcongested. On the one-vertex graph this makes `8δ = 0` blocks impossible.

### ⚠️ Observation 2.6 (blocks far from the part)
Observation 2.6 is false as stated: on the path `0 – 1 – 2` rooted at 0, with part `{2}` and `H = {01}`, there
are two blocks, but 2 is disconnected from 0, so the dilation is infinite (`observation_2_6_counterexample`).

**Impact.** Fixed by the evident condition that every block meets its part, which the shortcuts built in
Theorem 3.1 satisfy (`observation_2_6`, `blocksMeetPart_shortcut`).

**Details.** Definition 2.3 lets a tree-restricted `H_i` contain tree edges far from `P_i`. A block of such
an `H_i` need not meet `P_i`, so `G[P_i] + H_i` can be disconnected.

**Repair.** Require every block to contain a vertex of its part. We add this to Definitions 2.4/2.5. The
shortcuts built in Theorem 3.1 ("all ancestor edges of `P_i`") satisfy it. (`observation_2_6`,
`blocksMeetPart_shortcut`)

### ⚠️ Lemma 3.2 (lower bound: diameter of the construction)
The graph constructed in the proof of Lemma 3.2 violates the diameter bound: for `δ' = 5`, `D' = 12` (so
`δ = 3`, `k = 2`, `D = 6`, 174 vertices), the vertices `v_{3,3}` and `v_{10,11}` are at distance exactly 15
(`LowerBound.paperGraph_dist_eq`, `LowerBound.paperGraph_not_diam_le`).

**Impact.** The proof fails, so Lemma 3.2 is unestablished; the statement is plausibly true with different
constants. The upper bounds are unaffected.

**Details.** The proof shows that every vertex is within `1.5D + 1` of the middle of the top path. That bounds
the radius, but the proof concludes "diameter ≤ 1.5D + 1 ≤ D'"; the diameter can be nearly twice as large.
Numerical experiments (not formal) suggest that `k = ⌊(D' − 2)/(3δ)⌋` repairs the construction. Also,
Figure 3.2 uses `δ' = 3`, outside the lemma's range `δ' ≥ 5`.

### ⚠️ Observation 2.7 (number of halving rounds)
The proof's `log₂ k` halving rounds are not enough to cover `k` parts, which need `⌊log₂ k⌋ + 1` rounds (for
`k = 1` part one round is needed but `log₂ 1 = 0`), so the stated congestion `c log₂ n` is not established.

**Impact.** Harmless asymptotically: we prove congestion `c(⌊log₂ n⌋ + 1)` (`observation_2_7`).

## Proof gaps (statements true)

### 🛠️ Theorem 3.1, case (II) (edges of `B` never present in `B_{P'}`)
When the lower endpoint `v_e` of an overcongested edge lies in a part `P_i`, the pair `(e, P_i)` is never
present in `B_{P'}`, so the bound `E|E_{P'}| ≥ 3k/(16D)` is unjustified.

**Impact.** Repaired with a sharper presence probability (`exists_blocker`, `caseII_false`, `final_arith`).

**Details.** The representative is then `v_e`, so the path "from `v_e` to `r` excluding `r`" is empty.
Moreover, the edge-node `e` exists only if `P_i ∉ P'`, so the pair `(e, P_i)` is never present.

**Repair.** Each edge-node loses at most one such pair, since parts are disjoint. We compensate with a sharper
presence probability `(1 − p)^{D−1} ≥ (3D+1)/(4D)` instead of `3/4`, together with `δ ≥ 1/2` for any graph
with an edge. The arithmetic then closes. (`exists_blocker`, `caseII_false`, `final_arith`)

### 🛠️ Theorem 3.1, case (II) (representatives must be topmost)
"Some representative `r ∈ P_i` reachable from `v_e` via `T \ O`" does not give the claimed independence from
the event `P_i ∈ P'`, which needs the path from `v_e` to `r` to avoid `P_i`.

**Impact.** Repaired by choosing `r` as the first vertex of `P_i` on the way down (`exists_rep`).

### 🛠️ Theorem 3.1, case (II) (strictness and the edge-node count)
"At least half of the parts have degree at least `8δ`" yields only `≥` where the proof needs `<`, and the
claim that each edge-node is included with probability `1 − 1/(4D)` is wrong.

**Impact.** Repaired; the arithmetic only needs the bound `|O| ≤ k/c` on the number of edge-nodes.

**Details.** An edge-node whose `v_e` lies in no part is always present. This is harmless for the arithmetic,
which only uses the bound `|O| ≤ k/c`, but it means the strict inequality must come from the part-nodes. The
connectivity and disjointness of the branch sets of `B_{P'}` are only asserted in the paper; we prove them.

**Repair.** Take the exact negation of case (I): more than half of the parts have degree strictly greater than
`8δ`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Purely graph-theoretic. No distributed model is formalized, because the CONGEST algorithms are cited
from other work.
- `G` is a finite simple graph. "Diameter `D`" means connected with all distances `≤ D`. Rooted spanning trees are
  given by parent pointers with depths.
- Parts are pairwise disjoint vertex sets, each inducing a connected subgraph. A shortcut is a family of edge sets
  of `G`.
  - Congestion bounds per-edge multiplicity.
  - Dilation bounds the diameter of `G[P_i] + H_i`.
  - Blocks are the components of `(P_i ∪ V(H_i), H_i)`.
- Minors are branch-set models. `MinorDensityLE δ` means every minor has `|E| ≤ δ|V|`. `minorDensity` is the
  (attained) supremum. Theorem 3.1 holds for every `δ ≥ δ(G)`.
- Overcongested edges: instead of running the greedy, we take a set `O` with the greedy's fixed-point property
  (`exists_stable`).
- The probabilistic method (independent Bernoulli(`1/(4D)`) parts) is an explicit weighted sum over subsets, without
  measure theory: `bernWeight` and its lemmas come from the shared finite probability library
  `Cslib/Probability/Finite/Bernoulli.lean`.

**Main results in Lean** (namespace `LowCongestionShortcuts`).

| Paper | Lean | File |
|---|---|---|
| Observation 2.6 (with the block hypothesis); counterexample | `observation_2_6`, `observation_2_6_counterexample` | `Observations.lean` |
| Observation 2.7 | `observation_2_7` | `Observations.lean` |
| **Theorem 3.1** (`8δ + 1` blocks, congestion `8δD`) | `theorem_3_1`, `theorem_3_1_minorDensity` | `Theorems.lean` |
| Theorem 3.1 with `8δ` blocks is false | `theorem_3_1_literal_false_singleton` | `Literal.lean` |
| **Theorem 1.2** (congestion `8δD(⌊log₂ n⌋+1)`, dilation `(8δ+1)(2D+1)`) | `theorem_1_2`, `theorem_1_2_of_minorDensityLE` | `Theorems.lean` |
| Lemma 3.2: construction has diameter > `D'` | `LowerBound.paperGraph_not_diam_le` | `LowerBoundGraph.lean` |

**Not formalized.** Lemma 3.2 itself (it needs planarity and Euler's formula); Lemmas 1.1, 1.3, 2.8, 3.3, Theorem
1.5, Corollaries 1.4, 1.6, 1.7, 3.4 (cited results, distributed algorithms, genus/treewidth bounds).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The graph notions (rooted trees, BFS trees, minors and minor density, shortcuts) come from CSLib,
`Cslib/Foundations/Combinatorics/SimpleGraph/`.
