# Differences between the formalization and the paper

Paper: Ghaffari, Haeupler, *Low-Congestion Shortcuts for Graphs Excluding Dense Minors*, PODC 2021
(arXiv:2008.03091v1; numbering follows it).

Summary: **the main result (Theorem 3.1, hence Theorem 1.2) is morally correct** and the proof idea works, but the
written proof has several small gaps, two stated observations need corrections, and the construction in the proof
of the lower bound (Lemma 3.2) does not have the claimed diameter. All gaps in the upper bound are fixed in the
formalization at the cost of `+1` in the block number and `+1` in the number of halving rounds.

## 1. Errors and gaps in the paper

1. **Theorem 3.1, case (I): block number is `deg_B(P_i) + 1`, not `deg_B(P_i)`.** The blocks of `P_i` correspond
   to their topmost vertices, which are either overcongested edges `e` with `(e, P_i) ∈ B`, *or the root* (the root
   has no parent edge, so it is never overcongested). Hence a part with degree `≤ 8δ` in `B` gets up to `8δ + 1`
   blocks. We prove Theorem 3.1 with `8δ + 1` blocks (`theorem_3_1`, `numBlocks_shortcut_le`). **The literal
   statement with `8δ` blocks is false in a degenerate case:** on the one-vertex graph `δ(G) = 0`, while a part
   `{v}` always has one block, so `¬ AdmitsPartialTreeShortcuts 0 0 0` (Lean: `theorem_3_1_literal_false_singleton`,
   `Literal.lean`). (Informal, unchecked remark: changing the case split to "degree `≤ 8δ − 1`" seems not to work
   with the paper's constants, since the density computation is tight.) We did not decide whether `8δ` blocks are
   achievable for non-degenerate graphs; the consequence for Theorem 1.2 is only dilation `(8δ + 1)(2D + 1)`
   instead of `8δ(2D + 1)`.
2. **Theorem 3.1, case (II): edges `(e, P_i)` with `v_e ∈ P_i` are never present in `B_{P'}`.** If the lower
   endpoint `v_e` of an overcongested edge lies in `P_i` (allowed, and then `P_i ∈ I_e`), the representative is
   `v_e` itself, the "path from `v_e` to `r` including `v_e` but excluding `r`" is ill-defined, and the edge-node
   `e` exists only if `P_i ∉ P'`, so `(e, P_i)` is never actually present. The bound `E|E_{P'}| ≥ 3k/(16D)` is
   therefore unjustified. **Fix:** there is at most one such pair per edge-node (parts are disjoint), so at most
   `|O| ≤ m/c` of the `m` edges of `B` are lost; this is compensated by a sharper bound on the presence
   probability: the tree path from `v_e` to a representative at depth `≤ D` has at most `D − 1` vertices besides the
   representative (`v_e` has depth `≥ 1`), so `Pr[potentially present] ≥ (1 − p)^{D−1} ≥ (3D+1)/(4D)` rather than
   `3/4`. Together with `δ ≥ 1/2` (any graph with an edge has a `K₂` minor) the arithmetic closes
   (`final_arith`, `exists_blocker`, `caseII_false`).
3. **Representatives must be chosen topmost.** The paper picks "some representative node `r ∈ P_i` reachable from
   `v_e` via `T \ O`" and claims independence of "potentially present" from `P_i ∈ P'`. This needs the path from
   `v_e` to `r` to avoid `P_i`, i.e. `r` must be the first vertex of `P_i` on its way down (`exists_rep`).
4. **Strictness.** The paper writes `E[|V_{P'}|] < …` using "average degree more than `4δ`"; with "at least half of
   the parts have degree at least `8δ`" one only gets `≥`. Strictness comes from the case split itself: the
   negation of case (I) gives *more than half* of the parts with degree *strictly* greater than `8δ`, hence
   `4δk < m` (we use this). The paper's estimate of the edge-node count with probability `1 − 1/(4D)` is also
   inaccurate (an edge-node whose `v_e` lies in no part is always present); we bound it by `|O|`.
5. **Connectedness/disjointness of branch sets** of `B_{P'}` are only asserted; proved here (`branch_connected`,
   `branch_disjoint`, `part_branch_disjoint`, `present_adj`). We use the "downward" description of the component of
   `v_e` in `(T \ O) \ ⋃P'` (it cannot go up since `e ∈ O`).
6. **Observation 2.6 is false as stated.** Definition 2.3 allows a `T`-restricted `H_i` to contain tree edges far
   from `P_i`; then a block need not meet `P_i` and `G[P_i] + H_i` can be disconnected (infinite dilation) while the
   block number is 2. Lean counterexample: path `0 – 1 – 2` rooted at `0`, `P = {2}`, `H = {01}`
   (`observation_2_6_counterexample`). **Fix:** we add the hypothesis `BlocksMeetPart` (every block contains a vertex
   of the part) and include it in Definitions 2.4/2.5 (`AdmitsTreeShortcuts`, `AdmitsPartialTreeShortcuts`); the
   shortcuts built in Theorem 3.1 ("all ancestor edges of `P_i`") satisfy it (`blocksMeetPart_shortcut`). With it
   we even get dilation `≤ b(2D + 1) − 1`.
7. **Observation 2.7: `log₂ k` rounds are not enough.** Halving the set of remaining parts needs `⌊log₂ k⌋ + 1`
   rounds (e.g. one round for `k = 1`, where `log₂ 1 = 0`). We prove congestion `c(⌊log₂ n⌋ + 1)`
   (`observation_2_7`), which is `≤ 2c log₂ n` for `n ≥ 2`; the asymptotic Theorem 1.2 is unaffected.
8. **Lemma 3.2: the lower-bound graph does not have diameter `≤ D'`.** The proof bounds the distance from every
   vertex to the middle of the top path by `1.5D + 1` and concludes "diameter at most `1.5D + 1 ≤ D'`" — that is
   an eccentricity (radius) bound; the diameter can be about twice as large. For `δ' = 5`, `D' = 12` (`δ = 3`,
   `k = 2`, `D = 6`, 174 vertices) the vertices `v_{3,3}` and `v_{10,11}` are at distance exactly 15 > 12
   (`LowerBound.paperGraph_dist_eq`, `paperGraph_not_diam_le`). This refutes the proof, not the (existential)
   statement; numerically (Python BFS, `δ ≤ 5`, `k ≤ 4`) choosing `k = ⌊(D' − 2)/(3δ)⌋` gives diameter `≤ D'`, so the
   lemma should hold with different constants. Also, Figure 3.2 uses `δ' = 3`, outside the lemma's range `δ' ≥ 5`.
   The rest of Lemma 3.2 (minor density via planarity + Euler, shortcut-quality lower bound) is not formalized.

## 2. Modelling choices / changed definitions

1. **Minor density as an upper bound.** Theorem 3.1 is stated for every `δ` with `G.MinorDensityLE δ` (all minors
   have `|E| ≤ δ|V|`), which is at least as strong as `δ = δ(G)`; `theorem_3_1_minorDensity` specializes to
   `δ(G) = G.minorDensity` (a `sSup`, proved to be attained). Minors are branch-set models (the paper's second,
   "equivalent" definition); we did not prove equivalence with deletion/contraction sequences.
2. **"Graph with diameter `D`".** Definitions 2.4/2.5 and Theorem 3.1 only use trees of depth `≤ D`, so they are
   stated for an arbitrary `D : ℕ`; Theorem 1.2 assumes `G.Connected` and all distances `≤ D` and uses a BFS tree.
3. **Rooted trees** are parent-pointer structures with depths (`G.RootedTree`); this is equivalent to a rooted
   spanning tree (depth = tree distance to the root). Tree edges are identified with their lower endpoints.
4. **Overcongested edges.** Instead of running the greedy, we prove existence of a set `O` with the fixed-point
   property `v ∈ O ↔ v ≠ root ∧ |I_v(O)| ≥ c` (`exists_stable`, built level by level bottom-up exactly as the
   greedy); `I_v(O)` only depends on `O` strictly below `v`, so this is the greedy's output. Only this property is
   used.
5. **Partial shortcuts.** "At least `k/2` of the parts" = a set `J` of parts with `k ≤ 2|J|`; congestion is counted
   over `J` only. Congestion is required only on edges of `G` (shortcut edge sets are subsets of `E(G)`).
6. **Dilation** is formalized as: any two vertices of `P_i ∪ V(H_i)` are connected in `G[P_i] + H_i` by a path of
   length `≤ d` (the diameter of that subgraph). Block counts are `Set.ncard` of the set of components hit by
   `P_i ∪ V(H_i)` in the graph `(V, H_i)`.
7. **Probabilistic method** replaced by explicit weighted sums over subsets (product Bernoulli weights), which is the
   same computation without measure theory.
8. Parts are indexed by an arbitrary finite type (`ι : Type` in the "admits" definitions, to quantify over all
   collections of parts).

## 3. Not formalized

Lemma 1.1 (cited, Thomason), Lemma 1.3 / 3.2 (except the diameter counterexample), Lemma 2.8 and Theorem 1.5
(distributed construction, cited from [HHW18, HIZ16a]), Corollaries 1.4, 1.6, 1.7, 3.4 and Lemma 3.3 (need genus /
treewidth theory and CONGEST algorithms), and the remark on certifying algorithms after Theorem 3.1.
