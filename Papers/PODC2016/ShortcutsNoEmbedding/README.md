# Low-Congestion Shortcuts without Embedding — PODC 2016

Bernhard Haeupler, Taisuke Izumi, Goran Zuzic. *Low-Congestion Shortcuts without Embedding.* PODC 2016.
DOI [10.1145/2933057.2933112](https://doi.org/10.1145/2933057.2933112). Formalized version: the journal
(Distributed Computing) version, arXiv:1607.07553v3; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The deterministic core of the paper is proved: Lemma 1 (for distances between vertices of the
part, or after discarding the irrelevant edges that make it false as literally stated), Lemma 2 (pipelined
convergecast/broadcast on subtrees in `D − 1 + c` rounds), Theorem 2 (leader election and part-wise aggregation in `O(b)`
supersteps of `O(D + c)` rounds), Lemma 3/Corollary 6, Lemma 5 (`CoreSlow`), the combinatorial part of Lemma 4
(`CoreFast`), and the deterministic version of Theorem 1. The proofs of Lemma 3 and of the broadcast half of Lemma 2
needed local repairs. The randomized construction and the end-to-end CONGEST round bounds, which carry the paper's main
speed claim, were not checked.

## Mistakes in the paper

### ✏️ Slips
- Lemma 1 is false as literally stated because Definitions 4 and 5 allow shortcut edges in components that miss the
  part: on the path `0 – 1 – 2` rooted at `0`, the part `P = {2}` with `H = {01}` has block parameter 1, but
  `E_G[P] ∪ H` is disconnected, so the dilation is infinite (`lemma_1_literal_false`). The bound holds for distances
  between nodes of the part, which is what the proof shows and all Theorem 2 needs, and in full once the useless
  components are dropped (`lemma_1`, `lemma_1_dilation`). Details under **Proof remarks**.
- In the proof of Lemma 4, "`Pr[X₁+…+X_t ≤ 2E[S]] ≤ exp(−δE[S])`" should read `≥`, as the next sentence uses.

### Typos
- In `CoreFast`, an edge is unusable if `|L̃_v| ≥ 4c·p` (Algorithm 2, "at least `4c·p`" in the outline), while the
  detailed description assigns the edge if `|L_v| ≤ 4c·p` and otherwise tests `> 4·p`.

## Proof gaps (statements true)

### 🔧 Lemma 3 (verification)
The proof has each leader `r` build a BFS tree of "all the nodes that believe `r` is the leader", but these nodes need not be connected to `r` within that set, so some node belongs to no BFS tree.

**Impact.** Statement true; repaired with `4b₀ + 1` supersteps (`verification_correct`, `corollary_6`).

**Details.** The proof floods the minimum ID for `b₀` supersteps; then neighbouring nodes of different trees
report failure. Example (not formalized): supergraph `r – u – w` plus a path `s – x – u`, `b₀ = 2`, IDs
`s < r < u, w, x`. `w` believes in `r` (`s` is at distance 3 from `w`), but its only neighbour `u` believes in
`s`. So `w` belongs to no BFS tree and cannot learn the outcome from one.

**Repair.** BFS only along edges whose endpoints share a leader, let unreached nodes reject, and add "unreached
neighbour" to the failure flags. We prove that a node then accepts iff the supergraph has at most `b₀` nodes,
using `4b₀ + 1` supersteps. (`verification_correct`, `corollary_6`)

### 🔧 Lemma 2 (broadcast half claimed by "symmetry")
The induction on `height(v) + p` for the convergecast does not transfer to the broadcast, because the rank of a subtree is not monotone along its root-to-leaf paths.

**Impact.** We prove the `O(D + c)` bound by time reversal (`IsConvergecastSchedule.reverse`,
`exists_schedules`).

**Details.** The induction uses that a higher-priority subtree containing a child edge of `v` also contains `v`'s
parent edge. This holds upwards (convergecast) but not downwards. Example (not formalized): `c − 1`
higher-priority subtrees share `i`'s first edge, then branch off. Then `i`'s message reaches depth 2 only at round
`c + 1`, while the per-edge invariant would give 3.

**Repair.** The reversed greedy convergecast schedule is a valid broadcast schedule of the same length,
`D − 1 + c` rounds.
(`IsConvergecastSchedule.reverse`, `exists_schedules`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Graph-theoretic part as in CSLib. `G` is a finite simple graph and `T` a rooted spanning tree (parent pointers,
  depth `≤ D`). Parts are disjoint and connected. A shortcut is `ι → Finset (Sym2 V)`, `T`-restricted
  (Definition 4). Block parameter = Definition 5 (`blockParam`: components of `(V, H_i)` containing a node of
  `P_i`). Congestion = CSLib's `CongestionLE`, which counts only the `H_i`. This is weaker than the paper's
  Definition 2 (`PartCongestionLE`, which also counts `E_G[P_i]`), so our hypotheses are weaker.
- Round complexity in synchronous CONGEST is modelled at the level of **message schedules**: each tree edge carries
  one `O(log n)`-bit message per round, causality between messages, no message contents. Lemma 2's greedy
  algorithm is an explicit round-by-round process. A convergecast (broadcast) schedule is a send round for every
  (subtree, edge) pair with the causal order and the one-message-per-edge-per-round constraint.
- Theorem 2 and Lemma 3 are verified at the **supergraph level**. Each part's blocks form a connected graph with
  `blockParam ≤ b` nodes. Algorithms are synchronous supersteps (min-flooding, BFS labelling, tree convergecast of a
  commutative monoid). One superstep = one round over `G[P_i]` edges between blocks + an intra-block convergecast
  and broadcast. The latter is Lemma 2 applied to the family of all blocks of all parts, which has congestion
  `≤ c` (`theorem_2_intraBlock`), so a superstep costs `≤ 2(D − 1 + c) + 1` rounds. The message-level
  implementation of a superstep is not composed formally. Hence the round bounds of Theorem 2, Lemma 3 and
  Theorem 1 are *superstep counts × per-superstep cost*, not end-to-end theorems about a CONGEST execution;
  `aggregationRounds_le` is only the arithmetic `(4(b−1)+1)·(2(D−1+c)+1) ≤ (4b+1)(2(D+c)+1)`. For Lemma 3 the
  BFS and convergecast steps are given by their output specifications (`Reached`, `Accept`).
- `CoreSlow` is modelled by its output: the unusable set `U` is the unique set with
  `v ∈ U ⟺ v ≠ root ∧ |L_v| > 2c`, `L_v` being the parts seen by `v`'s parent edge in `T \ U`. The bottom-up
  construction proves existence; uniqueness is proved separately. The randomness of `CoreFast` is not modelled:
  Lemma 4 is proved conditionally on the two events that the paper's Chernoff bounds give w.h.p.
- Deterministic randomness-free model throughout; no failures.

**Main results in Lean** (namespace `ShortcutsNoEmbedding`; Lemma 2 in `SimpleGraph.RootedTree.SubtreeFamily`).

| Paper | Lean | File |
|---|---|---|
| Definition 5 (block parameter) | `blockParam` | `Defs.lean` |
| Definition 2 (congestion) ⇒ CSLib congestion | `PartCongestionLE.congestionLE` | `Defs.lean` |
| Lemma 1 (as proved: between part vertices) | `lemma_1`, `lemma_1_dist` | `Lemma1.lean` |
| Lemma 1 (full dilation, blocks meet the part) | `lemma_1_dilation` | `Lemma1.lean` |
| Lemma 1 literal: **false** | `lemma_1_literal_false`, `lemma_1_literal_false_edgeSet` | `Lemma1.lean` |
| Lemma 2, main induction (`h(v) + rank`) | `SubtreeFamily.sent_of_le` | `Podc/.../Congest/SubtreeRouting.lean` |
| Lemma 2, paper's priority is compatible | `SubtreeFamily.compatible_topDepth` | same |
| Lemma 2 (convergecast, greedy, `D − 1 + c` rounds) | `SubtreeFamily.greedy_isConvergecastSchedule` | same |
| Lemma 2 (convergecast + broadcast) | `SubtreeFamily.exists_schedules` | same |
| Theorem 2, intra-block step (Lemma 2 on all blocks) | `theorem_2_intraBlock`, `blockFamily_congestionLE` | `Theorem2.lean` |
| Theorem 2, supergraph connected with `b` nodes | `superGraph_connected`, `card_blocks` | `Theorem2.lean` |
| Theorem 2.1 (leader election) | `theorem_2_leader` | `Theorem2.lean` |
| Theorem 2.2/2.3 (convergecast/broadcast to leader) | `theorem_2_convergecast` | `Theorem2.lean` |
| Theorem 2 round count `O(b(D + c))` (superstep arithmetic only) | `aggregationRounds_le` | `Theorem2.lean` |
| supergraph primitives (flooding, BFS, tree convergecast) | `floodMin_eq_inf`, `floodDist_spec`, `treeAgg_root` | `Supersteps.lean` |
| Lemma 3 (repaired procedure) | `verification_correct` | `Verification.lean` |
| Corollary 6 | `corollary_6` | `Verification.lean` |
| Lemma 5 (`CoreSlow`) | `lemma_5`, `card_coreSlow_list_le` | `CoreSlow.lean` |
| Lemma 5/4 core (blame argument) | `many_good_of_cut`, `many_good_of_cut_on` | `CoreSlow.lean` |
| Lemma 4 (`CoreFast`), deterministic part | `lemma_4_combinatorial` | `CoreSlow.lean` |
| Theorem 1, deterministic (`FindShortcut` with `CoreSlow`) | `theorem_1_deterministic` | `Theorem1.lean` |
| one iteration halves the remaining parts | `card_remaining_succ` | `Theorem1.lean` |

**Proof remarks.**

*Lemma 1.* Definition 4 lets a `T`-restricted `H_i` contain any tree edges. Definition 5 counts only the
components of `(V, H_i)` that contain a node of `P_i`. Dilation (Definition 2) is the diameter of
`E_G[P_i] ∪ H_i`. In the example the depth is 2, so the bound would be `≤ 1·(2·2+1)`. The failure does not
depend on whether the vertex set of "`E_G[P_i] ∪ H_i`" includes `P_i`: on the path `0 – … – 4`, `P = {4}`,
`H = {01, 23}` has one block component, yet the edge set `{01, 23}` itself is disconnected
(`lemma_1_literal_false_edgeSet`). The paper even remarks (after Definition 5) that components of `(V, H_i)`
missing `P_i` need not be counted, so such `H_i` are explicitly allowed. The paper's proof ("contract every block component … remove all other nodes") bounds the distance
between nodes of `P_i`. We prove exactly that: any two nodes of `P_i` are at distance `≤ b(2D+1) − 1` in
`G[P_i] + H_i` (`lemma_1`). We also prove the full dilation bound when every component of `H_i` meets `P_i`
(dropping the other components changes neither the block parameter nor the routing) (`lemma_1_dilation`).

*`FindShortcut`.* "After `O(log N)` iterations" is exactly `⌊log₂ N⌋ + 1` (one iteration for `N = 1`).

**Not formalized.** The probabilistic analysis of `CoreFast` (Chernoff bounds, shared randomness), hence the
randomized Theorem 1 and Corollaries 4–5. The genus-`g` shortcut existence ([GH16], cited) and Boruvka's MST. The
message-level composition of supersteps (no end-to-end CONGEST round theorem for Theorem 2, Lemma 3, Theorem 1).
Whether the paper's greedy broadcast itself meets `D − 1 + c`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `empty_shortcut_canonical` (the hypotheses of Theorem 1 always hold for some `c, b`), and
`lemma_1_literal_false` exhibits the hypotheses of Lemma 1. Model from CSLib: `RootedTree`, `BFSTree`, `Shortcut`,
`ShortcutDilation`. Infrastructure staged in `Podc/`: `Podc/Computability/Distributed/Congest/SubtreeRouting.lean`
(Lemma 2, CSLib candidate) and `Podc/Foundations/Combinatorics/SimpleGraph/TreeCut.lean` (cutting a rooted tree at
congested edges; CSLib candidate). Its first half duplicates the older `Papers/PODC2021/LowCongestionShortcuts/Overcongested.lean`
(`Below`, `parts`, `exists_stable`, `shortcut`, …, with threshold `c ≤ |I_v|` instead of `θ < |I_v|`); follow-up: port
that paper to import `TreeCut` before upstreaming. `Supersteps.lean` (flooding, BFS labelling, tree convergecast) is a further CSLib candidate.
