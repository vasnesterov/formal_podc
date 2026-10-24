# Collaborative Tree Exploration with Breadth-First Depth-Next — PODC 2023

Romain Cosson, Laurent Massoulié, Laurent Viennot. *Brief Announcement: Efficient Collaborative Tree
Exploration with Breadth-First Depth-Next.* PODC 2023. DOI
[10.1145/3583668.3594568](https://doi.org/10.1145/3583668.3594568). Proofs are only in the full version,
arXiv [2301.13307](https://arxiv.org/abs/2301.13307) v1 (*Breadth-First Depth-Next: Optimal Collaborative
Exploration of Trees with Low Diameter*). We follow the numbering of the brief announcement (BA) and give
the full-version numbering in brackets.

**Verdict: ⚠️ Correct with fixes.** The headline Theorem 2.1 is true: BFDN explores any tree in
`2n/k + D²(min{log Δ, log k} + 2)` rounds. Theorem 3.1 (the balls-in-urns game) and Proposition 4.2
(break-downs) are true too. Corollary 3.2 is false as literally worded ("number of calls to `Reanchor`"),
because robots at the root call `Reanchor` in every round and get the root as anchor; its evident content
(anchor assignments at depths `d ≥ 1`) is what the analysis uses, and we prove it per depth with `+2`
instead of `+1` (Lemma 2 of the full version). The loop condition of Algorithm 1 in the BA is a
pseudo-code slip (the prose and the full version are right). Claim 1 inside the full-version proof of
Theorem 1 is false (`D + 1` must be `2D`), which is harmless. The key Lemma 2 [full version], obtained by
reduction to the urn game, is only sketched, and the sketch does not match the game. We prove it by a
different, direct argument.

## Mistakes in the paper

* **Corollary 3.2 is false as worded (imprecise statement).** It says that in an execution of BFDN,
  `Reanchor` is called at most `D(k·min{log k, log Δ} + k)` times. But every robot standing at the root calls `Reanchor` in every
  round (lines 6–7 of Algorithm 1). Take one robot on a star with two leaves (`D = 1`). The bound is `1`,
  yet `Reanchor` is called in rounds 0 and 2, and the exploration is still unfinished at round 2. On a
  star with many leaves and any `k`, the calls grow like `n`, while the bound does not depend on `n`.
  All these calls return the root itself (depth 0), which is not a move of any urn game; read as
  "assignments of anchors at depth `d ≥ 1`", the corollary is not refuted (random simulations on small
  trees stay far below the bound), but the paper proves only the weaker per-depth constant below.
  The statement the analysis needs is Lemma 2 [full version]: for each depth `d ≥ 1`, at most
  `k(min{log k, log Δ} + 2)` anchor assignments go to nodes of depth `d`. We prove that lemma. Note the
  `+2`: it is not `+1`, as the per-depth reading of Cor. 3.2 would suggest. (`corollary_3_2_false`;
  `lemma_2`)
* **Algorithm 1 (BA) does not explore the tree as written (pseudo-code slip).** Line 14 is `while not all robots are at the root`.
  With one robot on the star with two leaves, every execution has the robot on a leaf after round 0 and
  back at the root after round 1. The loop then stops with a leaf never visited. The prose of the BA
  and the full version use the right condition (`while some robot changes position`), and that is the
  one we formalize: we run until the tree is explored and all robots are back. This is a slip in the
  pseudo-code. (`algorithm_1_loop_stops_early`)
* **Claim 1 [full version, proof of Thm 1] is false.** It says at most `D + 1` rounds contain a robot
  that does not move. The proof misses robots that are still on a breadth-first trip when the last
  dangling edge is taken. Such a robot first walks down to its (now closed) anchor and only then
  returns, while the others idle at the root for up to `2D − 1` rounds. Lean counterexample: `k = 3`
  robots on a 7-node tree of depth `D = 4` (a path `1–3–5–6` and a path `2–4` below the root), with
  lowest-index tie-breaking. In round 3 robot 2 is sent to node 5 at the moment robot 0 takes the last
  dangling edge there. The run ends after 9 rounds, and 6 of them contain an idle robot (> `D+1 = 5`).
  The correct bound is `2D`, which still fits in the slack of Theorem 2.1, so Theorem 2.1 is unaffected.
  (`claim_1_false`; corrected: `card_idleRounds_le`)
* **Lemma 2 [full version] (the per-depth bound behind Cor. 3.2): proof gap, statement true.** The
  reduction to the urn game in Section 3.1 is a sketch, and the BFDN process is not literally a play of
  the game:
  * the load BFDN balances (`#{j : v_j = v}`) leaves out the robot exploring `T(v)`, which is "formally
    re-anchored" only in the analysis;
  * a node stops being a candidate as soon as its dangling edges are taken, without any robot returning
    from it, so the player's argmin ranges over a subset of `U_t`;
  * several urns can disappear between two re-assignments;
  * the final "`+k` for the last `d` rounds" is off by one round, because robots leaving a node in the
    very round it closes can be re-assigned once more.

  We prove the lemma directly. Open depth-`d` nodes are urns, and each holds its discoverer robot
  (Claim 5, proved as an invariant). Loads stay balanced. A robot anchored at an open node cannot come
  back. Removing an urn when `u` urns are alive frees at most `min(Δ, ⌈k/u⌉)` robots. These facts give
  at most `S_k(Δ) = Σ_{u=1}^{k} min(Δ, ⌈k/u⌉) ≤ k(min{log Δ, log k} + 2)` assignments. The `log Δ`
  part needs a careful window argument in the synchronous model. (`lemma_2`, `lemma_2_urnSum`,
  `alloc_bound`, `sync_window`)
* **Theorem 3.1 (game): proof gap, statement true.** Lemma 4 [full version] on the adversary's best
  response is only sketched, and so is the final sum estimate. We prove the bound by direct accounting:
  every play lasts at most `S_k(Δ) − k + 1` steps. (`game_ends`)
* Typos and small slips: the strategy is written `argmin_{i∈[k]\{a_1,…,a_t}}` in the full version but
  `a_0,…,a_t` in the BA (`a_0` must be included). "If `Δ ≥ k` the game stops when all urns have been
  chosen" holds only for `Δ > k`. Claim 3 [full version] counts "explored dangling edges" per trip; the
  accounting only needs the global inequality moves ≤ 2(n−1) + 2·Σ(anchor depths), and that is what we
  prove.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The tree is a CSLib `G.RootedTree` `T` (root, parent pointers, depths) of a finite graph `G`. Robots
  walk along tree edges. An edge is identified with its lower endpoint, so "all edges traversed" is the
  same as "all nodes visited". `n = |V|`, `D = maxDepth T`, `Δ = G.maxDegree`. Only
  `#children(w) + 1 ≤ Δ` for non-root `w` is used, so the theorems apply to any `G` containing the tree
  (when `G` is a tree, `T` has exactly its edges). `log` is the natural logarithm.
* Synchronous rounds, `k ≥ 1` robots starting at the root, complete communication. Within a round the
  robots decide in index order (`Reanchor`, then `BF` or `DN`, as in Algorithm 1) and then all move at
  once. A configuration holds positions, anchors, the visited set and a flag "stack nonempty" (the stack
  is the path from the position to the anchor). The round is a relation (`Round`), so **all results hold
  for every tie-breaking** (which minimum-load anchor, which free dangling edge). Algorithm 1's decisions
  only read explored information, but the model does not enforce this by an information-hiding
  interface.
* Runtime: the first time `t` at which the tree is explored and all robots are at the root (`Terminal`).
  This is exactly when the full version's loop `while some robot changes position` stops.
* Break-downs (Prop. 4.2): round `t` is played with an arbitrary set `act t` of robots allowed to move.
  Blocked robots neither decide nor move, as in the full version. `A(M)` is
  `(Σ'_t |act t|)/k ∈ ℝ≥0∞`. The model of Theorem 2.1 is `act t = univ`.
* The urn game: arbitrary adversary moves, the player's balancing strategy with arbitrary tie-breaking,
  and plays of any finite length that have not stopped.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 [Thm 1] | `theorem_2_1` | `Main.lean` |
| Lemma 2 [full version] (per-depth assignments, `k(min{log k, log Δ}+2)`) | `lemma_2`, `lemma_2_urnSum` | `Main.lean` |
| — its abstract core (balanced allocation with removals) | `alloc_bound` | `Allocation.lean` |
| — `log k` part for any break-down pattern / `log Δ` window (synchronous) | `sum_assignCount_le_k` / `sync_window` | `Phase.lean` / `Sync.lean` |
| Theorem 3.1 [Thm 3] (urn game) | `game_ends` | `Game.lean` |
| `S_k(Δ) ≤ k(min{log Δ, log k}+2)` | `urnSum_le`, `urnSum_sub_le` | `UrnSum.lean` |
| Corollary 3.2 — false as worded | `corollary_3_2_false` | `Counterexamples.lean` |
| Algorithm 1 (BA) loop condition — wrong | `algorithm_1_loop_stops_early` | `Counterexamples.lean` |
| Claim 1 [full version] — false; corrected `2D` | `claim_1_false`; `card_idleRounds_le` | `Counterexamples.lean`; `Idle.lean` |
| Claims 2–3 (moves accounting) | `sum_moved_le`, `card_vis_succ` | `Accounting.lean` |
| Claims 4–5 (open nodes covered by a discoverer) and other invariants | `Inv`, `IsExec.inv` | `Invariants.lean` |
| Proposition 4.2 [Prop 6] (break-downs) | `proposition_4_2` | `Breakdowns.lean` |
| Non-vacuity: executions exist | `exists_exec`, `exists_syncExec` | `Exists.lean` |

**Not formalized.** Proposition 4.1 (restricted memory, central planner), Proposition 4.3 (non-tree
graphs with known distances), Proposition 4.4 / Theorem 8 (recursive BFDN_ℓ), and the comparisons of
Figure 1.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: BFDN executions exist for every tree, `k` and break-down pattern
(`exists_exec`), and the Claim 1 counterexample is an explicit synchronous execution checked by
`decide`. The tree structure comes from CSLib (`Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree`).
