# Differences between the formalization and the paper

Paper: Cosson, Massoulié, Viennot, *Brief Announcement: Efficient Collaborative Tree Exploration with
Breadth-First Depth-Next*, PODC 2023 (BA), with proofs from the full version arXiv:2301.13307v1 (FV).

## Errors and gaps in the paper

1. **Corollary 3.2 (BA) is false as stated.** "The number of calls to procedure Reanchor is at most
   `D(k min{log k, log Δ} + k)`". Robots at the root call `Reanchor` in every round. One robot on the
   star with two leaves calls it in rounds 0 and 2 (before termination), but the bound is `1`
   (`corollary_3_2_false`). On stars with many leaves the number of calls is `Θ(n)` for every `k`. What
   the analysis uses is FV Lemma 2 (per depth `d ≥ 1`, at most `k(min{log k, log Δ} + 2)` assignments to
   depth-`d` anchors). We prove it (`lemma_2`). The per-depth reading with `+1` (`D·k(m+1)` in total)
   is neither proved by the paper nor by us. All calls in the counterexamples return the root (depth 0), which is
   not a move of any urn game, so the corollary is best read as an imprecise wording of the per-depth bound
   (hence ⚠️, not ❌); in that reading it is not refuted, only the `+1` constant is unproved.
2. **Algorithm 1 (BA), line 14** `while not all robots are at the root` makes the robots stop as soon as
   they are all back at the root, possibly with unexplored edges (`algorithm_1_loop_stops_early`, one
   robot, star with two leaves). FV Algorithm 1 uses `while some robot changes position`. Our runtime
   is the first time at which the configuration is terminal (tree explored, all robots at the root). This
   is when the FV loop stops: a round without movement happens iff the configuration is terminal.
3. **Claim 1 (FV)** "at most `D + 1` rounds in which some robot does not move" is false
   (`claim_1_false`: `D = 4`, 6 such rounds). We prove `2D` (`card_idleRounds_le`), which is enough for
   Theorem 2.1 because `D(min{…} + 2) ≥ 2D`.
4. **FV Lemma 2, proof.** The reduction to the urn game (FV Section 3.1) is a sketch whose details do not
   fit the game:
   * BFDN's loads do not count the discoverer of a node;
   * nodes leave the candidate set without any robot returning;
   * several nodes can close between two re-assignments;
   * the final window of `d` rounds is off by one round.

   We prove the statement by a direct argument (`alloc_bound` + `Phase.lean` + `Sync.lean`), with the
   intermediate bound `S_k(Δ) = Σ_{u=1}^{k} min(Δ, ⌈k/u⌉)`. In particular, the `log Δ` part uses the
   synchronous model (closure of all depth-`d` candidates within `d` rounds once each has `Δ − 1` robots).
   For break-downs only the `log k` part is proved, as in the paper.
5. **FV Theorem 3 / Lemma 4, proof.** The best-response analysis is sketched, and the final summation
   `Σ⌈k/h⌉ ≤ Σ k/h + 1` is imprecise. We prove `T ≤ S_k(Δ) − k + 1` for every play directly (balanced
   loads, each removal at size `u` frees at most `min(Δ, ⌈k/u⌉)` balls) and then
   `S_k(Δ) + 1 ≤ k(min{log Δ, log k} + 2)` (`urnSum_add_one_le`).
6. Typos: the player's strategy in FV Section 3 excludes `{a_1,…,a_t}` (should be `{a_0,…,a_t}`, as in
   the BA). "If `Δ ≥ k` the game stops when all urns have been chosen" holds only for `Δ > k`. The BA
   says `T_online` "equals the underlying tree" when there are no dangling edges; this is correct but
   needs the visited set to be closed under parents (`vis_eq_univ_of_no_open`).

## Modelling choices

* **Tree.** A CSLib `G.RootedTree T` with `[Fintype V] [DecidableEq V]`. The paper's tree is `T`, and
  `n = Fintype.card V`, `D = maxDepth T = max depth`. For `Δ` we use `G.maxDegree`. The proofs only use
  `#children(w) + 1 ≤ Δ` for non-root `w` (`nChildren_add_one_le`). We do not assume `G.IsTree`, so the
  theorems are slightly more general: if `G` has extra edges, BFDN explores the spanning tree `T`.
* **Edges** are identified with their lower endpoints. "Edge traversed" is the same as "lower endpoint
  visited", so `vis = univ` means all edges are explored. Dangling edges are the unvisited children of
  visited nodes. Edge identifiers and port numbers are not modelled.
* **Algorithm state.** The stack `S_i` is represented by a flag `bf i` (stack nonempty). Its content is
  the path from the current position to the anchor, so `BF` moves to `towards pos anchor`.
* **Ties.** `Round` is a relation that allows every resolution of the `argmin` in `Reanchor` and every
  choice of free dangling edge in `DN`. All positive results quantify over all resolutions.
* **Load in `Reanchor`.** `#{j : v_j = v}` is computed with the anchors as updated so far in the round
  (robots `j < i` already re-anchored), and counts all `j`, including `i` (with its old anchor), as in
  line 28. For the relevant nodes (open, non-root) `i`'s old anchor never matters.
* **Communication.** Complete communication, implicit: decisions read the whole configuration. BFDN only
  reads the visited set, the children of visited nodes, positions and anchors, but the model has no
  separate "knowledge" layer that would enforce online-ness.
* **Runtime.** `theorem_2_1` gives `∃ t ≤ 2n/k + D²(min{log Δ, log k}+2)` with `e t` terminal. Terminal
  configurations are stable (`IsExec.terminal_succ`). We require `k ≥ 1`, which the paper leaves
  implicit (with `k = 0` there is no exploration).
* **Lemma 2** is stated for every prefix of an execution: `Σ_{t<t₁}` assignments at depth `d ≥ 1`.
* **Break-downs (Prop. 4.2).** `M` is given as `act : ℕ → Finset (Fin k)` (`M^i_t = 1 ⟺ i ∈ act t`).
  `A(M) = (Σ'_t |act t|)/k` is in `ℝ≥0∞`, and the hypothesis is `ofReal(2n/k + D²(log k + 2)) ≤ A(M)`.
  The conclusion is `∃ t, vis(e t) = univ` ("all edges will be visited"). Blocked robots neither
  re-anchor nor select a move, as in FV Section 4.2.
* **Urn game.** A play is an infinite record of boards and moves. `IsPlay Δ T` says that the first `T`
  moves are legal, follow the player's strategy (any minimizer, arbitrary `b_t` if `U_{t+1} = ∅`), and
  the game has not stopped before `T`. Theorem 3.1 bounds every such `T`.
* **Claims 2–3.** Instead of the per-trip identity of Claim 3 we prove the global potential inequality
  `#moves ≤ 2(|visited| − 1) + 2 Σ (depths of assigned anchors)` (`sum_moved_le`). It gives exactly the
  estimate used in the paper.
* **Claims 4–5** are replaced by the invariant `Inv.disc`: every open non-root node `w` has in its
  subtree a robot anchored strictly above `w`. With the other fields of `Inv`, this is what the proofs
  need.

## Not formalized

Proposition 4.1 (restricted memory / central planner, FV Prop. 5 and Algorithm 2), Remark 4.1, Proposition
4.3 (graphs with known distances, FV Prop. 7), Proposition 4.4 (FV Thm 8, recursive BFDN_ℓ, Appendices B–C),
and Figure 1 / Appendix A comparisons.
