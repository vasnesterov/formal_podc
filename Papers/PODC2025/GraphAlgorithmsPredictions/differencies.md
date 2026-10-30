# Differences between the formalization and the paper

Paper: Boyar, Ellen, Larsen, *Brief Announcement: Distributed Graph Algorithms with Predictions*, PODC 2025.
Proof of Theorem 4.1 from the full version, arXiv:2501.05267 (Section 6, Theorem 3, Lemmas 1, 4, 5).

## Statements

1. **Theorem 4.1** (`theorem_4_1`). Stated for every `T`-local algorithm `f` (CSLib `IsLocal T`) that computes an
   MIS of every `n`-node line with arbitrary distinct natural identifiers; conclusion `(n − 5)/2 ≤ T` over `ℝ`.
   This is *stronger* than the paper's hypothesis "component-size bounded": the algorithm may know `n` and may
   be tailored to `n`; only independence of the round count from the identifier domain is used (as the full
   version states: "if its round complexity does not depend on the domain from which the node identifiers are
   chosen"). Bounded form (`lemma_4_bounded`, `mis_lowerBound_bounded`): identifiers `< D(n, T)` suffice, which
   covers the full version's alternative hypothesis "`d` is a sufficiently large function of `n`". No rule of
   `verdicts.md` applies (statement true as written).
2. **Lemma 4 (full version)** (`lemma_4`). Proved for any finite colour type `β`, not only 3 colours; bound
   `(n − 3)/2 ≤ T`. Same proof.
3. **Lemma 5 (full version)**. Split into the reduction (`misToColour_isLocal`: `T + 1` rounds;
   `misToColour_solves`: a proper 3-colouring) and `theorem_4_1`. The reduction is the paper's (MIS ↦ 0, non-MIS
   with MIS left neighbour ↦ 1, other ↦ 2). In the locality setting a node also checks that its labelled left
   neighbour is a graph neighbour; on lines this is always the case.
4. **Sharper bound** (`mis_lowerBound_sharp`, not in the paper): `(n − 4)/2 ≤ T`, by Ramsey directly on the MIS
   outputs (three consecutive equal outputs). Not an error of the paper (its bound is weaker but true).
5. **Pruning algorithm, rounds.** The paper's 3-round algorithm: round 1 exchange predictions, round 2 `I`
   outputs 1 and notifies, round 3 neighbours of `I` output 0. In our model a node knows after round 1 whether it
   is in `I` (its state changes to "output 1" then), neighbours of `I` output 0 in round 2, and round 3 is idle.
   We prove the paper's statement for 3 rounds (`pruneAlg_status`, consistency `predAlg_consistent`); the round
   count `η + 3` of §5 is proved as stated (`predAlg_terminates`), although `η + 2` would also hold in our model.
   The difference is the round convention (in the paper's pseudocode a node decides on messages of earlier rounds,
   so the round-3 notification of `N(I)` is needed before greedy can start); not an error of the paper.
6. **Greedy MIS round bound** (`greedy_round_complexity`, `greedy_decided`). The BA claims "at most `n` rounds on a
   graph with `n` nodes"; we prove the stronger per-node bound of Lemma 1 of the full version (the size of the
   node's component in the subgraph induced by the initially active nodes) from any start configuration
   satisfying the invariants (independent outputs 1, every output 0 dominated, no active node next to an output
   1). The paper's proof sketch counts per component of the remaining graph; components split over time, so we
   count the active nodes of a fixed initial component (≥ 2 of them terminate in every 2 rounds while ≥ 2 are
   active, and a single remaining node terminates in the next odd round). Routine; no repair needed.
7. **Error measure** (`eta`). The maximum number of nodes of an error component, error components = connected
   components of the subgraph induced by the nodes left active by the (fixed) basic pruning algorithm, exactly as
   in §3. Components are computed in `restrict G R` (same vertex type, vertices outside `R` isolated).
8. **`η`-degrading.** The paper's notion "terminates within `f(η) + c(n) + O(1)` rounds" is instantiated with
   the concrete bound `η + 3` (`predAlg_terminates`, `predAlg_correct`). Asymptotic notions (consistent, robust,
   smooth) are not formalized as definitions.
9. **Agreement with predictions** (`pruneSet_agrees`): the nodes of `I` have prediction 1 and their neighbours
   prediction 0, so the pruning output agrees with the prediction, as claimed.
10. **Variant initialization** (`pruneSet'`): we prove that its output is an extendable partial solution and that
    `I ⊆ I'` ("a possibly larger extendable partial solution"); it is not used by the main algorithm.

## Model

11. **Lower-bound model.** Nodes are named by identifiers (`ℕ`); a line is `(pathGraph n).map id`; labels give the
    left and right neighbour identifiers (orientation known, as in the full version). An algorithm is an
    extensional `T`-local function (standard: in `T` rounds a node can learn exactly its radius-`T` view, and a
    deterministic algorithm's output is a function of it). Algorithms that do not use the orientation or the
    neighbour identifiers are special cases.
12. **Algorithm model.** CSLib's locally-iterative (SET-LOCAL) model: a node sees the *set* of its neighbours'
    states. Since states carry identifiers, this loses nothing for the algorithms here. "Terminate" = the status
    leaves `active` and never changes again (`status_le_of_ne`). Graphs are finite; identifiers are a linear
    order on the node type (`LinearOrder V`), arbitrary (no bound `d` needed).
13. **MIS** (`IsMIS`): independent and dominating; equivalent to Mathlib's `Maximal G.IsIndepSet`
    (`isMIS_iff_maximal`). MIS of an induced subgraph: `IsMISOn` (equivalent to `IsMIS` of `G.induce R`,
    `isMISOn_iff_isMIS_induce`).

## Not formalized

14. The `2f(η)`-degrading composition (initialization, `D` for `r` rounds, clean-up `C`, then `B`), the
    fault-tolerant parallel composition with `B'`/`B''`, and the colouring-based examples (`O(η + log* d)`,
    Ghaffari–Grunau, KSV uniform colouring): these compose black-box algorithms from the literature; the round
    arithmetic in the paper ("if `f(η) ≤ r` then `f(η)` rounds, otherwise `2r < 2f(η)`") is correct.
15. Theorem 6 of the full version ("asymptotically optimal") is the combination of `greedy_round_complexity`
    (`≤ n`) and `theorem_4_1` (`≥ (n − 5)/2`); not stated as a separate theorem. Lemma 2 of the full version (the
    `μ₂` bound) is not part of the BA and not formalized.
