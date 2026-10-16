# Differences between the formalization and the paper

Paper: Lewis Tseng, Nitin H. Vaidya, *Fault-Tolerant Consensus in Directed Graphs*, PODC 2015
(formalized from the arXiv version 1412.8532v2, *Crash-Tolerant Consensus in Directed Graphs*;
numbering follows it).

Classification used below: **false statement**, **false only in a degenerate case**, **proof gap
(statement true)**, **under-specified definition**, **typo**, **modelling choice**.

## Section 1–2: model and graph notions

1. **Modelling choice — synchronous model** (`SyncModel.lean`). Deterministic algorithms in lock-step
   rounds on a static digraph `G`; a node knows `G` and its identity. In round `r` a node sends one
   (optional) message to each out-neighbour and updates its state from its *inbox* (the message from
   each in-neighbour, if any). Crash faults: `crash u = some c` means `u` behaves correctly before
   round `c`, its round-`c` message reaches an arbitrary subset `part u` of its out-neighbours, and it
   is silent afterwards; at most `f` nodes crash; the crash pattern may depend on the inputs. The
   decision is the first output. Agreement and validity concern fault-free nodes; validity is "the
   decision is the input of *some* node" (Section 1). The paper's self-loops (`i ∈ Nᵢ⁺, Nᵢ⁻`) are
   modelled by giving each node its own state; self-loops in `G` are harmless.
2. **Definition 2** (CT node connectivity) is `CTConn G k`, with `F ⊂ V` read as `F ≠ V`
   (written `∃ v, v ∉ F`). We prove it equivalent to the "1-reach" condition of later papers
   (`ctConn_iff_oneReach`): every two nodes of `G_F` have a common ancestor in `G_F`. The proof of
   Theorem 1 uses this equivalence silently ("there exists a pair `i, j` such that no node has paths
   to both") — **proof gap (statement true)**, a short finite argument (a node with a maximal set of
   descendants reaches everything).
3. **Definitions 3–4** (rooted spanning tree, source) are replaced by `IsRoot G F s` (`s ∉ F` reaches
   every node of `G_F`), which is equivalent. The fault-tolerant diameter `d` of equation (1) is
   `ftDiam G f`, defined as the least `D` such that every root of every `G_F` (`|F| ≤ f`) reaches
   all of `G_F` within `D` hops (`FTDiamLE`); this is `max_F max_s height(s, G_F)` since a BFS tree
   has minimum height. We prove `d ≤ n − 1` (`ftDiam_le_card`).

## Theorem 1 (necessity)

4. Faithful (`theorem1`), for any input domain with two distinct values and any message/state types.
   The step "the only input value learned by `x` is 0, so to satisfy validity 0 should be the output
   of `x`" is made rigorous by indistinguishability: `Sᵢ` only hears from `Sᵢ`
   (`state_eq_of_closed`), so `i` behaves as in the execution where *all* inputs are 0, where
   validity forces output 0. Only crash-at-start is used, so the necessity holds for initially dead
   nodes as well.

## Theorems 2–3 (Algorithm Min-Max)

5. **Modelling choice.** Values are `Bool` (`false` = 0). The phase length is any `D` with
   `FTDiamLE G f D` (`theorem3`); the paper's `D = d` gives `theorem2`, and `D = n − 1` is covered
   (Section 3's remark that `d` can be replaced by `n`). "Set `vᵢ` to the max/min of all values
   received" includes the own value (`recvd`).
6. **Proof of Theorem 3: minor gaps (statement true).** (a) The paper picks consecutive crash-free
   phases `p_t, p_{t+1}` and assumes "w.l.o.g." that `p_t` is a Min phase; we instead pigeonhole over
   the `f + 1` *disjoint* pairs (phase `2k+1`, phase `2k+2`), so the clean pair is always Max-then-Min
   (`exists_clean_pair`). (b) The paper stops at "agreement is achieved" after phase `p_{t+1}`; one
   also needs that agreement among non-crashed nodes is preserved by the remaining phases
   (`unanimity`). (c) "Validity is obvious": for binary values it follows because if all inputs are
   equal the values never change.
7. The agreement argument is formalized once, abstractly, for any binary trajectory following the
   Min/Max rule (`minmax_core`, `MinMaxCore.lean`), and reused for Claim 2 of Algorithm MVC.

## Section 2.3, Theorem 4 (Algorithm MVC)

8. **Under-specified: integer inputs.** The paper says "input being in the range `[0, K]`", but MVC
   only works for *integer* inputs (the OUTER-LOOP tests `tᵢ = l` for integers `l`); e.g. with
   all inputs equal to `1/2` and `K = 1` everybody outputs `1`, which is nobody's input. We take inputs in
   `{0, …, K}` (`SolvesOn G f {x | x ≤ K}` with `x : ℕ`).
9. **Modelling choice (encoding).** Each OUTER-LOOP iteration is a block of `(2f+2)·D + 1` rounds:
   one local round (STEP III of the previous iteration, then STEP I) followed by the INNER-LOOP rounds;
   after exiting, a node keeps running (its decision is fixed), which is harmless because all
   non-crashed nodes exit in the same iteration.
10. **Typo** in step 4 of the INNER-LOOP: "`If |min{b | (∗, b) ∈ Bᵢ, b > l}| > 0`" should read "if
    `{b | (∗, b) ∈ Bᵢ, b > l}` is non-empty".
11. **Proof of Lemma 3 / Claim 3: imprecise (statement true).** Claim 3's proof states "node `i`
    changes `vᵢ[0]` from 0 to 1 *if and only if* it receives `(1, x)` with `x > 0`"; only the "only
    if" direction holds (receiving `(1, x)` in a Min phase does not change `vᵢ`), and only that
    direction is needed. The induction step says "suppose that for all OUTER-LOOP iterations `l ≥ r`"
    (should be `l ≤ r`, **typo**). We prove the invariant directly for one iteration (`inv_iteration`:
    every alive node with `v = 1` has `t > l`), with the hypothesis that all alive nodes enter the
    iteration with `t ≥ l` (`t_ge_iter`), which the paper states only in the informal description.
12. **Lemma 4, case "no fault-free node exits the OUTER-LOOP".** The paper argues the output `K` is
    valid "since some node has input `K`". We show this case never happens when inputs are in
    `[0, K]` (all alive nodes would have `t > K`, but `t` is always an input, Claim 5). The validity
    proof is otherwise the paper's (Claims 5, 6).
13. Lemma 3 is stated for `0 ≤ l < K`; we use it for `l = K` as well (same proof).

## Section 3, Theorem 5 (fixed iterative algorithms)

14. **Under-specified definition: when does an iterative algorithm output?** The paper defines
    iterative algorithms by their state update only. Two readings:
    * *eventual* (`SolvesEventually`): from some iteration on, the values of fault-free nodes agree
      and are inputs;
    * *fixed iteration* (`SolvesAt … T`): the output is the value after iteration `T` (this is how
      Algorithm Min-Max, the motivating example of Section 3, outputs).
    The proof's key step "if `Rᵢ[t]` contains all 0's or all 1's, then `Z(Rᵢ[t])` should map to 0 or
    1, otherwise validity or agreement is violated", and the case "the source's state can only be 1
    throughout the execution", are justified only under the eventual reading.
15. **Theorem 5's proof is wrong under the fixed-iteration reading — false conclusion for the
    paper's graph.** For `f = 1`, the fixed transition function `Z(R) = ¬max R` with output after
    iteration `T = 4` solves binary crash consensus on the graph of Appendix B (source, clique of 2,
    leaf), for every crash pattern with at most one crash, including mid-round crashes
    (`notMax_solvesAt`, checked by kernel evaluation over all delivery patterns). The values
    alternate between "true" and "negated", so `¬max` simulates alternating Max/Min rounds; it violates
    the step "`Z` maps all-1 collections to 1". Bounded search (Python, outside Lean) also confirms
    `¬max`, `T = 4` for `f = 2`; for `f = 3` it fails at `T = 4` (three nodes crashing in rounds
    0, 1, 2 with partial deliveries make the leaf disagree with the clique). Whether Theorem 5 holds under the
    fixed-iteration reading (with another graph) is left open.
16. **Theorem 5 under the eventual reading: proved** (`theorem5`) for every `f`, with the paper's
    graph and the paper's case analysis, after deriving `Z({a}) = a` and `Z(1, 1, …) = 1` from
    validity. **False only in a degenerate case (proof):** the paper's executions crash one clique
    node, which is impossible for `f = 0`; for `f = 0` the graph is the path `s → c → l` and the same
    case analysis works without crashes (Case 2 cannot occur because `R = R'`). Our proof is uniform
    in `f`.
17. **Modelling choice.** In an anonymous network the transition function sees the *multiset*
    `Rᵢ[t]` (own value plus received values) — the paper counts 0's and 1's. A set-valued `Z` (the
    paper also says "the union") is a special case, so the impossibility covers it; `¬max` depends only
    on the set, so the counterexample also covers it. States are binary.
18. **Typo.** Claim 8 speaks of "a pair of set of `2f + 1` values" with `|R₀| = |R₁| = f + 1`. Claim 8
    is not used by the case analysis (the three cases are exhaustive by themselves).

## Section 4 (asynchronous approximate consensus)

19. **Modelling choice — asynchronous model.** We reuse the asynchronous message-passing model on
    digraphs of the PODC 2020 formalization (`Papers/PODC2020/AsyncApproxBCDirected/AsyncModel.lean`):
    deterministic event-driven algorithms, reliable FIFO links with adversarial finite delays, fairness
    on links between correct nodes. For Theorem 6 (`CrashSolvesOn`) faulty nodes are *initially dead*
    (a special case of crashes, so the impossibility is stronger), and validity is "between two
    inputs of any nodes" (the paper's "convex hull of all the inputs").
20. **Theorem 6** (`theorem6`, `theorem6'`): faithful; the paper's condition is
    `AsyncApproxBCDirected.CCA G f` (partition condition with `f + 1` distinct nodes), equivalent to
    2-reach (`theorem17b`). The informal "nodes in `L` cannot wait for any message from `O(L)`" is made
    precise by replaying two executions (with `O(R)`, resp. `O(L)`, initially dead) into one
    failure-free execution. Inputs `0` and `2ε` as in the paper (any two admissible inputs more than
    `ε` apart).
21. **Lemma 1** (`lemma1`): the graph part (`reachᵢ(Fᵢ) ∩ reachⱼ(Fⱼ) ≠ ∅`), from 2-reach.
22. **Algorithm WA, pseudocode bug / under-specified: termination fails if early messages are
    handled on arrival (fixable).** The pseudocode does not say what happens to a phase-`p` message
    arriving before `i` enters phase `p`; under the buffering convention (process it on entering
    phase `p`, keep relaying afterwards) simulation finds no deadlock. If it is handled on arrival: "On entering phase `p`: `Rᵢ[p] = {vᵢ[p−1]}`, `heardᵢ[p] = {i}`" *resets*
    the sets, but the handler "when message `(h, j, p)` is received for the first time" may run for a
    phase-`p` message before `i` enters phase `p`; that message is then lost (later copies are not
    "first time"). Concrete failure-free run found by simulation (`f = 1`, 5 nodes, edges
    `0→1,2,3; 1→0,2,4; 2→0,1,3,4; 3→4`, which satisfies the condition of Theorem 6): node 4 receives
    the phase-2 messages of nodes 1 and 2 while still waiting in phase 1, resets on entering phase 2,
    and then waits forever: Condition WAIT needs `reach₄(F) ⊆ heard₄[2] = {0, 3, 4}` with `|F| ≤ 1`,
    but `reach₄({1}) ∋ 2` and `reach₄({2}) ∋ 1`. The evident fix — accumulate early messages (do not
    reset) and re-check WAIT on entering a phase — is what we formalize. The handler also re-computes
    `vᵢ[p]` for late phase-`p` messages and checks WAIT only upon receipt (a node that satisfies WAIT
    on entry and receives nothing would wait forever, possible for `f = 0` if self-messages are not
    delivered); the fixed version computes each `vᵢ[p]` once.
23. **Theorem 7 is only sketched** ("the rest of the proof is standard"). We formalize it for the
    fixed algorithm (`wa`, `WA.lean`): recorded phase-`p` messages are never reset, and WAIT is
    re-checked after every receipt and on entering a phase, so each `vᵢ[p]` is computed once.
    **Implicit assumption:** `p_end` "as a function of `n, f, M, m`" requires the input range
    `[lo, hi]` to be known; we take the explicit bound `(1 − 1/n)^{p_end}·(hi − lo) ≤ ε`
    (`theorem7`). Averaging is over the *set* `Rᵢ[p]`, as in the paper; the contraction by `1 − 1/n`
    per phase (omitted in the paper) is `avg_bounds` / `contraction`. Lemma 1 is used as
    stated. **Proof gap (statement true for the fixed algorithm):** the sketch omits liveness
    (every fault-free node eventually satisfies WAIT: flooding along paths of never-crashed nodes,
    with `F` = the nodes that ever crash) and the contraction step.
24. **Modelling choice — general crashes for Theorem 7** (`AsyncCrash.lean`): the PODC 2020 model with
    a time-varying crashed set given by a crash schedule; a crashed node takes no more steps, its
    messages already in channels may or may not be delivered (this models a crash in the middle of a
    broadcast); fairness only on links between nodes that never crash. The initially-dead model of
    Theorem 6 is the special case of a constant schedule (`crashSolvesOn_of_gen`), so both theorems
    combine into the tight characterization `async_consensus_iff` (for `0 < ε < hi − lo`).
