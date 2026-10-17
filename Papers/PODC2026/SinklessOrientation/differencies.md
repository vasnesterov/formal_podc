# Differences between the formalization and [Nolin, PODC'26]

Paper: Alexandre Nolin, *Brief Announcement: Sinkless Orientation Made Trivial*, PODC 2026,
pp. 333–336, DOI 10.1145/3796701.3815953 (4-page brief announcement; no full version found on arXiv
or elsewhere). Proofs in the paper are sketches; the formalization fills them in.

**Verdict.** No error affects the results. The deterministic algorithm (Theorem 2.1, Lemma 2.2,
Lemma 2.3, Theorem 1.1) is correct as described, with the minor slips and remarks listed below.

## Errors and imprecisions in the paper

1. **Lemma 2.2, "in particular" part: typo.** The paper says the distance-`⌈log_{δ−1} n⌉`
   neighbourhood "contains a node of degree `δ` or a cycle". It should be "degree `< δ`"
   (`lemma_2_2_clog`); "degree `< δ`" is what the proof gives and what Algorithm 2 uses.
2. **Lemma 2.2: the hypothesis `r ≥ 1` is redundant (harmless, not a slip).** For `r = 0` the
   bound `1 + δ((δ−1)^0 − 1)/(δ−2) = 1` holds trivially, so `lemma_2_2` omits it.
3. **Section 3, "more balanced orientations": remark on the literal phrasing (not an error).** The
   text asks for "every node `v` [to] have at least `max(ε deg(v), 1)` outgoing edges and
   `max(ε deg(v), 1)` incoming edges". The paper works with graphs of minimum degree `δ ≥ 3`
   (abstract), where this is meaningful; read literally for arbitrary graphs it would fail at
   degree-1 nodes (`no_orientation_in_and_out_single_edge`: a single edge has no such orientation).
   Corollary 1.2 itself uses `⌊ε deg(v)⌋`, and the "sinkless and sourceless" variant is restricted to
   nodes of degree `≥ δ`.
4. **Theorem 2.1: "separated by a distance of at least `k`" vs. "cannot be within distance `k`".**
   The definition of `k`-sinksparse (Section 1) says distance `≥ k`, while the proof of Theorem 2.1
   gives distance `> k`. We formalize the stronger `> k` (`IsSinkSparse`). (With `k = 4c` the
   weaker `≥ k` would also suffice for Algorithm 1, since radius `c` already works.)
5. **Constants.** Algorithm 1 uses `k = 4⌈log_{δ−1} n⌉`; only `k ≥ 2⌈log_{δ−1} n⌉` is needed
   (the balls of radius `k/2` must contain a low-degree node or a cycle, which Lemma 2.2 gives
   already at radius `⌈log_{δ−1} n⌉`). We keep the paper's `k`.
6. **"Optimal complexity Θ(log_δ n)"**: the formalization gives the explicit upper bound
   `8⌈log_{δ−1} n⌉ + 2 ≤ 16⌈log_δ n⌉ + 2` LOCAL rounds (`sinklessAlg_isLocal`, `theorem_1_1`,
   `clog_pred_le`). The matching lower bound is cited from [2, 3, 8] and not formalized.

## Modelling choices

* **Model.** Deterministic LOCAL with unique identifiers; nodes know `n = |V|`. Round complexity
  is formalized as *locality*: an orientation algorithm `A : ∀ G : SimpleGraph V, Orientation G` is
  `R`-local (`IsLocal A R`) if the orientation of every edge `uv` is the same in any two graphs on
  the same node set that agree on the edges incident to nodes at distance `< R` from `u`
  (`GAgree`). This is exactly what `u` can learn in `R` rounds of LOCAL, so `R`-locality is
  equivalent to an `R`-round full-information LOCAL algorithm. Node names (`V`) double as
  identifiers; the identifier function `id : V → ℕ` is used by the min-ID flooding. A node's rule
  may use the names in its view arbitrarily (e.g. a fixed choice function on finite sets of names).
  Since `A` is an arbitrary function of the whole graph on `V`, a rule may also depend on the global
  set `V` of identifiers (not only on `n`) — slightly more than standard LOCAL. This is harmless here:
  the algorithms are explicit and only use `n` and the local view, and it makes the lower bound
  (`LowerBound.lean`) stronger.
* **CONGEST.** Message sizes are not formalized (CSLib/Mathlib have no CONGEST accounting). For
  Theorem 2.1 the flooding algorithm (`floodAlg`, `MinIdRun.lean`) is a broadcast algorithm in the
  CSLib SET-LOCAL model whose states are triples `(ID, m, d)` of numbers `≤ max(ID, k)`, i.e.
  `O(log n)` bits — a CONGEST algorithm in substance. For Lemma 2.3 only the LOCAL round complexity
  (`2⌊k/2⌋ + 1`) is formalized; the paper's CONGEST implementation of the BFS/aggregation steps is
  not.
* **Tie-breaking in Algorithm 2.** The paper breaks ties by identifiers / depth ("the node of
  smallest degree", "if needed, breaking ties by depth in the tree, and identifier"). We use a fixed
  choice function (`Classical.epsilon`) on sets of nodes: BFS parents (`SimpleGraph.bfsParent`), the low-degree target
  (`lowPick`) and the non-tree edge (`ntPick`). The correctness proofs use only the specification
  lemmas of these choices (`SimpleGraph.Reachable.bfsParent_spec`, `lowPick_mem`, `ntPick_mem`), so they would go through for
  ID-based tie-breaking as well; locality only needs the choice to be a function of the (local) set
  of candidates.
* **Cycle case of Algorithm 2.** The paper distinguishes "`t` has a neighbour `t'` at equal depth"
  and "`t` has two neighbours `t'`, `t''` of lower depth". Both are covered uniformly by a
  *non-tree edge* `(t, t')` with `depth t' ≤ depth t` and `t' ≠ parent t` (`ntSet`); in the second
  case `t'` is the lower neighbour that is not the BFS parent. The repaired edges are the tree path
  `s → t`, the edge `t → t'`, and the tree path from `t'` up to the highest-depth common ancestor
  `v` of `t, t'` (`RepCycle`); this is the paper's "orient the cycle consistently and the path from
  the sink to the cycle towards the cycle".
* **Simultaneous repairs.** `repairOrientation` applies all repairs at once. To make it a total
  function (needed to state locality for all inputs), an edge claimed by repairs in both directions
  keeps its old orientation; under the hypotheses of Lemma 2.3 this never happens
  (`lemma_2_3_core`).
* **"Contains a cycle"** (Lemma 2.2, Lemma 2.3) is formalized as: some cycle of `G` has all its
  vertices in the ball (`ContainsCycle`). It is equivalent to the existence of a non-tree edge in
  the BFS ball (`HasBackEdges`, `hasBackEdges_of_containsCycle`, `containsCycle_of_hasBackEdges`).
  "Degree" is always the degree in `G` (`deg`, instance-free `ncard` of the neighbour set).
* **Lemma 2.3 hypothesis.** The paper assumes a `k`-sinksparse orientation; we only need distinct
  `δ`-sinks at distance `> 2⌊k/2⌋` (`lemma_2_3_core`; `lemma_2_3` derives it from
  `k`-sinksparseness).
* **Graphs.** Theorem 2.1 and Lemma 2.3 hold for arbitrary (even infinite) simple graphs; Lemma 2.2
  and Theorem 1.1 assume a finite node set.

## Tightness remark after Theorem 2.1

The paper only asserts that `O(k)` rounds for `k`-sinksparse orientations is "obviously tight, even
in Local" via "a standard argument". We prove it (`LowerBound.lean`, `sinkSparse_lower_bound`):
any `T`-local orientation algorithm with `2T + 2 ≤ k` puts two sinks on some `(k+1)`-node path
(given `2T + 2 + 3k` identifiers), so `T ≥ (k − 1)/2`, versus the upper bound `k + 1`. The constant
`c` is thus `1/2`. Instances are paths plus isolated nodes on a common node set.

## Not formalized

* The randomized part of Theorem 1.1 (`O(log_δ log n)` rounds via the shattering argument of
  Ghaffari–Su [8]) and Corollary 1.2 (balanced orientations via the reductions of [7, 8]): they rely
  on external results not available in Lean. Only the remark on the literal phrasing of item 3 is checked.
* The `Ω(log_δ n)` (deterministic) and `Ω(log_δ log n)` (randomized) lower bounds cited from earlier
  work.
