# Differences between the formalization and the paper

Paper: Bar-Yehuda, Censor-Hillel, Ghaffari, Schwartzman, *Distributed Approximation of Maximum
Independent Set and Maximum Matching*, PODC 2017; arXiv 1708.00276 v1 (numbering follows it).
Scope: Section 2 (Theorem 2.1, Lemma 2.2, Algorithm 1, Algorithm 3, the deterministic parts of
Lemma A.1 / Theorem 2.3, Section 2.4 and the deterministic half of Theorem 2.10). Section 3 and
Appendix B (randomized `O(log Δ / log log Δ)` matching algorithms), the probability statements
of Theorem 2.3, and Theorems 2.8/2.9 (CONGEST simulation on the line graph) are not formalized.

## Errors and imprecisions in the paper

1. **Algorithm 1, line 11 overwrites instead of accumulating.** `w₁(v) = w(v) − w(u)` inside
   `foreach u ∈ U, foreach v ∈ N(u)` keeps only the reduction of the last `u` adjacent to `v`. The
   text of Section 2.1 (`w₂[v] = ∑_{u ∈ U ∩ N(v)} w[u]`) and the proof of Lemma 2.2 use the sum.
   Taken literally, Algorithm 1 is not a `Δ`-approximation: `LiteralLine11.literal_line_11_fails`
   (4 vertices, `Δ = 2`, output weight 2, optimum 5). We formalize the sum (`red`), i.e. line 11 read
   as `w₁(v) = w₁(v) − w(u)`.
2. **Open vs. closed neighbourhood.** Section 2.1 and Lemma 2.2 write `N(v)` but need the closed
   neighbourhood `N[v] = N(v) ∪ {v}`: the proof uses `w₂[u] = w[u]` for `u ∈ U` (so `w₁[u] = 0`)
   and "at most `|N(u)| − 1` nodes of `N(u)` can be in an independent set", and Algorithm 2/3 set
   `w(v) = 0` after `v` reduces (Algorithm 3, line 18 even writes `N(v) \ {v}`). With open
   neighbourhoods `w₁[u] = w[u]`, Algorithm 1 need not terminate and the residual bound fails. We use
   `N[u]` (`cl`, `red`); the paragraph "`w₂(v) = w(v)` for every `u ∈ N(v)`" in the single-vertex
   description is read the same way.
3. **`Δ ≥ 1`.** The bound "an independent set meets `N[u]` in at most `|N[u]| − 1 = deg(u) ≤ Δ`
   vertices" fails for an isolated `u ∈ U` (the set `{u}` meets `N[u]` in one vertex). The correct
   bound is `max(1, deg u)`. So the statement needs `Δ ≥ 1` (for an edgeless graph a "0-approximation"
   is impossible; the algorithm is then exact). Our theorems assume `1 ≤ Δ` and `deg v ≤ Δ`
   (`card_inter_cl_le`, `localBound_of_degree_le`, `algorithm_1`).
4. **Termination of Algorithm 1** needs `U ≠ ∅` whenever vertices remain (line 7 allows any
   independent set, including `∅`, and then the recursion does not progress). Part of our `Rule`
   (`pick_nonempty`); the paper's two instances satisfy it.
5. **Algorithm 3, recipients of `removed`/`addedToIS`.** A node deletes a neighbour from `N(v)` when
   that neighbour becomes a candidate, and candidates send `reduce` only to their current `N(v)`. If
   "send ... to all neighbors" (lines 8, 13, 16) meant the current `N(v)`, an earlier candidate would
   never hear from its later candidate neighbours and would wait forever (line 12). The algorithm is
   correct when these messages go to all neighbours in `G`. In our model every node sees the states of
   all its `G`-neighbours, which realizes this reading.
6. **Typos in the formulas of the proof of Lemma 2.2**: `∑_v ∑_{u ∈ U∩N(v)} w₂[u] x*[u]` should be
   `∑_v ∑_{u ∈ U∩N[v]} w[u] x*[v]`; "at most `|N(v)| − 1`" should be `|N(u)| − 1`; in
   `x'·w₂ = ∑_{u∈U} ∑_{v∈N(u)} w₂[u] x'[u]` the last factor should be `x'[v]`. §2.3: "Thus, the
   removal stages finishes in O(Δ) rounds" (second occurrence) should be "addition stage". §2.4: "Let
   `G` be a graph with weighted nodes" should be weighted edges.
7. **Number of layers.** With integer weights in `[1, W]` there are `⌈log₂ W⌉ + 1` layers
   `L₀, …, L_{⌈log₂ W⌉}` (`L₀ = {w = 1}`), so the removal stage of Algorithm 2 takes
   `⌈log₂ W⌉ + 1` phases, not `log W` (matters only for `W = 1`). `removal_stage` proves the bound
   `⌈log₂ W⌉ + 1`.

## Modelling choices

* **Weights.** Real weights, arbitrary sign. Nonpositive vertices are simply never chosen (the
  paper assumes `w : V → ℝ₊`; Theorem 2.1 is stated for arbitrary real vectors, as in the paper).
  Integrality is used only for the layer argument (`removal_stage`).
* **Approximation.** `IsApprox G r w S`: `S` independent and `w(T) ≤ r · w(S)` for every independent
  `T`. For `r > 0` this is the paper's "`r`-approximate". Theorem 2.1 is also stated for an arbitrary
  feasible set `C ⊆ ℝⁿ` (`IsApproxVec`, `theorem_2_1`).
* **Lemma 2.2 is proved for a general factor `r`**: every independent set meets each `N[u]`,
  `u ∈ U`, in at most `r` vertices (`LocalBound`). `r = Δ` gives the paper's lemma, `r = 2` on the
  line graph gives Section 2.4. The paper does the `r = 2` case by re-reading the inequality chain.
* **Algorithm 1** keeps the graph fixed; the current vertex set is `pos w` (positive weights).
  Since weights only decrease, this equals the paper's deletion of nonpositive vertices. The choice
  of `U` is any function of the current weights (`Rule`): independent, among positive vertices,
  nonempty while vertices remain. Correctness is proved for every such rule.
* **Algorithm 3** is modelled in CSLib's synchronous locally-iterative model (each node reads the
  set of its neighbours' states; states carry identifiers). One iteration of the paper takes two
  rounds here: a *select* round (local colour maxima among remaining nodes become candidates) and a
  *reduce* round (neighbours subtract the reduced amounts and drop out if `≤ 0`). In the paper,
  removals and reductions of one iteration are only seen in the next iteration, so a node may
  postpone its turn by an iteration because of a stale neighbour; our two-round version selects
  exactly the local maxima of the current remaining set, which makes it an exact instance of
  Algorithm 1. Decisions of candidates (lines 12–17) are taken in every round: a candidate of
  level `j` outputs `NotInIS` if a neighbour that became a candidate later output `InIS`, and
  `InIS` when every neighbour is removed, an earlier candidate, or a later candidate that output
  `NotInIS`. Line 12 for still-remaining nodes ("`N(v) = ∅` ⇒ `InIS`") is not a separate rule: such
  a node becomes a candidate in the next select round and decides one round later.
* **Removed nodes** keep their state (weight `≤ 0`, output `NotInIS`) instead of halting; their
  weight keeps decreasing, which is irrelevant.
* **Colouring** is a black box: the colour `c v < k` is part of the initial state. The paper uses a
  `(Δ+1)`-colouring computed in `O(Δ + log* n)` rounds [BEK14, Bar15]; that algorithm is not
  formalized (CSLib has Linial's colouring and the standard colour reduction, which give
  `O(Δ² + log* n)`).
* **Round complexity.** Algorithm 3: all nodes output by round `3k` (`2k` rounds of removal stage,
  then `≤ k` rounds of addition stage), i.e. `3Δ + 3` with `k = Δ + 1` — the paper's `O(Δ)`.
  Outputs never change once produced and are correct when produced (`output_sound`).
* **Algorithm 2 / Theorem 2.3.** Only the deterministic core is formalized: if each phase picks a
  maximal independent set of the top layer (`Rule.IsTopMIS`), the top layer empties (Lemma A.1) and
  the removal stage takes `⌈log₂ W⌉ + 1` phases. The distributed implementation of Algorithm 2 (its
  waiting rule, the MIS black box with failure probability `p`, the union bound, the addition-stage
  bound) is not formalized. Correctness of Algorithm 2 is covered by `algorithm_1` for any rule.
* **Matchings (Section 2.4, Theorem 2.10).** A matching is a finite set of edges with pairwise
  disjoint endpoints (`IsMatchingSet`), equivalently an independent set of Mathlib's
  `G.lineGraph` (`isMatchingSet_iff_isIndepSet`). Theorem 2.10 (deterministic half) is proved for
  Algorithm 3 run on `L(G)` with a black-box proper colouring of `L(G)` with `k` colours; the round
  bound `3k` is in rounds of `L(G)`. `L(G)` has maximum degree `≤ 2Δ − 2` (`lineGraph_degree_le`), so
  `k = 2Δ − 1` colours suffice. The simulation of `L(G)`-rounds in `G` is not formalized: in LOCAL it
  costs `O(1)` rounds of `G` per round of `L(G)`; for CONGEST the paper relies on Theorem 2.8 (local
  aggregation algorithms), whose proof is only a sketch, and Theorem 2.9 (stated for Algorithm 2;
  "the exact same technique" for Algorithm 3).
* **Message size** (CONGEST) is not formalized: our messages are full node states (identifier,
  colour, a weight, a level, a decision bit), i.e. `O(log n)` bits when weights are polynomial.

## Not formalized

* Theorem 2.3's probability bound and the randomized MIS black box; the addition-stage round bound
  of Algorithm 2.
* Definitions 2.4–2.7, Observation 2.6, Theorems 2.8 and 2.9 (local aggregation / CONGEST on the line
  graph); the randomized half of Theorem 2.10.
* Section 3 and Appendix B (Theorems 3.1, 3.2, Lemma B.1 and the `(2+ε)`/`(1+ε)` matching
  algorithms).
