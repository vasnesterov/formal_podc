# Distributed approximation of MaxIS and maximum matching — PODC 2017

Reuven Bar-Yehuda, Keren Censor-Hillel, Mohsen Ghaffari, Gregory Schwartzman. *Distributed Approximation
of Maximum Independent Set and Maximum Matching.* PODC 2017. DOI
[10.1145/3087801.3087806](https://doi.org/10.1145/3087801.3087806). Formalized version: arXiv
[1708.00276](https://arxiv.org/abs/1708.00276) v1; numbering follows it. Scope: Section 2 (deterministic
parts). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The local-ratio theorem (Thm 2.1), Lemma 2.2, the `Δ`-approximation of
the sequential meta-algorithm (Algorithm 1) for *every* choice of independent sets, the colouring-based
Algorithm 3 (a `Δ`-approximation in `O(Δ)` rounds after a `(Δ+1)`-colouring), the layer argument of
Lemma A.1, and the 2-approximation for maximum-weight matching via the line graph (Thm 2.10,
deterministic half) all hold. They need closed neighbourhoods and `Δ ≥ 1`. Line 11 of Algorithm 1, read
literally, breaks the approximation; the text of Section 2.1 has the correct rule.

## Mistakes in the paper

* **Algorithm 1, line 11, read literally, is not a `Δ`-approximation.** Inside
  `foreach u ∈ U, foreach v ∈ N(u)` it sets `w₁(v) = w(v) − w(u)`, so a vertex adjacent to several
  `u ∈ U` keeps only the reduction of the last one. The text before Lemma 2.2 defines the sum
  `w₂[v] = ∑_{u∈U∩N(v)} w[u]`. Counterexample (`Δ = 2`): edges `a₁v, a₂v, a₁b`, weights
  `w(a₁)=3, w(a₂)=1, w(v)=2, w(b)=3`, `U = {a₁, a₂}` processed in this order (loop over the closed
  neighbourhoods `N[u]`, see the next item). Then `v` keeps weight `1` (`a₁, a₂, b` drop to `0`), the
  recursion can only return `{v}`, and line 13 adds nothing. The output `{v}` has weight 2 while `{v, b}`
  has weight 5 > 2·2. This is a pseudocode slip: with `w₁(v) = w₁(v) − w(u)` everything is correct.
  (`LiteralLine11.literal_line_11_fails`)
* **`N(v)` must be the closed neighbourhood, and `Δ ≥ 1` is needed.** The proof of Lemma 2.2 uses
  `w₂[u] = w[u]` for `u ∈ U` and "at most `|N(u)| − 1` vertices of `N(u)` are independent". Both hold
  only for `N[u] = N(u) ∪ {u}`, which is also what Algorithms 2 and 3 do (`w(v) = 0` after reducing).
  The correct bound on `|I ∩ N[u]|` for an independent `I` is `max(1, deg u)`, not `deg u`. So the
  `Δ`-approximation needs `Δ ≥ 1`; an edgeless graph is the degenerate counterexample. We prove Lemma 2.2
  for closed neighbourhoods and every factor `r` that bounds `|I ∩ N[u]|`. This gives `r = Δ` for
  `Δ ≥ 1` and `r = 2` on line graphs. (`lemma_2_2`, `card_inter_cl_le`, `localBound_of_degree_le`)
* **Under-specified details.**
  * Algorithm 1 terminates only if `U ≠ ∅` while vertices remain. Our choice rules require this.
  * In Algorithm 3, `removed`/`addedToIS` must go to *all* neighbours in `G`, not to the current
    `N(v)`. Otherwise an earlier candidate never learns the decision of a later candidate neighbour
    and waits forever.
  * There are `⌈log₂ W⌉ + 1` weight layers, not `log W`.
* **Typos.** In the proof of Lemma 2.2 several indices are swapped (`w₂[u]x*[u]` for `w[u]x*[v]`,
  `x'[u]` for `x'[v]`, `|N(v)|−1` for `|N(u)|−1`). §2.3 says "removal stage" for the addition stage.
  §2.4 says "weighted nodes" for weighted edges.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finite simple graph `G`, arbitrary real vertex weights (nonpositive vertices are removed). For matchings,
  the line graph `G.lineGraph` of Mathlib with edge weights.
* Algorithm 1 has the graph fixed and the current vertex set = positive-weight vertices. The independent set
  of line 7 is an arbitrary *rule* (a function of the current weights: independent, positive vertices,
  nonempty while vertices remain). Every result is proved for every rule.
* Algorithm 3 runs in CSLib's synchronous locally-iterative (SET-LOCAL) model
  `Cslib.LocallyIterative.Algorithm`. It is deterministic with no failures. Every node reads the set of
  its neighbours' states (= messages); states carry identifiers, so sums over neighbours are exact. The
  round number is known. The `(Δ+1)`-colouring is a black box: any proper colouring `c` with `c v < k` is
  part of the input. One iteration of the paper takes two rounds: "select" (local colour maxima among
  remaining nodes become candidates) and "reduce". Candidates decide in every round (lines 12–17).
* Algorithm 2 is covered only abstractly. If each phase picks a maximal independent set of the top weight
  layer, the removal stage has `⌈log₂ W⌉ + 1` phases. The randomized MIS black box, the waiting rule and
  the probability bound are not modelled.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (local ratio, arbitrary feasible set `C ⊆ ℝⁿ`; set form) | `theorem_2_1`, `isApprox_add` | `Basic.lean` |
| Lemma 2.2 (general factor `r`; `r = Δ`) | `lemma_2_2`, `lemma_2_2_total`, `localBound_of_degree_le` | `Lemma22.lean` |
| Algorithm 1 is a `Δ`-approximation (any choice of `U`) | `seqLR`, `seqLR_isApprox`, `algorithm_1` | `SeqLR.lean` |
| Level-by-level characterization of the output of Algorithm 1 | `mem_seqLR_iff`, `mem_seqLR_iter` | `SeqLR.lean` |
| §2.3: colour rule; after `k` iterations all nodes candidate or removed | `colorRule`, `colorRule_removal` | `Coloring.lean` |
| Algorithm 3: outputs by round `3k`, final and correct, `Δ`-approx. | `alg3`, `algorithm_3`, `output_eq`, `output_sound` | `Distributed.lean` |
| Lemma A.1 / Thm 2.3, deterministic part (`⌈log₂ W⌉+1` phases) | `top_layer_drops`, `removal_stage` | `Layers.lean` |
| §2.4: matchings meet `N[e]` in `L(G)` in `≤ 2` edges; Alg. 1 on `L(G)` is a 2-approx. | `matching_localBound`, `seqLR_lineGraph_isApprox` | `Matching.lean` |
| Theorem 2.10, deterministic half (Alg. 3 on `L(G)`, `3k` rounds of `L(G)`) | `theorem_2_10_det` | `Matching.lean` |
| `Δ(L(G)) ≤ 2Δ − 2` | `lineGraph_degree_le` | `Matching.lean` |
| Line 11 taken literally fails | `LiteralLine11.literal_line_11_fails` | `LiteralLine11.lean` |

**Not formalized.** The `(Δ+1)`-colouring in `O(Δ + log* n)` rounds [BEK14, Bar15]. Message sizes and
the CONGEST simulation on the line graph (Defs. 2.4–2.7, Thms. 2.8–2.9). How rounds of `L(G)` are
simulated in `G`. All randomized results (Thm 2.3's probability, randomized half of Thm 2.10, Section 3,
Appendix B).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity (`Main.lean`): every finite graph has a proper colouring with `|V|` colours
(`exists_proper_coloring`), so `algorithm_3` applies to all graphs and weights. `singletonRule` (classical
sequential local ratio) and `topMISRule` (a maximal independent set of the top layer, satisfies
`IsTopMIS`) are admissible rules. The distributed model is CSLib's `Cslib.LocallyIterative` with the
identifier API of `Cslib/Computability/Distributed/Local/Identifiers.lean`.

**CSLib candidates** (marked `-- CSLib candidate` in the code): `isMatchingSet_iff_isIndepSet`,
`card_filter_mem_le_one`, `matching_localBound`, `lineGraph_degree_le` (line graphs); `exists_mis`/`mis_maximal`
(a maximal independent subset of a finset); `theorem_2_1` and `lemma_2_2` with `seqLR` (local ratio for
maximum-weight independent set).
