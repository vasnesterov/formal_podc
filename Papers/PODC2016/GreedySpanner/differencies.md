# Differences between the formalization and the paper

Paper: Filtser, Solomon, *The Greedy Spanner is Existentially Optimal*, PODC 2016; full version
arXiv 1605.06852v2. Classification tags: **[gap]** = proof gap with a true statement, **[def]** =
under-specified definition, **[model]** = modelling choice, **[stronger]** = we prove more than
stated, **[cond]** = cited result taken as a hypothesis, **[omitted]** = not formalized.

## Model and definitions

1. **[model]** Weighted graphs are `SimpleGraph V` with `w : Sym2 V → ℝ≥0` on a finite vertex type `V`
   with `|V| = n`. An "`n`-vertex graph family" is a set of weighted graphs on this fixed `V`, which is
   the same up to relabelling. Weights may be `0` wherever the paper's positivity is not needed (see
   items 9 and 13).
2. **[model]** The greedy spanner (Algorithm 1) is modelled as a literal scan `greedy w t L` over an edge
   list `L`. `IsGreedySpanner G w t H` says that `H` is the output for *some* list `L` containing each
   edge of `G` exactly once in non-decreasing weight order. This is the paper's "`H` designates an
   arbitrary such spanner" when weights tie. All results are proved for every such execution.
3. **[def]** `OPT_t^sparse(𝒢)`/`OPT_t^light(𝒢)` are defined in §1.3 as a maximum over `𝒢`. For infinite
   families of weighted graphs the maximum of the lightness need not be attained, so we use the
   supremum (`familyOptSparse`, `familyOptLight`, `metricOptSparse`, `metricOptLight`, valued in `ℕ∞`
   and `ℝ≥0∞`). The per-graph optima `optSparse`/`optLight` are infima over all `t`-spanners. They
   are attained because the graphs are finite, but we never need that.
4. **[def]** Section 2 assumes all graphs are connected, but a family closed under edge removal must
   contain disconnected graphs. `mstWeight G w` is the minimum weight of a subgraph with the *same
   connected components* as `G`, i.e. a minimum spanning forest. `mstWeight_eq_iInf_isTree` shows
   that for connected `G` this is the minimum weight of a spanning tree, i.e. `w(MST(G))`.
5. **[model]** Lightness is `wt w H / mstWeight G w` in `ℝ≥0∞`. With `n ≤ 1`, or with no edges, this
   is `0/0 = 0`. Such degenerate cases are irrelevant to the paper.
6. **[model]** Stretch `t : ℝ≥0`. The paper's convention `t ≥ 1` is assumed where it is used: the
   greedy output being a `t`-spanner, Theorems 5 and 6, and Lemmas 5 and 6.
7. **[model]** A metric space on `V` is a weight function on the complete graph `⊤` (`IsMetricW`): `0` on
   the diagonal, positive off it, triangle inequality. The paper also views metrics as complete
   weighted graphs. The induced metric `M_H` has weights `inducedW H w ({x,y}) = δ_H(x,y)`. It is a
   metric when `H` is a spanner of a metric (`isMetricW_inducedW`).
8. **[def]** The doubling dimension is not defined explicitly in the paper. We use the standard
   definition (`IsDoubling w D`): every closed ball `B(x,r)` is covered by at most `2^D` closed balls of
   radius `r/2`, with centres in `V` and `D ∈ ℝ`. Then `M(n, D) = metricFamily V D`.

## Statements

9. **[stronger]** Lemma 3 (`lemma3`) is proved without the hypothesis `t ≥ 1` and for non-negative
   weights.
10. **[stronger]** Observation 2 (`IsGreedySpanner.exists_mst_le`, `IsGreedySpanner.mstWeight_eq`) holds
    for every `t` and for non-negative weights. It is derived from a general exchange lemma
    (`mstWeight_eq_of_forall_walk`): if every edge `uv` of `G` missing from `H ≤ G` is bypassed in `H`
    by a walk of edges of weight `≤ w(uv)`, then `H` contains a minimum spanning forest of `G`. The
    paper calls Observation 2 "immediate" and cites [ENS14, CW18].
11. **[stronger]** Theorem 5 (`theorem5`) is proved for any family closed under edge removal; the
    family may contain disconnected graphs. We also prove the two equalities that §1.3 uses as the
    definition of existential optimality (`existentially_optimal_sparse`/`_light`). The intermediate
    facts `optSparse H w t = |H|` and `optLight H w t = Ψ_G(H)` are `optSparse_greedy` and
    `optLight_greedy`.
12. **[cond]/[stronger]** Corollary 1. The size part is proved *unconditionally* and with an explicit
    bound (`corollary1_size`). For every real `t ≥ 2k − 1`, which includes `(2k−1)(1+ε)`, the greedy
    spanner has no cycle of length `≤ 2k` (`IsGreedySpanner.noShortCycles`). Hence it has
    `≤ n^{1+1/k} + n` edges by CSLib's Moore bound. The paper instead derives the size bound from
    Theorem 5 and Theorem 1 [CW18]. The lightness part `O(n^{1/k}(1/ε)^{3+2/k})` rests on the cited
    Theorem 1 [CW18]. We prove the transfer statement `greedy_le_of_forall_exists`: any upper bound
    `m` on the size and `ℓ` on the lightness of *some* `t`-spanner of *every* weighted graph on `V`
    holds for the greedy `t`-spanner. The `O(·)` statements become explicit bounds taken as
    hypotheses. The hypothesis ranges over *all* weighted graphs on `V`, including
    disconnected ones and ones with zero weights, whereas the cited results are stated (under the
    paper's §2 convention) for connected graphs with positive weights. The cited bounds extend to these
    graphs by applying them to each connected component, so the hypothesis is still a true statement,
    but it is slightly stronger than the literal cited one.
13. **[cond]** Corollary 2 is the same transfer statement (`greedy_le_of_forall_exists`) with the cited
    bound of [BFN19] as the hypothesis.
14. **[stronger]** Lemmas 5 and 6 (`lemma5`, `lemma6`) are stated in the paper for metric spaces. We
    prove them for an arbitrary *connected* weighted graph `G`; a metric is the case `G = ⊤`. The
    triangle inequality of `G` is never used. Lemma 6 needs positive weights on the edges of `G` and
    `1 ≤ t < 2`.
15. **[gap]** Lemma 6, proof. "An edge `e' ∈ H ∩ H'` covers itself" assumes that the chosen shortest
    `H`-path `P_{e'}` between the endpoints of `e' ∈ H` is the edge `e'` itself. This is used in the
    injectivity argument ("It must hold that `e₁` and `e₂` are in `H \ H'`"). It is true for greedy
    spanners: otherwise `H − e'` would be a `t`-spanner of `H`, contradicting Lemma 3. The paper does
    not argue it. Our proof treats all `e ∈ H` uniformly. `Q_e` is a shortest `H'`-path with
    `w_{M_H}(Q_e) ≤ t·w(e)`. Some edge `f(e) ∈ Q_e` has `e ∈ P_{f(e)}`, since otherwise `H − e` is a
    `t`-spanner of `H` (Lemma 3 again). Two edges with the same image would give
    `w_{M_H}(f(e)) ≥ 2·min(w(e₁), w(e₂)) > t·min(…)`.
16. **[model]** Observation 7 (`observation7`) is proved as stated for `t ≤ 2`, for any `t`-spanner
    `H ≤ ⊤` of a metric in `M(n, D)`. Typo in the paper's proof: the ball is covered by `2^{2ddim}` balls
    of radius "`4r`" in `M`; this should be radius `r/4` (two applications of the doubling property),
    which then lie in balls of radius `t·r/4 ≤ r/2` in `M_H`. The Lean proof uses `r/4`.
17. **[gap]** Observation 4 is not formalized. Its proof considers only MST edges of `M_G` that are not
    edges of `G`. An edge of `G` that is not a shortest path needs the same (verbatim) argument. In
    Theorem 6, Observations 2 and 4 are used only to show that `M` and `M_H` have the same MST
    weight. We prove this directly (`mstWeight_inducedW`): `w ≤ w_{M_H}` everywhere, with equality
    on the edges of `H`, and `H` contains an MST of `M` (Observation 2).
18. **[model]** Theorem 6 (`theorem6`) assumes `1 ≤ t < 2`; the paper writes only `t < 2`. For `t < 1`
    no `t`-spanner of a metric with `n ≥ 2` exists, so that case is degenerate.
19. **[cond]** Corollary 3 (`corollary3_of_forall_exists`) takes the cited Theorem 4 [Got15], and for the
    size Theorem 3 [Smi09], as the hypothesis "every metric in `M(n, 2D)` has a `t`-spanner with
    `≤ m` edges and lightness `≤ ℓ`". The `(ddim/ε)^{O(ddim)}` bounds become this hypothesis.

## Not formalized

20. **[omitted]** Theorems 1–4 and Lemma 1 (all cited) appear only as hypotheses.
21. **[omitted]** Section 5 is not formalized: Algorithm Approximate-Greedy, Lemma 8 (cited from
    [GLN02]), Observation 9 (cited from [Smi07]), Lemma 10 and Theorem 7. These are running-time
    claims (algebraic computation-tree model) on top of cited geometric facts.
22. **[omitted]** The Petersen-graph example of Figure 1 / §1.3, which shows that the greedy spanner is
    not instance-optimal, is not formalized. It is an illustration, not a claim used later.
