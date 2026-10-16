# The Greedy Spanner is Existentially Optimal — PODC 2016

Arnold Filtser, Shay Solomon. *The Greedy Spanner is Existentially Optimal.* PODC 2016. DOI
[10.1145/2933057.2933114](https://doi.org/10.1145/2933057.2933114). Formalized version: arXiv
[1605.06852](https://arxiv.org/abs/1605.06852) v2 (full version, January 2020); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** Lemma 3, Observation 2, Theorem 5 (greedy is existentially optimal for size
and lightness in any family closed under edge removal), Lemmas 5 and 6, Observation 7 and Theorem 6
(near-optimality in doubling metrics) are all proved as stated. Corollaries 1–3 are proved relative to
the cited external bounds, which are taken as hypotheses. The only issues are a small unstated step in
the proof of Lemma 6 and some loose definitions. None affects any statement.

## Mistakes in the paper

There are no false statements. Minor points:

* **Lemma 6: unstated step (proof gap, statement true).** The injection `f : H → H'` sets `f(e) = e`
  for `e ∈ H ∩ H'` because "an edge `e' ∈ H ∩ H'` covers itself". So the fixed shortest path
  `P_{e'}` in `H` between the endpoints of `e'` must be the edge `e'` itself. This fact is used in the
  injectivity step ("it must hold that `e₁` and `e₂` are in `H \ H'`"), but the paper never proves it.
  It is true for the greedy spanner: a different path of weight `≤ w(e')` would make `H − e'` a
  `t`-spanner of `H`, contradicting Lemma 3. Our proof avoids the special case. For *every*
  `e ∈ H`, `f(e)` is an edge of a shortest `H'`-path `Q_e` whose `P_{f(e)}` contains `e` (`lemma6`).
* **Observation 4: proof treats only pairs outside `G`.** The proof replaces an MST edge `e ∈ M_G \ G`
  by a shortest path with at least two edges. An edge of `G` heavier than the distance between its
  endpoints needs the same treatment, and the argument works for it verbatim. Theorem 6 does not need
  Observation 4: all edges of a greedy spanner of a metric are shortest paths. We prove the equality
  `w(MST(M_H)) = w(MST(M))` directly (`mstWeight_inducedW`).
* **Loose definitions (harmless).** `OPT_t(𝒢)` is defined as a *maximum* over `𝒢`. For lightness
  over an infinite family of weighted graphs the maximum need not be attained; we use the supremum.
  Section 2 assumes all graphs connected, but a family closed under edge removal contains
  disconnected graphs. We define the MST weight as the weight of a minimum spanning *forest*. For
  connected graphs it is the minimum weight of a spanning tree (`mstWeight_eq_iInf_isTree`).
* **Unneeded hypotheses.** Lemma 3 and Observation 2 hold for every stretch `t` (the paper assumes
  `t ≥ 1`) and for non-negative weights (the paper assumes positive weights).
* **Typo.** In the proof of Observation 7, the covering balls in `M` should have radius `r/4`, not `4r`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The setting is sequential and centralized: Section 3 is pure graph theory, with no distributed model.
* A weighted graph is a CSLib `SimpleGraph V` on a finite vertex type (`n = |V|`) with weights
  `w : Sym2 V → ℝ≥0`. Distances are CSLib's `wdist`, in `ℝ≥0∞`, equal to `⊤` when disconnected.
  The stretch `t` is a real number `t ≥ 1`.
* `IsWSpanner G H w t`: `H ≤ G` and `δ_H(u,v) ≤ t·δ_G(u,v)` for all `u, v`.
* **Algorithm 1** is modelled literally (`greedy w t L`). It scans an edge list `L` and adds
  `e = {u,v}` iff `δ_H(u,v) > t·w(e)` for the current `H`. "The greedy `t`-spanner"
  (`IsGreedySpanner`) is the output of *any* execution: `L` lists every edge exactly once, in
  non-decreasing order of weight, with ties broken arbitrarily. Every result holds for every
  execution.
* Lightness is `Ψ(H) = w(H)/w(MST(G))` in `ℝ≥0∞`. `w(MST(G))` (`mstWeight`) is the minimum weight of a
  subgraph with the same connected components as `G`, i.e. a minimum spanning forest.
* A graph family is a set `𝒢` of weighted graphs on `V`. "Closed under edge removal" means
  `(G,w) ∈ 𝒢`, `H ≤ G` ⇒ `(H,w) ∈ 𝒢`.
* A metric is a weight function on the complete graph `⊤`: zero on the diagonal, positive off it,
  triangle inequality. `M_H` is the complete graph with weights `δ_H`. `IsDoubling w D` means
  every closed ball of radius `r` is covered by `≤ 2^D` balls of radius `r/2`. `M(n, D)` is
  `metricFamily V D`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 1 outputs a `t`-spanner; local criterion (§2) | `IsGreedySpanner.isWSpanner`, `isWSpanner_of_adj` | `Basic.lean` |
| Observation 2 (greedy contains an MST of `G`) | `IsGreedySpanner.exists_mst_le`, `IsGreedySpanner.mstWeight_eq` | `MST.lean` |
| Lemma 3 (the only `t`-spanner of `H` is `H`) | `lemma3` | `Lemma3.lean` |
| Theorem 5 (existential optimality, size and lightness) | `theorem5` | `Theorem5.lean` |
| Existential optimality as an equality (§1.3 definition) | `existentially_optimal_sparse`, `existentially_optimal_light` | `Theorem5.lean` |
| Corollary 1, size: `t ≥ 2k−1` ⇒ girth `> 2k`, `≤ n^{1+1/k}+n` edges | `IsGreedySpanner.noShortCycles`, `corollary1_size` | `Theorem5.lean` |
| Corollaries 1 (lightness) and 2, given the cited bounds | `greedy_le_of_forall_exists` | `Theorem5.lean` |
| Lemma 5 (`w(H) ≤ w(H')` for `H'` a `t`-spanner of `M_H`) | `lemma5` | `Section4.lean` |
| Lemma 6 (`|H| ≤ |H'|`, `t < 2`) | `lemma6` | `Section4.lean` |
| Observation 7 (`M_H ∈ M(n, 2 ddim)` for `t ≤ 2`) | `observation7` | `Doubling.lean` |
| Observations 2 + 4 as used in Thm 6 (`M`, `M_H` have equal MST weight) | `mstWeight_inducedW` | `Doubling.lean` |
| Theorem 6 (near-optimality in doubling metrics) | `theorem6` | `Doubling.lean` |
| Corollary 3, given Theorem 4 [Got15] | `corollary3_of_forall_exists` | `Doubling.lean` |
| (sanity) `mstWeight` = minimum spanning tree weight | `mstWeight_eq_iInf_isTree` | `MSTTree.lean` |

Lemmas 5 and 6 are proved for an arbitrary connected weighted graph `G`, not only for metrics. Lemma 6
additionally needs positive edge weights and `1 ≤ t < 2`.

**Not formalized.** The cited Theorems 1–4 and Lemma 1 are used only as hypotheses, in
Corollaries 1–3. For Corollaries 1 and 2 the hypothesis is stated for all weighted graphs on `V`,
including disconnected ones; this follows from the cited bounds by applying them per component.
Section 5 is not formalized: the approximate-greedy algorithm, Lemmas 8 and 10,
Observation 9 and Theorem 7. Its claims are about running time in the algebraic computation-tree
model and rest on cited geometric lemmas. The illustrative Petersen-graph example of Figure 1 is
also not formalized.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: every weighted graph has a greedy `t`-spanner (`exists_isGreedySpanner`).
The hypotheses of Theorem 6 are met by the uniform metric, which has doubling dimension
`≤ log₂ n` (`isDoubling_logb_card`, and the `example` at the end of `Doubling.lean`). Distances and
weighted walks come from CSLib (`WeightedSpanner.lean`, `ShortestWalks.lean`). The Moore bound and
the cycle-splitting lemma also come from CSLib (`Girth.lean`, `Cycle.lean`).

CSLib candidates (marked `-- CSLib candidate`): weighted spanners with real stretch, the local criterion,
attainment of weighted distances by paths (`exists_isPath_wlength_eq`), the greedy scan and Lemma 3,
`mstWeight` with the exchange lemma `mstWeight_eq_of_forall_walk` and `mstWeight_eq_iInf_isTree`,
two-weight distance comparison, finite metrics and doubling dimension.
