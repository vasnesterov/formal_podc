# Fault-Tolerant Spanners: Better and Simpler — PODC 2011

Michael Dinitz, Robert Krauthgamer. *Fault-Tolerant Spanners: Better and Simpler.* PODC 2011. DOI
[10.1145/1993806.1993830](https://doi.org/10.1145/1993806.1993830). Formalized version: arXiv
[1101.5753](https://arxiv.org/abs/1101.5753) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main results hold, with explicit constants:
* the generic conversion (Theorem 2.1) and its greedy instance (Corollary 2.2);
* Lemma 3.1, the LP relaxation with knapsack-cover inequalities (validity, LP ≤ OPT, the integrality
  gap example);
* the `O(log n)` rounding of Theorem 3.3.

Lemma 3.8, a step of the distributed algorithm (Section 3.5), is false as stated. It holds once the
cluster LP is redefined in the way the later proof of Theorem 3.9 actually uses.

## Mistakes in the paper

* **Lemma 3.8 is false as stated (Section 3.5).** `LP(C)` is LP (4) on `G(C)`, the subgraph induced
  by `C ∪ N(C)`, where *only the arcs of `δ(C)`* get cost 0. Arcs with both endpoints in `N(C)`
  keep their cost, and inside `G(C)` they may have no cheap length-2 bypass. The proof ignores these
  arcs: it sets `x^C` only on `E(C) ∪ δ(C)` and zeroes all other flows.

  Counterexample with `r = 0`:
  * vertices `a, b, c, d`;
  * arcs `c→a`, `c→b`, `a→d`, `d→b` of cost 1, and `a→b` of cost `M > 4`;
  * partition `{{c}, {a, b, d}}`.

  LP (4) for `G` has a solution of value 4 (route `a→b` via `d`). `G({c})` is induced by `{c, a, b}`
  and contains no length-2 path from `a` to `b`, so `LP({c}) ≥ M > 4 ≥ LP*`.

  Severity: a false statement caused by a misdefined `LP(C)`; the intended lemma is true and
  Theorem 3.9 / Theorem 1.3 are unaffected (their cost argument only needs
  `∑_{e∈E(C)} c_e x^C_e ≤ LP*(C)`, true for any nonnegative costs). One repair is to give cost 0 to
  *all* arcs of `G(C)` outside `E(C)`, matching the phrase "the rounds in which the edge `e` does not
  have cost 0" in the proof of Theorem 3.9; dropping the covering constraints of arcs outside
  `E(C)` would also work. With the first repair Lemma 3.8 holds, and we prove it.
  (`Lemma38Counterexample.lemma_3_8_counterexample`, `lemma_3_8_corrected`)
* **Theorem 2.1: implicit `f` monotone, and a degenerate case `r > 2n`.**
  * The proof bounds the size of the spanner on `G \ J` (at most `2n/r` vertices) by `f(2n/r)`,
    which needs `f` nondecreasing. This is a proof gap with a true statement: since the base
    algorithm works on every graph, one can pad `G \ J` with isolated vertices up to `⌊2n/r⌋`
    vertices. Our `SpannerAlg` only runs on induced subgraphs of `G`, so we assume `Monotone f`.
  * For `r > 2n` the claimed size `O(r³ log n · f(2n/r))` can be 0, because `f(0) = f(1) = 0` is
    legitimate. Yet any fault-tolerant spanner of a graph with an edge is nonempty.
  * We assume `1 ≤ r ≤ n`, `f` monotone and `f(2) ≥ 1`. The last condition holds for any algorithm
    that is correct on a single edge.
  * We prove the theorem with explicit constants: `α = ⌈8r²(r+2+C) ln(n+1)⌉` iterations and size
    `≤ (8C+26) r³ ln(n+1) f(⌊2n/r⌋)`.
  * The success probability is `≥ 1 − (n+1)^{−C} − α e^{−n^{1/3}/6}`. The last term is the paper's
    Chernoff bound on the number of survivors under its "w.l.o.g. `r ≤ n^{2/3}`".

  (`theorem_2_1`)
* **Lemma 3.1 and the exactness of IP (3) need a loopless digraph. Degenerate case.** With a
  self-loop `(u,u) ∈ E`, `H = ∅` is a fault-tolerant 2-spanner that does not "satisfy" `(u,u)`. The
  proof also has a slip: "in `H \ W` there is no `u–v` path" should read "no `u–v` path of length
  `≤ 2`". The weaker claim is the true one, and it suffices. (`isFTSpanner_two_iff`)
* **Theorem 3.3: implicit conditions, all fine.**
  * `i* = max{i : f_{P_i} ≥ 1/α}` is undefined when no path has flow `≥ 1/α`; we take `i* = 0`.
  * The steps "`x_uv ≥ 1/2` ⇒ selected" and "`i* + αr′/4 ≥ r+1`" need `α ≥ 2` and `α ≥ 4`.
  * "With probability 1" means almost surely.
  * We prove: per-arc failure `≤ e^{−α/4}` for `α ≥ 4`, expected cost `≤ 2α·LP`, and with
    `α = 12 ln n` success probability `≥ 2/3 − 1/n` for cost `≤ 72 ln n · LP`.

  (`prob_not_satisfies_le`, `theorem_3_3`)
* **Typos and small slips.**
  * Section 2: the sufficiency claim needs "a path … in `H \ F`", not "in `G \ F`".
  * Section 2: `ℓ({u,e})` should be `ℓ({u,v})`, and the set defined is `E′_F`, not `E_F`.
  * Section 2: the iteration count is garbled as "`O(e³ ln n log n)`".
  * Theorem 3.3: "`T_z ≤ min{x_(u,z), x_(z,v)}`" is missing the factor `α`.
  * Theorem 3.4, not formalized: `Z_u^−` uses `x_{u,v}` where `x_{v,u}` is meant.
  * Theorem 3.4: `A_{u,v}` also depends on `T_v`, which does not change the `O(Δ³)` dependency count.
  * The introduction calls the `O(log Δ)` bound non-algorithmic, while Section 3.4 makes it
    algorithmic via Moser–Tardos.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Section 2.** Finite simple graph with nonnegative weights `w : Sym2 V → ℝ≥0` and vertex faults.
  * We use CSLib's `IsWeightedVFTSpanner`: for every `|F| ≤ r` and all `u, v ∉ F`,
    `d_{H\F}(u,v) ≤ k·d_{G\F}(u,v)`, where `G \ F` keeps the vertices and deletes their edges.
  * The underlying `k`-spanner algorithm (`SpannerAlg`) is given by its outputs on the induced
    subgraphs `G[S]`, the only inputs the conversion uses. Each output is a subgraph of `G[S]` with
    stretch `k` on `S` and at most `f(|S|)` edges.
  * Randomness is exact and finite. In each of the `α` iterations every vertex draws a uniform label
    in `Fin m` and survives iff the label is 0, so `Pr[v ∈ J] = 1 − 1/m`. We take `m = r`, or
    `m = 2` when `r = 1`, as in the paper.
  * Probabilities are counting ratios over `Fin α → V → Fin m`; no measure theory is involved.
  * The bound of `theorem_2_1` is asymptotic, like the paper's: its term `α e^{−n^{1/3}/6}` (from
    the paper's `r ≤ n^{2/3}` step) exceeds 1 unless `n` is large (`n > 10^4` is not enough even for
    `r = C = 1`). `conversion_explicit`, with the term `α e^{−n/(3m)}`, is the sharper finite statement.
* **Section 3.** Directed graph `E : Finset (V × V)`, unit lengths, arc costs `c ≥ 0`.
  * `IsFTSpanner E H r k` is stated with directed walks avoiding `F`.
  * LP (4) is written literally: capacity sums, all knapsack-cover constraints, `0 ≤ x ≤ 1`, `f ≥ 0`.
  * The thresholds of Algorithm 1 are i.i.d. uniform on `[0,1]` (product of Lebesgue measures on
    `[0,1]`).
  * Theorem 3.3 is stated for any LP-feasible solution whose value is at most the cost of a given
    spanner `H⋆` (e.g. an LP optimum and an optimal spanner). Solving the LP (Ellipsoid,
    Lemma 3.2) and running times are not modelled.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 2.1 (explicit) | `conversion_explicit` | `Conversion.lean` |
| Thm 2.1 (paper's parameters) | `theorem_2_1` | `Theorem21.lean` |
| Thm 2.1 proof: correctness core / good-iteration probability | `isWeightedVFTSpanner_ftUnion`, `uprob_good`, `uprob_not_isVFT_le` | `Conversion.lean` |
| Thm 2.1 proof: Chernoff bound on survivors | `uprob_card_surv_gt_two_mul` | `Sampling.lean` |
| [ADD+93] greedy spanner (cited) + Moore bound on `S` | `exists_greedy_spanner`, `SimpleGraph.NoShortCycles.ncard_edgeSet_le_card_rpow` | `Corollary22.lean`, `Cslib/Foundations/Combinatorics/SimpleGraph/Girth.lean` |
| Cor 2.2 (`≤ 6(8C+26) r^{2−1/t} n^{1+1/t} ln(n+1)`, `k = 2t−1`) | `corollary_2_2` | `Corollary22.lean` |
| Lemma 3.1 | `isFTSpanner_two_iff` | `TwoSpanner/Characterization.lean` |
| IP (3) exact, KC inequalities valid, LP ≤ OPT | `isFTSpanner_iff_exists_ip3`, `IsIP3Feasible.toLP4`, `exists_lp4_of_isFTSpanner` | `TwoSpanner/Characterization.lean` |
| Lemma 3.2 (hardest KC constraint = top flows) | `sum_sdiff_le_of_top`, `knapsack_iff_top` | `TwoSpanner/Characterization.lean` |
| Integrality gap example of §3.2 | `GapExample.*` | `TwoSpanner/Characterization.lean` |
| Thm 3.3 analysis (per arc, cost, total) | `prob_not_satisfies_le`, `expected_cost_le`, `rounding_success` | `TwoSpanner/Rounding.lean` |
| Thm 3.3 | `theorem_3_3`, `theorem_3_3'` | `TwoSpanner/Theorem33.lean` |
| Lemma 3.8 false / corrected | `Lemma38Counterexample.lemma_3_8_counterexample`, `lemma_3_8_corrected` | `TwoSpanner/Distributed.lean` |

**Not formalized.**
* Theorem 3.4 (`O(log Δ)`): it needs the Lovász Local Lemma (Moser–Tardos), which Mathlib lacks.
* The distributed results: Theorem 2.3, Corollary 2.4, Lemma 3.7 (padded decompositions) and
  Theorem 3.9 (round counts, Chernoff over iterations). Only Lemma 3.8 is formalized.
* Running times, Lemma 3.2's Ellipsoid algorithm, and the integrality-gap example of LP (2) in §3.1.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`.
* Section 2 builds on CSLib's `WeightedSpanner` and `Girth` (Moore bound), and on the shared
  `Podc` libraries: the greedy spanner (`Cslib/Foundations/Combinatorics/SimpleGraph/GreedySpanner.lean`, also used by
  [Filtser–Solomon](../../PODC2016/GreedySpanner)), the relative Moore bound
  (`Cslib/Foundations/Combinatorics/SimpleGraph/Girth.lean`) and finite uniform probability `uprob`
  (`Cslib/Probability/Finite/Uniform.lean`, whose counting Chernoff bound gives the survivor bound).
* Non-vacuity, Section 2: the greedy spanner (`greedyAlg`) satisfies all hypotheses of Theorem 2.1,
  which yields Corollary 2.2.
* Non-vacuity, Section 3: every fault-tolerant spanner gives an LP-feasible solution
  (`theorem_3_3'`), so Theorem 3.3's hypotheses are satisfiable.
* CSLib candidate: the multiplicative Chernoff lower tail for independent threshold indicators
  `chernoff_count` (`TwoSpanner/Rounding.lean`, measure-theoretic).
