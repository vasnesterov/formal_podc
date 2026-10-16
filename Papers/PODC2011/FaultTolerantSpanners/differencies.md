# Differences between the formalization and the paper

Dinitz–Krauthgamer, *Fault-Tolerant Spanners: Better and Simpler*, PODC 2011 (arXiv 1101.5753 v1).
Classification: **false statement** / **degenerate case** / **proof gap (statement true)** /
**under-specified** / **typo** / **modelling choice**.

## Section 2 (general stretch `k`)

1. **Theorem 2.1, `f` monotone** — *proof gap (statement true)*. The proof bounds the size of the
   spanner of `G \ J` (with `≤ 2n/r` vertices) by `f(2n/r)`, which needs `f` nondecreasing. The
   theorem itself does not need it (pad `G \ J` with isolated vertices to `⌊2n/r⌋` vertices; the base
   algorithm works on every graph), but our `SpannerAlg` model only runs on induced subgraphs. We assume
   `Monotone f`.
2. **Theorem 2.1 for `r > 2n`** — *degenerate case (false)*. The claimed size `O(r³ log n f(2n/r))`
   involves `f` at an argument `< 1`, where `f = 0` is legitimate, while any `r`-FT spanner of a graph
   with an edge is nonempty. We assume `1 ≤ r ≤ n` and `f 2 ≥ 1` (true for any algorithm that works
   on a single edge). For `r = 1` the paper uses `p = 1/2`; we do the same (`m = max r 2`).
3. **Theorem 2.1, "with high probability"** — *under-specified / made explicit*. We prove
   `Pr[r-FT k-spanner ∧ |E(H)| ≤ (8C+26) r³ ln(n+1) f(⌊2n/r⌋)] ≥ 1 − (n+1)^{−C} − α e^{−n^{1/3}/6}`
   with `α = ⌈8 r² (r+2+C) ln(n+1)⌉` (`theorem_2_1`), and the fully explicit version for any `m, α`
   (`conversion_explicit`):
   `≥ 1 − (n+1)^r n² (1 − (1/m)²(1−1/m)^r)^α − α e^{−n/(3m)}`.
   The second error term is the paper's Chernoff/union bound for the size; as in the paper it is
   only used when `r³ < n²` (otherwise the size bound is deterministic). We do not formalize that
   it is `n^{−ω(1)}` (elementary).
4. **Constants.** Per-iteration success probability: we prove `(1/m)²(1−1/m)^r ≥ 1/(8r²)` (`q_ge`);
   the paper states `≥ 1/(4r²)` for `r ≥ 2` (true, since `(1−1/r)^r ≥ 1/4`, but not needed).
   Number of fault sets of size `≤ r`: we use `≤ (n+1)^r` (`card_faultSets_le`). Chernoff: `Pr[#
   survivors > 2n/m] ≤ e^{−n/(3m)}` proved by the exponential-moment method on a finite space
   (`uprob_card_surv_gt_two_mul`), matching the paper's `e^{−(1/3) n/r}`.
5. **Tight edges `E′_F`** — *simplification*. The paper restricts the union bound to edges that are
   shortest paths in `G \ F`; we union-bound over all edges of `G \ F` (the per-edge argument works
   for every edge because `d_{G[S]}(u,v) ≤ ℓ(uv)`), using CSLib's local criterion
   `isWeightedVFTSpanner_of_adj`. Same bound up to the count of edges (`≤ n²`).
6. **Typos in the proof of Theorem 2.1.** "a path of length at most `k·d_{G\F}(u,v)` between `u` and
   `v` in `G \ F`" should be "in `H \ F`"; `k·ℓ({u,e})` should be `k·ℓ({u,v})`; the set defined as
   `E_F = {… d_{G\F}(u,v) = ℓ}` is `E′_F`; "`α = O(r³ log n) ≤ O(e³ ln n log n)`" is garbled
   (should be `O(n² log n)` using `r ≤ n^{2/3}`).
7. **Model of the spanner algorithm** — *modelling choice*. `SpannerAlg G w k f` gives, for every
   `S ⊆ V`, a subgraph of `G[S]` (`G.deleteVerts Sᶜ`) with stretch `k` for `u, v ∈ S` and `≤ f(|S|)`
   edges. The paper assumes an algorithm correct "on every graph"; ours only needs the induced
   subgraphs of the input graph (weaker hypothesis). Deterministic algorithm, as in the paper's
   simplifying assumption. Running time is not modelled.
8. **Randomness** — *modelling choice*. `Pr[v ∈ J] = 1 − 1/m` is realised exactly by a uniform
   label in `Fin m` (survive iff label `0`), independently over vertices and iterations; probabilities
   are counting ratios on `Fin α → V → Fin m` (`uprob`).
9. **Edge lengths** — Theorem 1.1 says positive lengths and odd `k ≥ 3`, Corollary 2.2 says
   nonnegative lengths and odd `k ≥ 1`. We allow nonnegative weights `ℝ≥0` and all `k = 2t − 1`,
   `t ≥ 1`.
10. **Corollary 2.2** — the cited fact [ADD+93] (greedy `(2t−1)`-spanner with `O(n^{1+1/t})` edges) is
    proved: existence of a `(2t−1)`-spanner of girth `> 2t` by the greedy induction
    (`exists_greedy_spanner`, an existence statement; the algorithm is not run) plus CSLib's Moore
    bound relative to a vertex set (`|E| ≤ |S|^{1+1/t} + |S|`). Final explicit bound:
    `6(8C+26) r^{2−1/t} n^{1+1/t} ln(n+1)` (`corollary_2_2`), i.e. `O(r^{2−2/(k+1)} n^{1+2/(k+1)} log n)`.
11. **Theorem 2.3 / Corollary 2.4 (distributed)** — not formalized (round counting around a black-box
    distributed spanner [DGPV08]).

## Section 3 (`k = 2`, unit lengths, directed, costs)

12. **Model** — directed graph as `E : Finset (V × V)`; `IsFTSpanner E H r k`: `H ⊆ E` and for all
    `|F| ≤ r`, `u, v ∉ F`, every walk of length `n` in `E \ F` is matched by a walk of length `≤ kn`
    in `H \ F` (= `d_{H\F} ≤ k·d_{G\F}` with unit lengths, `∞ ≤ k·∞`). Costs `c ≥ 0`.
13. **Lemma 3.1** — *degenerate case*: the "only if" direction needs `E` loopless (with a loop
    `(u,u) ∈ E`, `H = ∅` is an `r`-FT 2-spanner not satisfying `(u,u)`). *Proof slip*: "in `H \ W`
    there is no `u − v` path" should be "no `u − v` path of length `≤ 2`" (which is what is needed).
    (`isFTSpanner_two_iff`)
14. **IP (3) exact; knapsack-cover inequalities valid** — proved (`isFTSpanner_iff_exists_ip3`,
    `IsIP3Feasible.toLP4`, `IsIP3Feasible.isFTSpanner`, `exists_lp4_of_isFTSpanner`). Needs `E`
    loopless (otherwise an arc can lie on two paths of `P_{u,v}` and the capacity constraint fails for
    the indicator flow). The paper's "obvious" `f_P ≤ 1` follows from the capacity constraints.
15. **LP (4)** — capacity constraints are stated literally as sums over the paths of `P_{u,v}`
    through `e`; per-path consequences `f_{(u,z,v)} ≤ x_{(u,z)}, x_{(z,v)}` are derived
    (`IsLP4Feasible.flow_le_left/right`).
16. **Lemma 3.2** — only the combinatorial core is formalized: the knapsack-cover constraint for a
    fixed size `|W| = j` is hardest for the `j` largest flows, so it suffices to check those
    (`sum_sdiff_le_of_top`, `exists_top_subset`, `knapsack_iff_top`). The Ellipsoid method /
    polynomial-time solvability is not modelled.
17. **Integrality gap example (§3.2)** — formalized for every `r ≥ 1`, `M ≥ 0` (`GapExample`): OPT ≥
    `M`, the relaxation of IP (3) has value `M/(r+1) + 2r`, and LP (4) forces `x_{uv} = 1`. The §3.1
    gap example for LP (2) (complete graph) is not formalized.
18. **Theorem 3.3** — the analysis is formalized with explicit constants:
    per-arc failure `≤ e^{−α/4}` for `α ≥ 4` (`prob_not_satisfies_le`), `E[cost] ≤ 2α·LP`
    (`expected_cost_le`), `Pr[cost > 6α·LP] ≤ 1/3` (`prob_cost_gt_le`), total success
    `≥ 2/3 − |E| e^{−α/4}` (`rounding_success`); with `α = 12 ln n`: success `≥ 2/3 − 1/n`, cost
    `≤ 72 ln n · LP` (`rounding_success_log`), and combined with Lemma 3.1 and LP ≤ OPT in
    `theorem_3_3`, `theorem_3_3'`. Remarks:
    * *under-specified*: `i* = max{i : f_{P_i} ≥ 1/α}` is undefined if no path has flow `≥ 1/α`
      (convention `i* = 0`); we avoid sorting and use the set `{z : α f_z ≥ 1}`;
    * *implicit conditions*: "`x_{uv} ≥ 1/2` ⇒ `(u,v)` selected" needs `α ≥ 2`; "`i* + αr′/4 ≥ r+1`"
      needs `α ≥ 4` (both hidden in "C large enough");
    * *typo*: "`T_z ≤ min{x_{(u,z)}, x_{(z,v)}}`" should be `α·min{…}`;
    * equation (5) is made explicit: `Pr[Σ I_P ≤ r′ − 1] ≤ 2^{r′−1} e^{−αr′/4} ≤ e^{−α/4}` via the
      exponential moment `E[2^{−X}] = ∏(1 − a_z/2)` (`chernoff_count`);
    * "with probability 1" means almost surely (`T ∈ [0,1]` a.s.); the Markov step needs `c ≥ 0` and
      a separate argument when the LP value is 0.
    * The approximation statement is relative to any LP-feasible solution whose value is `≤` the cost
      of a given spanner `H⋆` (an LP optimum, whose existence is not formalized, satisfies this for an
      optimal `H⋆`).
19. **Theorem 3.4 (`O(log Δ)` via the Lovász Local Lemma)** — not formalized (no LLL in Mathlib).
    Remarks from reading: `Z_u^−` should use `x_{v,u}` (*typo*); `A_{u,v}` also depends on `T_v`
    (not only on `T_z`, `z ∈ (N⁺(u) ∩ N⁻(v)) ∪ {u}`), which does not affect the `O(Δ³)` dependency
    degree (*slip*); the introduction calls this result non-algorithmic while Section 3.4 makes it
    algorithmic via Moser–Tardos (*inconsistency*).
20. **Lemma 3.8** — **false statement** as written. `LP(C)` gives cost 0 only to the arcs of `δ(C)`;
    arcs of `G(C)` with both endpoints in `N(C)` keep their cost, and the proof never assigns them a
    value (it sets `x^C` on `E(C) ∪ δ(C)` and zero flow elsewhere). Counterexample (`r = 0`, vertices
    `a, b, c, d`, arcs `c→a, c→b, a→d, d→b` of cost 1 and `a→b` of cost `M > 4`, partition
    `{{c},{a,b,d}}`): `LP* ≤ 4`, but every feasible solution of `LP({c})` has value `≥ M`
    (`Lemma38Counterexample.lemma_3_8_counterexample`). With cost 0 on all arcs of `G(C)` outside
    `E(C)` — consistent with the wording of the proof of Theorem 3.9, whose cost argument works
    with any such repair — the lemma holds
    (`lemma_3_8_corrected`; our construction copies all flows instead of zeroing them, both work).
21. **Lemma 3.7, Theorem 3.9, Algorithm 2 (distributed)** — not formalized (padded decompositions,
    LOCAL-model round counts, Chernoff over iterations). With the corrected `LP(C)` the cost argument
    of Theorem 3.9 matches Lemma 3.8.
