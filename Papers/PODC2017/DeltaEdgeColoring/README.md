# (Δ + o(Δ))-Edge-Coloring and Clique Decompositions — PODC 2017

Leonid Barenboim, Michael Elkin, Tzalik Maimon. *Deterministic Distributed (Δ + o(Δ))-Edge-Coloring, and
Vertex-Coloring of Graphs with Bounded Diversity.* PODC 2017. DOI
[10.1145/3087801.3087812](https://doi.org/10.1145/3087801.3087812). Formalized version: arXiv
[1610.06759](https://arxiv.org/abs/1610.06759) v1 (full version with appendix); numbering follows it.

**Verdict: 🛠️ Proof repaired.** The combinatorial correctness of the clique-decomposition colouring
(Lemmas 2.1–2.3, Theorems 2.4–2.6), its colour count `D^{x+1} S` (Theorem 3.2), Lemma 5.1, Theorem 5.2
(`Δ + O(a)` colours) and Theorem 5.3 (`Δ + o(Δ)` colours when `a = o(Δ)`) all hold. The appendix proof of
the `D^{x+1} S` bound of Theorem 3.2 does not work as written: its inductive step does not cover the
first recursion step (`𝒜_2`), and with the parameter it states for that step the inequality is false.
We prove the bound with a stronger invariant. It then holds for every `S ≥ 1` and needs no colour
reduction.

## Mistakes in the paper

* **Theorem 3.2's colour bound: the inductive step is wrong for `𝒜_2`; the statement is true.** The proof
  builds `𝒜_{i+1}` from `𝒜_i` with `t = ⌊S^{1/(i+1)}⌋`. It uses only the induction hypothesis
  "`𝒜_i` uses `D^{i+1} S'` colours". Then it claims `(D(t−1)+1)·D^{i+1}⌈S/t⌉ ≤ D^{i+2} S` "for `S` larger
  than some constant, since `(D−1)(S/t) > Dt` because `t = ⌊S^{1/(i+1)}⌋` and `i ≥ 2`". But `𝒜_2` is the
  case `i = 1`. There `t = ⌊√S⌋`, and the inequality fails for arbitrarily large `S`. For example,
  `D = 2`, `S = 31`, `t = 5` gives `9·4·7 = 252 > 248 = 8·31` (`paper_inductive_step_fails`).
  In the running-time part the proof uses a different parameter, `t = ⌊S^{1/(i+2)}⌋`. With that choice
  the step works for `S` above a constant (constant `S` is covered by §3's direct `D(S−1)+1`-colouring), so
  the gap is repairable from the paper itself, but the proof as written does not establish `𝒜_2`. The
  bound itself is true for the actual algorithm. For `D ≥ 2`, the invariant `pal_j · (D·S_j − 1) ≤ D^j (D S − 1)` holds whenever every level
  uses some `t` with `t² ≤ S_cur`. Here `pal_j` is the number of subgraphs after `j` levels and `S_j`
  the current clique bound. So `𝒜_x` uses fewer than `D^{x+1}S` colours, for all `S ≥ 1`, with either
  choice of `t` and with no colour-reduction rounds (`theorem_3_2`, `theorem_3_2_algA`).
* **Theorem 3.2, base case `𝒜_1`: correct, but not tight, and only for `D ≥ 2`.** The chain of inequalities
  is valid (the `+(D−1)²` term is absorbed by the `−1` in `2⌊√S⌋ − 1`, since `t + k ≥ 2⌊√S⌋` and
  `D(D−1) ≥ (D−1)²`). The 2 colour-reduction rounds are unnecessary: the count is already
  `≤ D(DS − 1) < D²S` (the case `x = 1` of `theorem_3_2`). The proof assumes `D ≥ 2`, the statement does
  not. For `D = 1`, `𝒜_1` produces up to `⌊√S⌋⌈S/⌊√S⌋⌉` colours, e.g. 6 > 5 for `S = 5`, so the `S` colours
  of the statement need more colour reduction. This case is degenerate (the graph is a disjoint union of
  cliques).
* **Minor imprecisions.**
  - The (p,q)-clique-decomposition is defined with clique size "is `q`"; "at most `q`" is meant.
  - The proof of Lemma 2.3 (i) speaks of "a clique `Q` of `G'`" where a clique of `G_i` is meant.
  - Theorem 2.4's `S/t^x + 2` can be sharpened to `⌈S/t^x⌉ ≤ S/t^x + 1`.
  - Algorithm 1 passes `⌈S/t⌉` as the next `S`, and the nested ceilings equal `⌈S/t^x⌉`.
  - §4: `(2t−1)(2k−1) ≤ 4Δ` already holds for `t = ⌊√Δ⌋`, so the extra reduction round is unnecessary
    (`theorem_4_1_count_one`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic synchronous message passing (LOCAL) with unique IDs (`LinearOrder V`), finite simple
  graphs. We verify the *combinatorial correctness* of the algorithms: properness, decomposition
  properties, colour counts, the round schedule, and the consistency of parallel choices. Running-time
  claims of the `Õ(·)` form are not formalized.
* The subroutines are black boxes given by their output specifications:
  - the `(Δ+1)`-vertex colouring of [17] is `IsDeltaColorer`. Non-vacuity: identifiers followed by CSLib's
    standard colour reduction, `isDeltaColorer_reductionColorer`;
  - the H-partition of [4] is `IsHPartition`. It is instantiated with the peeling algorithm formalized in
    `Papers/PODC2010/ArbdefectiveColoring/HPartition.lean`: degree `3a` (`ε = 1`) and `L = 2(⌊log₂ n⌋+1)` sets
    (`exists_hPartition`);
  - the edge colourings of the H-sets (via [17] or §4) are given as any proper colouring with `k₀` colours.
    Greedy `2d − 1` colours: `exists_hSet_coloring`.
* Clique identification: `IsCliqueCover G 𝒬 D S`. It is a family of cliques covering every edge, with every
  vertex in at most `D` members and every member of size at most `S`. This covers both the paper's
  "consistent identification" (e.g. stars of a line graph) and all maximal cliques (`maximalCliques`,
  `diversity`). The bound "every clique of `G[U_i]` has size `≤ q`" is proved when `𝒬` contains every
  clique (`CoversCliques`, true for maximal cliques).
* Algorithm 1 is unrolled level by level (`stages`). The parallel recursive calls on the colour classes `G_i`
  form one call on their disjoint union `sameColor G φ`. The output pair `⟨φ, ψ⟩` is encoded as `φ·B + ψ`.
  "Uses `N` colours" means all colours are `< N`.
* The round-by-round procedures of Lemma 5.1 and Theorem 5.2 are formalized as a schedule (`EdgeSchedule`).
  Edges inside `A`/`B`, resp. inside the H-sets, are pre-coloured. The crossing edge `ab` (`h a < h b`) is
  coloured in round `(ℓ−1−h a)·d + lab a b` by `b`. A *run* is any colouring obeying the local rule
  (`EdgeSchedule.Follows`), so we quantify over all of the paper's "any assignment of distinct available
  colours". Every run is proper, runs exist, and two adjacent edges coloured in the same round are chosen
  by their common endpoint.
* Theorem 5.3's Lean conclusion is existential ("some proper edge colouring with `N` colours", which alone
  would also follow from Vizing). The algorithm is captured by the colouring the proof builds
  (`⟨φ, ψ⟩` from runs of Theorem 5.2) and by `theorem_5_3_combine`, which holds for *every* such `φ`, `ψ`.
* Orientation connector (§5): the acyclic orientation is a rank `r`. Incoming/outgoing edges are grouped by
  ID into groups of `sIn`/`sOut`, with virtual vertices `V × Fin (m+1)`. The paper's `k = ⌈√Δ⌉` groups of
  size `⌈Δ/k⌉` become groups of size `⌊√Δ⌋+1`, and similarly for `√d`. Asymptotically this is the same.

**Main results in Lean.** All in namespace `Podc.DeltaEdgeColoring`.

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 | `connector_degree_le` | `Basic.lean` |
| Lemma 2.2 | `lemma_2_2` | `Basic.lean` |
| Lemma 2.3 (i) / (ii) | `lemma_2_3_i`, `isCliqueCover_refine` / `diversity_sameColor_le` | `Basic.lean` |
| Theorem 2.4 | `theorem_2_4` | `CliqueDecomposition.lean` |
| Theorem 2.5 | `theorem_2_5` | `CliqueDecomposition.lean` |
| Theorem 2.6 | `theorem_2_6` | `CliqueDecomposition.lean` |
| Theorem 3.2 (colours) | `theorem_3_2`, `theorem_3_2_algA` | `CliqueDecomposition.lean` |
| Proof of Thm 3.2: failing step | `paper_inductive_step_fails` | `CliqueDecomposition.lean` |
| Theorem 4.1 (colour arithmetic only) | `theorem_4_1_count`, `theorem_4_1_count_one` | `Section4Count.lean` |
| Lemma 5.1 | `lemma_5_1`, `lemma_5_1_rounds`, `lemma_5_1_parallel` | `Section5.lean` |
| Theorem 5.2 | `theorem_5_2`, `theorem_5_2_colors`, `theorem_5_2_rounds`, `theorem_5_2_parallel` | `Section5.lean` |
| Theorem 5.2 (`Δ+6a` colours, `3a·2(⌊log₂n⌋+1)` rounds) | `theorem_5_2_arboricity` | `Theorem52Arboricity.lean` |
| Theorem 5.3 (connector, classes, combination) | `oconn_degree_le`, `oconn_hasOutDegLE`, `classGraph_degree_le`, `classGraph_hasOutDegLE`, `theorem_5_3_combine` | `Theorem53.lean` |
| Theorem 5.3 (colours) | `theorem_5_3_count`, `theorem_5_3`, `theorem_5_3_arboricity`, `theorem_5_3_asymptotic` | `Theorem53.lean` |

Supporting files:
* `EdgeSchedule.lean`: the generic round-scheduled greedy edge colouring (`Follows.isProperEdgeColoring`,
  `exists_follows`). CSLib candidate.
* `NonVacuity.lean`: the black-box colourer instance and a non-vacuity example of Theorem 2.5.

**Not formalized.**
* All `Õ(·)` running times (Theorems 2.7, 3.1, 3.3, the time parts of 3.2, 4.1, 5.2–5.4) and the `log*`
  bookkeeping of §3. They are compositions of the black boxes' running times.
* The §4 edge-connector algorithm itself; only its colour arithmetic is checked.
* Theorem 5.4 and Corollary 5.5.

**Remark (not formalized, no verdict impact).** In Theorem 5.4 the last stage colours subgraphs of
in-degree `≤ Δ^{1/x}` and out-degree `≤ â^{1/x}` "with `Δ^{1/x} + â^{1/x} + 3` colours by Theorem 5.2". But
Theorem 5.2 only gives `Δ' + O(a')` colours (`Δ' + (2+ε)a' − 1` with the paper's own procedure), and those
subgraphs can have total degree up to `Δ^{1/x} + â^{1/x}`. So the exact constant `+3` in
`(Δ^{1/x} + â^{1/x} + 3)^x` is not justified as written. Constant factors on `â^{1/x}` would only change
constants in Corollary 5.5's analysis.

**Trust.** No `sorry`, `axiom` or `native_decide`. All listed theorems use only `propext`, `Classical.choice`
and `Quot.sound`. Hypotheses are shown satisfiable: the reduction colourer satisfies `IsDeltaColorer`,
maximal cliques give a clique cover, and H-partitions and labellings exist (`exists_hPartition`,
`exists_isHLabeling`, `exists_isLabeling`). Uses CSLib's `LocallyIterative.colorReduction`,
`SimpleGraph.HasOutDegLE` and the staged `Podc/Foundations/Combinatorics/SimpleGraph/EdgeColoring/Basic.lean`.
The H-partition comes from `Papers/PODC2010/ArbdefectiveColoring/HPartition.lean`.

**CSLib candidates.** `EdgeSchedule.lean` (round-scheduled greedy edge colouring); the clique-cover /
connector API in `Basic.lean` (`IsCliqueCover`, `maximalCliques`, `diversity`, `block`).
