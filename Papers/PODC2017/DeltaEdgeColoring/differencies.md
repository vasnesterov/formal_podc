# Differences between the formalization and the paper

Paper: Barenboim, Elkin, Maimon, *Deterministic Distributed (Δ + o(Δ))-Edge-Coloring, and Vertex-Coloring of
Graphs with Bounded Diversity*, PODC 2017, arXiv 1610.06759v1.

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Theorem 3.2, proof of the colour bound (appendix B): inductive step invalid for `i = 1` — proof repair
   (🛠️, R1: the statement is true).**
   - The step bounds `𝒜_{i+1}`'s colours by `(D(t−1)+1)·D^{i+1}⌈S/t⌉` using only the induction hypothesis.
   - It claims `≤ D^{i+2}S` for large `S` "because `t = ⌊S^{1/(i+1)}⌋` and `i ≥ 2`". `i = 1` (`𝒜_2`) is not
     covered, and for `i = 1`, `t = ⌊√S⌋` the inequality is false for infinitely many `S`
     (`paper_inductive_step_fails`: `D = 2, S = 31, t = 5`).
   - The running-time part of the proof switches to `t = ⌊S^{1/(i+2)}⌋`. With it the step works for `S`
     above a constant (constant `S`: §3's direct colouring). Borderline 🛠️ vs ✅: the fix is recoverable
     from the paper, but the colour-count argument as written has a missing case (`𝒜_2`) and a false
     inequality for the parameter it states; we count it as a proof repair (R1: a false claim inside a
     proof whose result is true).
   - Repair: the invariant `pal_j (D S_j − 1) ≤ D^j (D S − 1)` holds for every level choice with
     `t² ≤ S_cur` and `D ≥ 2` (`step_bound`, `theorem_3_2`). It gives `< D^{x+1}S` colours for all
     `S ≥ 1`, for both of the paper's choices of `t` (`theorem_3_2_algA` uses `t = ⌊S_cur^{1/(x−j+1)}⌋` at
     level `j`), with no colour reduction.
2. **Theorem 3.2, base case `𝒜_1`: correct (no verdict impact).** The `+(D−1)²` term disappears between the
   4th and 5th lines of the chain, but legitimately: `t + k ≥ 2⌊√S⌋` and `D(D−1) ≥ (D−1)²`, so
   `−D(D−1)(t+k) + (D−1)² ≤ −(D²−D)(2⌊√S⌋−1)`. The resulting `≤ D²S + 2` holds for `D ≥ 2` and `S ≥ 4`. It is
   not tight: the count is `≤ D(DS − 1) < D²S` (`theorem_3_2` with `x = 1`), so the paper's 2 extra
   colour-reduction rounds are not needed.
3. **Theorem 3.2 for `D = 1`: not covered by the proof (degenerate, R2).** The proof assumes `D ≥ 2`; the
   statement does not. For `D = 1` (disjoint unions of cliques) the algorithm without reduction can exceed
   `S` colours (e.g. `S = 5`: `t = 2`, palette `2·3 = 6`). Colour reduction (allowed by the paper) fixes
   this, and the instance is trivial. Our `theorem_3_2` assumes `D ≥ 2`.
4. **Definition of (p,q)-clique-decomposition**: "the maximum size of a clique in `G(U_i)` is `q`". We read it
   as "at most `q`" (R3, evident intent).
5. **Theorem 2.4's clique bound `S/t^x + 2`**: we prove the sharper `⌈S/t^x⌉ ≤ S/t^x + 1`. The paper's bound
   follows.
6. **Theorem 5.4 (not formalized; recorded only).** Its last factor `Δ^{1/x} + â^{1/x} + 3` is attributed to
   Theorem 5.2, which only gives `Δ' + O(a')` colours. The degree of the final subgraphs is bounded by
   in-degree plus out-degree, not by `Δ^{1/x}`. Not part of the checked statements, so no verdict impact.

## Modelling choices

- **Synchronous LOCAL algorithms, combinatorial level.** We formalize the algorithms as deterministic functions
  of black-box subroutine outputs and check correctness and colour counts. `Õ(·)` running times, the
  `log* n` bookkeeping (§3) and Theorem 2.7 are not formalized. Round counts are formalized only for the
  schedules of Lemma 5.1 (`d` rounds) and Theorem 5.2 (`ℓ·d` rounds; `ℓ = 2(⌊log₂ n⌋+1)` for degree `3a`).
- **Black boxes.**
  - [17] `(Δ+1)`-vertex colouring: `IsDeltaColorer`, i.e. any function returning a proper colouring with
    colours `≤ Δ` when the degree bound is valid. All theorems hold for every such colourer.
  - [4] H-partition: `IsHPartition` (degree `d`, `ℓ` sets). Instantiated with degree `3a`, i.e. `ε = 1`,
    via the PODC'10 ArbdefectiveColoring formalization. The paper's `(2+ε)a` for small `ε` changes only
    constants.
  - The `O(a)`-edge-colouring of the H-sets ([17] / §4) is any proper colouring. In the arboricity
    corollaries it is a greedy `(2d−1)`-colouring.
  - The edge colourings in Theorem 5.3 are runs of Theorem 5.2 (via `theorem_5_2_arboricity`).
- **Clique identification.**
  - The paper's "maximal cliques, or a consistent identification" is modelled by `IsCliqueCover` (cliques
    covering all edges, each vertex in `≤ D`, each of size `≤ S`).
  - Lemma 2.3 (i) / Theorem 2.4's "every clique of `G[U_i]`" bound needs `𝒬` to contain every clique
    (`CoversCliques`). This holds for maximal cliques.
  - For a mere identification (e.g. stars of a line graph) only the identified cliques shrink. That is all
    that the degree bounds and the colour count use.
- **Partition of a clique into blocks.**
  - Each clique is split into consecutive blocks of `t` vertices by ID rank (`block`).
  - The paper assumes `t > 1`; we allow `t ≥ 1`.
  - The recursion parameter may depend on the level and the current clique bound (`cdColoringSched`).
    Algorithm 1 is the constant case `cdColoring`.
- **Recursion unrolled.**
  - The parallel recursive calls on the colour classes are one call on the disjoint union `sameColor G φ`.
  - Colours are encoded in mixed radix (`idx · B + ψ`) instead of tuples. The number of colours is the
    palette bound (all colours `< N`).
  - `x` is the number of connector levels, as in Algorithm 1 (`x = 1`: one connector, then the direct
    colouring). We also allow `x = 0` (direct colouring only).
- **Runs of Lemma 5.1 / Theorem 5.2.**
  - A run is any colouring satisfying the local rule (`EdgeSchedule.Follows`). This matches "any assignment
    of distinct available colours".
  - The rule asks for a colour different from all adjacent edges that are pre-coloured or coloured in an
    earlier or the same round. `lemma_5_1_parallel` / `theorem_5_2_parallel` show that the same-round
    adjacent edges are exactly those chosen by the same vertex. So the rule is locally executable.
  - The stages of Theorem 5.2 ("apply Lemma 5.1 for `H_i` vs `H_{i+1} ∪ … ∪ H_ℓ`, from `H_ℓ` back") are one
    global schedule. Stage `ℓ−1−i` handles `H_i`.
  - The palette is `max k₀ (Δ + d − 1)`, which is `Δ + O(d)` with an explicit constant.
- **Orientation connector (§5).**
  - The acyclic orientation is given by a rank `r` (`u → v` iff `r u < r v`). For the arboricity corollary,
    `r = h·n + ID` (H-index, then ID), as in the paper.
  - Group sizes: the paper's `k = ⌈√Δ⌉` incoming groups of size `⌈Δ/k⌉` become groups of size `⌊√Δ⌋+1`
    (at most `⌊√Δ⌋+1` groups). The paper's `⌈√d⌉` outgoing groups of size `⌈√d⌉` become groups of size
    `⌊√d⌋+1`.
  - Virtual vertices are `V × Fin (m+1)` (a fixed number per vertex; unused ones are isolated).
  - We bound the degree of a colour class by the number of virtual vertices, `max(nIn, nOut)`, which is
    stronger than the paper's `k + O(√a)`.
- **Theorem 5.3's conclusion is existential.** `theorem_5_3_count`, `theorem_5_3` and
  `theorem_5_3_arboricity` conclude "there is a proper edge colouring with `N` colours". On its own, that
  conclusion also follows from Vizing's theorem (`N ≥ Δ + 1`). The algorithmic content is in the proof
  and in the separate lemmas: the colouring is `⟨φ, ψ⟩` with `φ` a run of Theorem 5.2 on the connector and
  `ψ_i` runs of Theorem 5.2 on the classes. `theorem_5_3_combine` shows that every such combination is
  proper, and `oconn_*` / `classGraph_*` give the degree and out-degree bounds used to invoke Theorem 5.2.
- **Theorem 5.3's `Δ + o(Δ)`.** Stated as an explicit bound `(√Δ + 7√(3a) + 8)²` (`theorem_5_3_arboricity`)
  plus an ε–δ form: for all `ε > 0` there are `δ > 0` and `N` with bound `≤ (1+ε)Δ` when `Δ ≥ N` and
  `a ≤ δΔ` (`theorem_5_3_asymptotic`).
- **Theorem 4.1.** Only the colour arithmetic `(2t−1)^x(2⌈Δ/t^x⌉−1) ≤ 2^{x+1}Δ` for `t = ⌊Δ^{1/(x+1)}⌋` (any
  `t ≥ 1` with `t^{x+1} ≤ Δ`) is checked. The edge-connector algorithm is not formalized.
- **Not formalized**: Theorems 2.7, 3.1, 3.3, the algorithm of 4.1, 5.4, Corollary 5.5, and the abstract's
  comparison with previous running times.
