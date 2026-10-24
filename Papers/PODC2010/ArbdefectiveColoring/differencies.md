# Differences between the formalization and the paper

Barenboim–Elkin, *Deterministic Distributed Vertex Coloring in Polylogarithmic Time*, PODC 2010
(arXiv:1003.1608v1).

## Model and definitions

1. **LOCAL model as locality.** "Time `T`" is CSLib's `IsLocal T f`: the output of `v` is determined
   by the edges incident to vertices at distance `< T` and the inputs at distance `≤ T`. Identifiers
   are the vertices of a fixed finite type `V` (`n = |V|`, known to everyone, as is the arboricity
   bound `a`). Algorithms are total functions of the graph (local for every graph); correctness is
   proved for graphs of arboricity `≤ a`. Message size is not modelled (LOCAL).
2. **Black boxes.** Lemma 2.1 [Kuhn SPAA'09] is the hypothesis `Lemma21 V C R`: for all `Δ`, `q > 0`
   an `R`-round algorithm computing a `⌊Δ/q⌋`-defective colouring with `< Cq²` colours on all graphs
   of maximum degree `≤ Δ` (the paper: `O(p²)` colours, `O(log* n)` rounds). The `(Δ+1)`-colouring
   of [BE09] used in Lemma 3.3/Lemma 2.2(1) is the hypothesis `DeltaPlusOne V C' R'` (only needed
   for Lemma 4.1). Both are shown satisfiable (with `n` rounds, via Lovász's lemma); CSLib's
   Linial colouring is an unconditional `O(log* n)`-round instance with `O(Δ²)` colours.
3. **Definition 2.1 (arbdefective).** `IsArbdefective G c r` requires arboricity `≤ r` of the
   disjoint union of the colour-class-induced subgraphs (`classGraph G c`); the per-class statement
   of the paper is `IsArbdefective.induce`. The algorithms work on `classGraph` (same vertex set,
   cross-class edges deleted), which models "each subgraph in parallel".
4. **Arboricity.** CSLib's `ArboricityLE a` (edges covered by `a` forests). Everything about
   H-partitions only uses an orientation with out-degree `≤ a` (`HasOutDegLE`), which follows from
   `ArboricityLE a`.
5. **Partial orientations** are parent sets `par v ⊆ N(v)` with no edge oriented both ways.
   **Length** is defined via directed walks (`LengthLE par ℓ`: every directed walk has `≤ ℓ` edges);
   for acyclic orientations (the only ones used) walks are paths, as in the paper. Acyclicity is
   "no vertex reaches itself". We work with height functions (`lengthLE_iff_exists_height`).
6. **Colours** are `0, …, k-1` instead of `1, …, k`; palettes in Algorithm 2 are
   `index · (A+1) + colour` instead of `(i-1)·A + colour`.
7. **Simple-Arbdefective** is implemented in CSLib's locally-iterative model: a vertex sees the
   *set* of its neighbours' states, each state carrying the vertex identifier, its parent set (the
   input orientation) and its colour. Ties in "a colour used by the minimum number of parents" are
   broken by `Classical.choose` (any choice works). Vertices without parents choose in round `0`;
   after `ℓ` rounds all vertices of an orientation of length `ℓ` have chosen (exactly the paper's
   `O(ℓ)`, with constant 1).
8. **H-partition (Lemma 2.3).** Proved, not assumed: the peeling algorithm with degree parameter
   `A` and `L` rounds, terminating when `n (2a)^L < (A+1)^L`; with `A = ⌊(2+ε)a⌋` this holds for
   `L = ⌈2/ε⌉(⌊log₂ n⌋+1)` (`hRounds_ok`). H-sets are indexed from `0`.

## Section 3

9. **Lemma 3.1.** Instead of a topological sort we orient unoriented edges along the injective rank
   `h(v)·|V| + e(v)` (`h` a height function, `e` an enumeration of `V`); we also record that every
   vertex gains at most its deficit many out-edges.
10. **Theorem 3.2.** Proved as stated (arbdefect `τ + ⌊m/k⌋`, `k` colours, `ℓ` rounds). Proof typo:
    "`len(u) ≤ i-1`" should read "`len(w) ≤ i-1`".
11. **Theorem 3.5.** Stated for a generic `d`-defective black box with `K` colours: deficit `≤ d`,
    out-degree `≤ A`, length `≤ L·K − 1`, `L + R + 1` rounds. The H-sets have maximum degree
    `≤ A = ⌊(2+ε)a⌋`, so to get deficit `⌊a/t⌋` from Lemma 2.1 the parameter must be about
    `(2+ε)t`; the paper leaves this implicit. We use `q = 3t` (`⌊⌊(2+ε)a⌋/(3t)⌋ ≤ ⌊a/t⌋` for
    `ε ≤ 1`, `defect_le`), giving `9Ct²` colours and length `< 9C t² L`.
12. **Lemma 3.3 / Lemma 2.4.** `completeOrientation_spec` is Theorem 3.5 with a legal colouring
    (`d = 0`); the running time `O(a + log n)` and length `O(a log n)` become `L + R + 1` and
    `L·K − 1` with explicit `K`, `R` of the black box.
13. **Corollary 3.4** is stated with a legal-colouring black box (`corollary_3_4`); the paper's
    `O(a log n)` needs the [BE09] black box (`K = A+1`).
14. **Corollary 3.6.** Requires `0 < ε ≤ 1` (for `q = 3t`, item 11); rounds
    `L·C(3t)² + R + L` (`arbRoundsε`), i.e. `O(t² log n)` for `R = O(log* n)`.

## Section 4

15. **Lemma 2.2(1)** is derived (not assumed): complete orientation (Lemma 3.3) + greedy colouring
    along it, colours `0..⌊(2+ε)a⌋`; `O(a log n)` rounds with the [BE09] black box.
16. **Algorithm 2.** Parametrized by the number `I` of iterations (`LCParams.proc a I`); the paper's
    while-loop is `I = iters a`, the first `i` with `α_i ≤ p`. The arboricity bounds are
    `α_{i+1} = ⌊⌊(2+ε)α_i⌋/(3p)⌋ + ⌊⌊(2+ε)α_i⌋/p⌋`, which is `≤ ⌊α_i/p + (2+ε)α_i/p⌋` (line 15,
    `next_le`). All procedures use the *bound* `α_i` in place of the unknown arboricity of the
    subgraphs (the paper's Partial-Orientation is stated with the exact arboricity `a`); line 2
    (`α := a(G₁)`) is replaced by a known upper bound `a`.
17. **Final step of Algorithm 2 (line 19).** For Theorem 4.3 / Corollary 4.4 we colour the final
    subgraphs with Lemma 2.2(1) using the legal colouring of Lemma 2.1 (`q = Δ+1`, `O(Δ²)` colours),
    so the step takes `O(p² log n)` rather than the paper's `O(p log n)` rounds; this does not
    change the `O(a^μ log n)` bound and avoids a second black box. Lemma 4.1 needs the `O(Δ)`-colour
    black box of [BE09] (`DeltaPlusOne`), as in the paper.
18. **Lemma 4.1.** `k = t = ⌊a^{1/3}⌋`, `a ≥ 1`, `0 < ε ≤ 1`; colours `< ((2+ε)(3+ε)+1)·a` (the
    paper: `k·γ` with `γ = ⌊(2+ε)(3+ε)a^{2/3}⌋+1`); rounds explicit (see README).
19. **Lemma 4.2(2).** Proved in the form "fewer than `4/μ` iterations" for `p = ⌊a^{μ/2}⌋ ≥ 16`,
    `0 ≤ ε ≤ 1/2` (the paper: `≤ log_b a ≤ 4/μ`); a general version for any `p ≥ 16` with
    `(3+ε)a^θ ≤ p` gives `< 1/θ` iterations (`iters_lt_of`).
20. **Lemma 4.2(3)** is stated with `|𝒢_i| = p^i` (we count all `p^i` subgraph indices, empty ones
    included, as the paper's line 9 does).
21. **Theorem 4.3.** The statement's `p = ⌈a^{μ/2}⌉` is a typo for `⌊a^{μ/2}⌋` (used in the text and
    proof); we use the floor. We assume the paper's w.l.o.g. condition `p ≥ 16` explicitly, and
    `0 < ε ≤ 1/2` (the paper uses `ε < 1/2` in Lemma 4.2(2)); the paper's `μ < 1` is not needed.
    Colours: fewer than `(3+ε)^{4/μ+1}·a` (the paper: `(3+ε)^c a` with `c = 4/μ+1`, "for
    sufficiently large `a`"). Rounds: `≤ (4/μ+1)(L(9C a^μ + 2) + R)`.
22. **Corollary 4.4.** The proof's case split is wrong (see README; `corollary_4_4_proof_gap`:
    for `a = (log₂ n)²`, `μ' ≤ 1/2`, `n ≥ 4`, the paper's `p = ⌊a^{μ'}/log n⌋` satisfies
    `p ≤ 1 < a^{μ'/2}`; `line15_one`: with `p = 1` line 15 never decreases `α`). Our proof splits at
    `a^{μ/4} ≈ log n` into three cases (Legal-Coloring with `p = ⌊a^{μ/2}/ℓ⌋`; Theorem 4.3 with
    `μ²/4`; constant `a` via Lemma 2.2(1)). Statement: for `0 < ε ≤ 1/2`, `0 < μ ≤ 1` there are
    `c₁, c₂, c₃` (depending on `ε, μ, C` only, uniform in `n` and in the vertex type) such that for
    every `a ≥ 1` some algorithm uses `< c₃ a` colours and `≤ c₁(a^μ + ℓ^{1+μ}) + c₂ R` rounds,
    `ℓ = ⌊log₂ n⌋ + 1`. The algorithm depends on `a` and `n` (both known to all vertices).
    `μ ≤ 1` is harmless ("arbitrarily small constant").

## Not formalized

23. Lemma 2.1 and [BE09] (black boxes, see item 2); Lemma 2.2(2) (forest decomposition into `O(a)`
    forests — not needed); Lemma A.1 (only Lemma A.2 is formalized); Theorem 4.5, Corollaries 4.6,
    4.7; Section 5 (Procedure Arb-Recolor, Lemma 5.1, Theorems 5.2, 5.3; Theorem 5.3's
    "`O(a/t)`-coloring" is a typo for `O(a·t)`); Appendix B.
