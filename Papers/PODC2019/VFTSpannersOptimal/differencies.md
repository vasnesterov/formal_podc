# Differences between the formalization and the paper

Paper: Bodwin–Patel, *A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners*, PODC 2019
(arXiv 1812.05778v2).

## Errors and imprecisions found

1. **Algorithm 1 read literally is wrong** (genuine imprecision, low severity). The test reads "there exists a set `F` of `|F| ≤ f`
   vertices such that `dist_{H\F}(u, v) > k·w(u, v)`". It does not exclude `u, v ∈ F`.
   * With `F = {u}` the distance is `∞`, so for `f ≥ 1` every edge is added and the output is `G`
     (`ftGreedyLiteral_eq`).
   * On `K_n` with `f = 1` and stretch 3, this output has `n(n-1)/2` edges. That contradicts
     Corollary 2: for every `C` there is an `n` with more than `C·n^{3/2}` edges
     (`literal_violates_corollary2`).
   * The proof of Lemma 3 tacitly uses `F_e ⊆ V \ {u, v}`: it needs "some node `x ∈ C \ {u, v}`
     must be in `F_e`", and `x ∉ e` for the blocking pair. Definition 2 constrains `s, t ∉ F`
     implicitly, via Definition 1's `s, t ∈ V` applied to `G \ F`.
   * We therefore formalize the intended test with `u, v ∉ F` (`vftTest`).
   * For edge faults we likewise require `{u, v} ∉ F` (`eftTest`). Otherwise an edge already in `H`
     could pass the test again.
   * The counterexample relies on the convention that the distance to a deleted vertex is `∞`
     (ours: `wdist = ⊤`). One could instead read `dist_{H\F}(u, v)` as undefined for `u ∈ F`.
     The intended reading (`x ≠ u, v`) is clear from the proof of Lemma 3. So this is a
     statement-level slip, and the result is morally right.
2. **Theorem 1 needs a `max(·, 1)` or an additive term when `f = Ω(n)`** (genuine but cosmetic).
   * The proof says the theorem "holds trivially since it states `|E(H)| = O(n²)`". But when
     `n/f < 2`, `b(n/f, k+1) = 0`, so the stated bound `O(f²·b(n/f, k+1))` is `0` even though `H`
     can have edges.
   * `b(N, ·)` is also only defined for integer `N`. The failure does not depend on the rounding:
     with floor rounding it occurs once `f > n/2`, and with ceiling rounding once `f ≥ n`
     (`⌈n/f⌉ = 1`, so `b = 0`).
   * Our statement is `|E(H)| ≤ 32 f² · max(b(⌊n/2f⌋, k+1), 1)` for all `n` and all `f, k ≥ 1`. Its
     cases:
     * `n < 8f`: the trivial bound `|E| ≤ n²/2 < 32 f²` applies.
     * `n ≥ 8f`: the main argument applies.
   * The paper's `b(n/f, ·)` would become `b(⌊n/2f⌋, ·)`. Since `b` is monotone in `N` (folklore;
     not formalized here), our form is at least as strong.
3. **`n`/`m` typo.** The proof of Theorem 1 says "let `H` be an output graph … on `n` edges and `m`
   nodes"; the two are swapped.
4. **`(1 + o(1))` factors and the ceiling in Lemma 4.**
   * The paper samples `⌈n/(2f)⌉` vertices and writes both probabilities as `(1+o(1))/(4f²)` and
     `(1+o(1))/(8f³)`. This assumes `f = o(n)`.
   * With the ceiling, the triple probability can exceed `1/(8f³)`.
   * We sample `s` vertices with `2fs ≤ n`, e.g. `s = ⌊n/(2f)⌋`, and prove the exact,
     non-asymptotic `m·s(s-1) ≤ 2n(n-1)·|E(H'')|` by counting over all `s`-subsets
     (`IsBlockingSet.exists_dense_subgraph_of_le`, shared with Dinitz–Robelle's Lemma 7). This is
     the paper's `Ω(m/f²)`.
5. **Tie-breaking.** Lemma 3 uses that the last edge `e` of a cycle `C` (in scan order) is at least
   as heavy as the other edges of `C`. This holds for any nondecreasing order, with ties broken
   arbitrarily. We assume `L.Pairwise (w · ≤ w ·)`, which allows ties. Since the algorithm adds
   edges as a sublist of `L`, the insertion order inherits this (`greedyEdges_sublist`).

## Scope

6. **Lower bounds not formalized.** This covers optimality ("best possible … due to [9]"), the EFT
   discussion and the final remark on edge blocking sets.
7. **Edge faults.**
   * The paper only asserts that the EFT proof is "essentially identical". We prove it
     (`ftGreedyEdge_exists_blockingSet`, `ftGreedyEdge_card_edges_le`, `..._rpow`).
   * Instead of edge blocking sets we build a **vertex**–edge blocking set directly. For each fault
     edge `e'` on the cycle, keep one endpoint of `e'` outside the tested edge. Such an endpoint
     exists because `e' ≠ e`.
   * So the VFT Lemma 4 applies unchanged.
   * This also explains the paper's closing remark: edge blocking sets give no more than vertex
     blocking sets.
8. **Running time not modelled.** The FT-greedy test is a classical `decide`; the paper also leaves
   its complexity aside.

## Modelling choices

9. **Edge order and duplicates.**
   * The edge order is a list of ordered pairs. Every edge must occur, and every entry must be an
     edge.
   * Duplicates are harmless: an edge already in `H` never passes the test again, since `k ≥ 1`.
10. **`f ≥ 1`.** Theorem 1 and Corollary 2 assume `f ≥ 1`. The paper leaves this implicit; for
    `f = 0` the bound `32 f² · …` would be `0`.
11. **Stretch.** `k` is a natural number `≥ 1`. The blocking set is for cycles with `≤ k + 1`
    edges; `b(·, k+1)` counts graphs with no cycle of length `≤ k + 1`, i.e. girth `> k + 1`.
12. **Definition of `b`.** `girthExtremal N g` is a `sSup` over graphs on `Fin N`. The supremum is
    attained (`exists_eq_girthExtremal`). The Moore bound for it is proved:
    `b(N, 2k) ≤ N^{1+1/k} + N`, and `b(N, 2k) ≤ d N` whenever `N ≤ d^k`.
13. **Explicit constants.** The paper writes `O(·)`. We give 32 in Theorem 1 and 16 in Corollary 2,
    valid for all `n`.
