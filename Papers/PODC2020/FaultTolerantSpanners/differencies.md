# Differences between the formalization and the paper

Paper: Dinitz–Robelle, *Efficient and Simple Algorithms for Fault-Tolerant Spanners*, PODC 2020
(arXiv 2002.10889v2).

## Scope

1. **Distributed results skipped.** Theorems 11–15 (Section 5, LOCAL and CONGEST) are not formalized.
   They are corollaries of external constructions used as black boxes: padded decompositions [DK11],
   Baswana–Sen [BS07] and the [DK11] reduction. Their guarantees hold with high probability.
2. **Running times not formalized.** This covers Theorem 4's `O((m+n)α)`, Theorem 9 and the time part
   of Theorems 2/10. Only the structural fact is visible: Algorithm 2 makes at most `α + 1` oracle
   (BFS) calls, by its definition.
3. **Algorithm 1 not formalized.** The exponential greedy algorithm of [BDPW18, BP19] is only
   motivation.
4. **Edge faults.** Theorem 4, Theorem 5 and Theorem 10 (correctness) are formalized for edge faults
   too: `lbcEdge_correct`, `modifiedGreedyEdge_isEFTSpanner`,
   `modifiedGreedyEdge_isWeightedEFTSpanner`. The **size bound for edge faults is not formalized**.
   The paper only says the proof is "essentially identical". It would need vertex–edge blocking sets
   replaced by edge–edge ones, with a different count in Lemma 7.

## Modelling choices

5. **BFS is an oracle.** "Run BFS to find a path P of length at most t from u to v in G \ F" is an
   arbitrary oracle `O` with `O.Spec`: it returns some `u`–`v` walk of length `≤ t` if one exists,
   `none` otherwise. All results hold for every oracle, i.e. for every choice of the path. The oracle
   may return walks rather than paths. "Add all vertices of P \ {u, v}" then becomes
   "add `p.support \ {u, v}`" (`Walk.interior`). This has at most `length ≤ t` elements, so the
   paper's count is unaffected.
6. **`G \ F` keeps the vertex type.** `G.deleteVerts F` removes all edges touching `F` instead of
   removing the vertices. For `u, v ∉ F` the distances agree with `G[V \ F]`, which is all that
   Definition 1 uses.
7. **Edge order.** The edge order is a list `L : List (V × V)` of ordered pairs. Every entry is an
   edge of `G`, and every edge occurs in at least one orientation. Duplicates are allowed: a second
   copy of an edge is never added, because an edge already present has no cut. Algorithm 4's
   "nondecreasing weight order" is the hypothesis `L.Pairwise (w · ≤ w ·)`.
8. **Weights.** Weights are `w : Sym2 V → ℝ≥0` (the paper uses `R≥0`). Distances are in `ℝ≥0∞`
   (unweighted: `ℕ∞`), with `⊤` for "no path", as in the paper's convention.
9. **Theorem 4, NO part.** The NO part is stated as its contrapositive: YES implies a length-`t` cut of
   size `≤ α t` (`exists_isLengthCut_of_lbc`). `lbc_correct` also gives the paper's form.

## Statements changed or made precise

10. **Lemma 3 (weighted) has a different proof.** In the "if" direction the paper writes, for `p = 1`,
    "`d_{H\F}(u, v) = w(u, v) = d_{G\F}(u, v)`". This is a slip: `H` need not contain the edge `uv`.
    What holds is `d_{H\F}(u, v) ≤ t·w(u, v)` by hypothesis, which suffices. The paper's argument also
    uses a shortest path. We prove the full iff (`isWeightedVFTSpanner_iff`) a different way, without
    shortest paths. A non-tight edge `xy` has a strictly lighter `x`–`y` walk, all of whose edges are
    strictly lighter than `xy`; strong induction on the number of lighter edges finishes the proof
    (`wdist_le_mul_of_tight`). This needs a finite vertex type. Theorems 5 and 10 only use the
    easier "check all edges" direction (`isVFTSpanner_iff`, `isWeightedVFTSpanner_of_adj`). Their
    proofs work for all edges, not only tight ones.
11. **Lemma 7 is made explicit and non-asymptotic.** The paper assumes `f = o(n)` and gets
    `Ω(m/(kf)^2)` edges up to a factor `(1 - o(1))`. Strictly, the paper's estimate
    `s(s-1)/(n(n-1)) ≥ (1-o(1))/(4((2k-1)f)^2)` needs `kf = o(n)`, not `f = o(n)`: `k` may grow with
    `n`. Theorem 8 is still trivially true when `kf = Ω(n)`, so this is harmless.
    The formal statement (`IsBlockingSet.exists_dense_subgraph`): if `|B| ≤ D·m`, `D ≥ 1` and
    `2Ds ≤ n`, some `s`-set `S` carries a subgraph `H' ≤ H` of girth `> 2k` with
    `m·s(s-1) ≤ 2n(n-1)·|E(H')|`.
    The proof is exact counting over all `s`-subsets, not probability. The key bound is
    `(n-2) - D(s-2) ≥ (n-2)/2`, valid for every `n`.
12. **Theorem 8 has explicit constants.** `|E(H)| ≤ 8 (2(2k-1)f)^{1-1/k} n^{1+1/k} ≤ 32 k f^{1-1/k}
    n^{1+1/k}` holds for all `n` and all `k, f ≥ 1`. The case split `n < 8(2k-1)f` (trivial bound
    `m ≤ n²/2`) replaces the paper's "if `f = Ω(n)` the theorem is trivially true".
13. **The Moore bound is proved, not cited.** If the girth is `> 2k`, all edges lie in `S` and
    `|S| ≤ d^k`, then `|E| ≤ d|S|`; in particular `|E| ≤ n^{1+1/k} + n`. The proof uses min-degree
    peeling and path counting. The paper cites it ("long been known", [ADD+93]) as
    `O(n^{1+1/k})`. In Theorem 8 it is applied with `d = ⌈s^{1/k}⌉`.
14. **Definition 2 (blocking set)** additionally records that the edge of each pair is an edge of
    `G`; the paper writes `B ⊆ V × E`. "`v, e ∈ C`" means: `v` is in the support of the cycle and
    `e` is in its edge list.

## Errors found

No substantive errors. The paper's results hold as stated, with the explicit constants above. The
minor issues are the `p = 1` slip in the proof of Lemma 3 (item 10) and `f = o(n)` vs. `kf = o(n)`
in Lemma 7 (item 11).
