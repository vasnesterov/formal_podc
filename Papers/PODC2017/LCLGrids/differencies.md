# Differences between the formalization and the paper

Paper: S. Brandt, J. Hirvonen, J. H. Korhonen, T. Lempiäinen, P. R. J. Östergård, C. Purcell,
J. Rybicki, J. Suomela, P. Uznański, *LCL problems on grids*, PODC 2017 (arXiv:1702.05456v2).
Formalized: Section 9 (Theorem 9 with Theorem 10 and Lemmas 12–14), Theorem 21, Lemma 24, and the
third case of Theorem 22.

## Errors in the paper

1. **Theorem 22, third case, is false as written (⚠️, R3).** Theorem 22 says that if `2 ∉ X`,
   `{1,3,4} ⊄ X` and `{0,1,3} ⊄ X`, then "no solution exists for infinitely many `n`". The set
   `X = {0,3,4}` (and, by reversing all edges, `{0,1,4}`) is in this case, but a `{0,3,4}`-orientation of
   the `n × n` torus exists for **every** `n ≥ 3` (`exists_orientation034`,
   `theorem22_third_bullet_false`, `Orientation034.lean`). The construction is invariant under the
   diagonal shift `(x, y) ↦ (x + 1, y + 1)`. Each diagonal `k = y − x` gets a value `t_k ∈ {0,1,2}`,
   the number of the two edges between diagonals `k` and `k + 1` that point to `k + 1`. The node
   in-degree is then `2 − t_k + t_{k−1}`. The cyclic sequence `t = 0,2,0,2,…` (even `n`), or
   `0,2,…,0,2,1` (odd `n`), gives in-degrees in `{0,3,4}`. A brute-force search also found
   solutions for `n = 3,…,7`.
   *Severity.* The complexity claim is still right. `{0,3,4}`-orientation is global, as the paper
   itself proves by a different argument (Theorem 25, via `q`-sum coordination), and the
   introduction states the classification correctly ("otherwise it is global"). Only the reason
   given in Theorem 22, non-existence of solutions, is wrong; it holds for the other sets of this
   case, e.g. `{1,3}` (Lemma 24). The intended statement can be recovered from the paper itself (the
   introduction and Theorem 25) and the fix is local. So by R3 this is a minor statement issue,
   not a false claim. Borderline with ❌: the bullet as written asserts a different complexity class (unsolvable) than the true one (global); we take R3 because the correct classification is stated in the introduction and proved in Theorem 25, which the proof of Theorem 22 itself invokes ("the following lemmas cover the remaining cases"), so a reader of the paper is not misled. We did not formalize Theorem 25 (Θ(n) for `{0,3,4}`).

2. **Typos and slips** (none affects a statement):
   * Proof of Theorem 10: "let `d = A(F₁X₂F₂) − A(F₁X₂F₂)`" should read `A(F₁X₂F₂) − A(F₁X₁F₂)`.
   * Reduction to 3-colouring: "for some `q` satisfying the conditions in Section 10" means the
     conditions of Theorem 10.
   * Proof of Lemma 14: the nodes of row `r` are written `(r, y)` with `y` the position along the
     row, which swaps the coordinates relative to the convention `u = (x_u, y_u)` (`y` = row) of
     Section 3.
   * Proof of Lemma 12: "southbound on `r` (`S_{r1}`)" means "on `r₁`".

## Model and statements

3. **LOCAL model on oriented tori.** A `T`-round algorithm for a fixed `n` is a map
   `A : (ℤ × ℤ → ℕ) → Col` that only depends on the identifiers at the offsets `d` with
   `|d₁| + |d₂| ≤ T` (`GridLocal`). Node `v` outputs `A (d ↦ I (v + d))`. Since the grid is
   consistently oriented and the nodes know `n`, this is exactly what a node learns in `T`
   rounds, so it is equivalent to the paper's model. Identifiers are natural numbers in
   `[0, B)`, not `{1, …, poly(n)}`. The lower bound assumes correctness only for `B = 8n²` and
   therefore holds for every identifier range of size at least `8n²`. Colours are the inductive
   type `Col = {one, two, three}`.
4. **Theorem 9** is proved in a quantitative form: for every odd `n`, a `T`-round algorithm that
   properly 3-colours all `n × n` tori satisfies `n ≤ 8T + 8` (`theorem9`). Hence `T(n) ≠ o(n)`
   (`theorem9_not_isLittleO`). The paper states "`Ω(n)`" and proves "not `o(n)`" along odd `n`;
   the formal statement is stronger. Even `n` is not covered, as in the paper.
5. **No greedy post-processing.** The paper first makes the colouring greedy with a constant-round
   step. This is not needed: Lemmas 12–14 hold for every proper 3-colouring (`Basic.lean`,
   `Invariant.lean`). The local facts about `H` are checked on all `3 × 3` blocks by `decide`
   (`Block.key`): in-degree = out-degree, `ℓ = (in-edges from below) − (out-edges to below)`, and
   `ℓ(v) ≠ 0` iff the west and east neighbours of a colour-3 node differ. For greedy colourings,
   the paper's case list (Figure 5b) is consistent with this.
6. **The auxiliary graph `H`.** It is defined directly by diagonal steps (`HEdge`), with the
   colour-1 common neighbour on the left. This matches the paper's definition ("share two
   neighbours…") for `n ≥ 5`. For `n = 4`, two nodes at distance 2 on a row also share two
   neighbours; this degenerate case is irrelevant for the asymptotic result.
7. **Lemma 12** is proved for every closed walk whose steps change the row by ±1, in particular
   every directed cycle of `H` (`lemma12`, `crossing_eq_of_rows`), for all `n`. The proof differs
   from the paper's pairing argument: `i_r` is the net number of steps from row `r − 1` to row `r`,
   and these counts telescope. The paper's argument implicitly needs `r − 1 ≠ r + 2`, i.e.
   `n ≥ 4`.
8. **The corollary of Lemma 12 and the definition of `s`.** The paper defines
   `s(G) = Σ_{C ∈ 𝒞} i_r(C)` for a decomposition `𝒞` of `H` into edge-disjoint directed cycles and
   uses `s(n) = Σ_v ℓ(v)` "directly by definitions". We work with `rowSum c r = Σ_x ℓ(x, r)`
   directly. We prove that it is independent of the row (`rowSum_eq`) by flux conservation in the
   Eulerian graph `H` (`rowSum_eq_flux`, `indeg_eq_outdeg`), without a cycle decomposition. The
   identity `Σ_C i_r(C) = Σ_v ℓ(v)` is not formalized. It is routine: a node of in- and
   out-degree 2 contributes 0 under either pairing of its edges.
9. **Lemma 14** is proved for every proper 3-colouring (not only greedy ones and not only those
   produced by `A`). The parity part is proved in the stronger form `s ≡ n (mod 2)` for all `n`
   (`rowSum_cast_two`). Its proof is the paper's parity argument on the row in another
   bookkeeping: with `g(x)` the colour of the last non-3 node up to `x`, the colour changes of `g`
   around the row are even. The paper's step "there are two adjacent nodes with colours 1 and 2
   (by greediness)" is not needed. The bound `|s| ≤ n/2` is `two_mul_abs_rowSum_le`. The paper's
   artificial values `s(n)` for `n < n₀` are not needed, because the formal Theorem 9 is proved
   for each `n` separately.
10. **Lemma 13** (`lemma13`) assumes `4(T + 2) ≤ n` instead of `T < n/4`, and an identifier range
    `B ≥ 3n²` that leaves room for the fresh identifiers of the proof. `ℓ` reads the `3 × 3`
    block, so a row sum depends on the identifiers up to distance `T + 2`. The paper explicitly
    absorbs such `O(1)` terms in its "radius-1 LCL" convention (Section 3), and the lemma is only
    used with `T = o(n)`. We neither prove nor refute the literal bound `T < n/4`; this is a
    constant-level imprecision, not a statement issue. The proof of Theorem 9 does not use
    Lemma 13. It needs only the special case of strip instances (`rowSum_far`): far from the strip
    these instances carry the same identifiers.
11. **Theorem 10** is proved by a different and stronger argument (`QSum.lean`). If `8T < n` and
    identifiers range over `[0, 7n)`, then any `T`-round algorithm whose outputs sum to a fixed
    `Q` on every directed `n`-cycle has `Q ∈ nℤ` (`sum_eq_mul`). This holds for any output
    alphabet. The reason: word sums `α_{FG}(L)` between blocks of length `2T` depend only on the
    length `L`, are affine in `L` with a common slope `δ`, and the two-block cycle identity forces
    `Q = nδ` (`alg`). For odd `Q` with `|Q| ≤ n/2` this is impossible, so `n ≤ 8T`
    (`theorem10_of_solves`; the paper has `T ≥ n/200`). The family version is `theorem10`. The
    paper's own proof (Lemma 11 and the arithmetic progression of sums) is not formalized. We
    checked it by hand and found it correct up to the typo above. Lemma 11 is not formalized
    separately: its context (an `o(n)`-round algorithm for `q`-sum coordination) is
    contradictory by Theorem 10. The output range `{−1, 0, 1}` is part of `Solves` but is not used.
12. **The reduction** (`Theorem9.lean`). The cycle node `x` with identifier `id x` simulates the
    column `x` of a strip of `2T + 3` rows; the grid identifiers are `id x · n + y` in the strip
    and `7n² + x n + y` elsewhere (`gridOf`). It outputs `ℓ(x, 0)` (`cycAlg`, a `(T + 1)`-round
    cycle algorithm). The paper simulates "a `T(n)`-wide strip". Its brute-force branch for
    `n < n₀` is unnecessary in the per-`n` formulation.
13. **Theorem 21** (`not_edgeColouring_torus`) is stated with Mathlib's line graph
    (`IsEmpty ((torusGraph d n).lineGraph.Coloring (Fin (2d)))`) and assumes `d ≥ 1` and `n ≥ 3`.
    For `n = 1` the "grid" has no edges and the empty colouring exists (R2, degenerate). For
    `n = 2` the grid is not `2d`-regular as a simple graph.
14. **Lemma 24** (`not_exists_oneThreeOrientation_torus`) holds for every odd `n`, including
    `n = 1`, where there are no edges and every in-degree is 0. Orientations are CSLib's
    `SimpleGraph.Orientation`.
15. **Not formalized:** Theorems 2–4 and 15, Lemmas 7, 8, 11, 17–20, 23, Theorem 25, the
    `O(log* n)` upper bounds, the undecidability result, the normal form and synthesis, the
    `d`-dimensional 3-colouring lower bound, and the appendix.
