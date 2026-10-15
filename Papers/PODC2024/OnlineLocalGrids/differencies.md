# Differences between the formalization and the paper

Paper: Chang, Mishra, Nguyen, Yang, Yeh, *A Tight Lower Bound for 3-Coloring Grids in the
Online-LOCAL Model*, PODC 2024.

Overall verdict: **the results formalized here (Theorems 1.1 and 1.3, Lemmas 3.3–3.6) are correct.**
No step fails. The differences below are imprecise statements, implicit assumptions, and changed
constants or conventions.

## Model

1. **Identifier space.** The paper allows identifiers from `{1, …, poly(n)}`. We use an identifier type
   `ι` with exactly `n` elements, so the input is a bijection `pos : ι ≃ V`. The adversary is
   therefore weaker and the lower bounds are stronger. An algorithm for a larger identifier space
   restricts to one for ours.
2. **Re-embedding is not an adversary primitive.** The paper says the adversary "has the liberty to
   adjust how the current discovered region fits into G". Here the adversary only chooses `pos` and
   `σ`. Re-embedding is derived as an *indistinguishability* lemma: if two inputs agree on all edges
   seen from the revealed nodes, the labels agree (`label_eq_of_agreeOn`, `exists_move`). This makes
   precise the requirement the paper leaves implicit: moved parts must stay at distance `≥ 2T+2`
   from the rest (or touch nothing) and must keep their radius-`T` neighbourhood away from the grid
   border. Translating a piece that touches the border would change its view.
3. **Locality `T = 0` is allowed.** The paper assumes `T(n) ≥ 1` ("3-coloring cannot be solved with
   zero locality"). Our proofs need no such assumption.
4. **Colours.** We use `Fin 3 = {0,1,2}`; colour `2` is the paper's colour `3`, and `0, 1` stand
   for `1, 2`. `aval x y = x - y` for `x, y ≠ 2`, which is the paper's `a`-value up to this
   renaming (`1–2` edges have `a = ±1`, edges touching colour `3` have `a = 0`).
5. **Grids.** We use Mathlib's `pathGraph`, `cycleGraph` and box product `□`, with rows first:
   `grid a b = P_a □ P_b`, `cylinder a b = P_a □ C_b` (each row is a cycle), and
   `torus a b = C_a □ C_b`. These match §2.1.

## Lemmas 3.3–3.5

6. **Lemma 3.4 is strengthened and proved differently.** The paper sums the cells "inside" a simple
   cycle, which implicitly uses the Jordan curve theorem for grid cycles. We build a potential `φ`
   with `a(c p, c q) = φ q − φ p` on every edge (`grid_exists_potential`). It is defined along an
   L-shaped path, and the horizontal edges are checked by induction using Lemma 3.3 on each cell.
   As a result, **every closed walk** has `b = 0` (`grid_bval_closed`), not only simple cycles.
7. **Lemma 3.5** is stated for arbitrary walks; the paper states it for paths. The hypothesis that the
   colouring is proper (along the walk) is explicit. The paper's "Throughout this section, c is any
   proper 3-coloring" carries it implicitly.

## Lemma 3.6

8. **Correctness of the algorithm is a hypothesis.** The paper claims the adversary "constructs a
   directed path with b-value at least k". This is only meaningful if the algorithm colours the
   revealed segment properly: the parity argument (Lemma 3.5) fails otherwise. We state it as
   "if the revealed segment is properly coloured, then it contains a row path with `|b| ≥ k`"
   (`Lemma36`). If the colouring is not proper, the final colouring is already wrong.
9. **Orientation.** The paper writes `b(P_{u,v}), b(P_{s,t}) ≥ k−1` and concatenates `P_{u,v}`,
   `P_{v,s}`, `P_{s,t}`. This silently requires orienting the second piece, by reflecting it, so
   that both large `b`-values point the same way. We make the reflection part of the move: the
   choice of `fl` in `choose_move`. When `k − 1 = 0` the orientation is arbitrary.
10. **Where the second piece is built.** The paper does not say where `P_{s,t}` is constructed
    before it is moved. We build it in a dedicated stretch `[a+s+2T+2, a+2s+2T+2)` of the same row,
    then translate or reflect it next to the first piece.
11. **Constants.** The segment produced for `k` has length `< segLen T k`, where
    `segLen T k + 2T + 2 = 2^k (2T+3)` (`segLen_add`). The paper gives a "discovered region" of
    length `≤ 5^{k+1} T`; growth `2^k` suffices. The paper is silent on the `T`-margins (our reading: its bound counts them inside the
    region), while ours requires them outside it, as hypotheses `T ≤ a` and `a + segLen T k + T ≤ m`.
    Rows also need margins: `T ≤ r`, `r + T < m`. The paper does not mention the vertical margins.

## Theorem 1.1

12. **Explicit statement.** `theorem_1_1`: if `2^(4T+5)(2T+3) ≤ m`, then no algorithm with
    locality `T` 3-colours the `m × m` grid. `theorem_1_1_log`: every correct algorithm satisfies
    `log₂ n < 12T + 14` with `n = m²`. The paper states `Ω(log n)` without constants. Our choice of
    `k = 4T+5` matches the paper's condition `k > 4T+4`.
13. **Second path.** As in the paper, `P_{s,t}` is revealed directly in row `r₂ = r₁ + 2T + 2`,
    exactly above `P_{u,v}` (it is not built with Lemma 3.6). It is reflected about the midpoint of
    its column range if its `b`-value has the same sign as `b(P_{u,v})`. The paper says "we can
    simply reverse the direction of `P_{s,t}`". Reversing must keep `s` above `v` and `t` above `u`,
    which is what a reflection about the midpoint achieves.
14. **Rectangle identity.** It comes from the potential (item 6), not from summing cells.

## Theorem 1.3

15. **The statement in the paper omits that the side length must be odd.** Theorem 1.3 says "the
    locality of 3-coloring `√n × √n` toroidal and cylindrical grids is `Ω(√n)`", with no condition
    on `n`. The proof chooses `n` with `√n` odd. For even `√n` these graphs are bipartite. The
    `O(log n)` algorithm of Akbari et al. for bipartite graphs (Corollary 1.2) then applies, so
    `Ω(√n)` cannot hold for all `n`. The correct reading is "for all `n` with `√n` odd" (or
    "infinitely often"). Oddness appears only in the proof and in a remark at the end of §2.1; the
    abstract and the theorem statement omit it. We state it with `b` (columns) odd and `b ≥ 3`; rows are arbitrary with `a ≥ 4T+3`
    (cylinder) or `a ≥ 4T+4` (torus).
16. **Torus constant.** The torus needs `4T + 4 ≤ a`, one row more than the cylinder: the two
    revealed bands of rows `[0, 2T]` and `[2T+2, 4T+2]` must also be separated across the
    wrap-around. The paper uses `4T + 4 ≤ √n` for both graphs, which is consistent.
17. **General shape.** We allow `a × b` grids with `a` and `b` independent, as in the paper's closing
    remark ("`Ω(a)` whenever `b` is odd"). The `√n` corollaries are `theorem_1_3_*_square`.

## Not formalized

18. **Corollary 1.2** (`Θ(log n)`) and the other-models part of **Corollary 1.4** need the
    `O(log n)` algorithm of Akbari et al. and the simulations between the LOCAL, SLOCAL and Dynamic
    models. They are outside this paper. We formalize the Online-LOCAL upper bound `T = O(√n)` for
    cylinders and tori (`torus_square_tight`, `cylinder_square_tight`). For the grid we only show
    that `T = 2m` suffices (`grid_bounds`).
19. **Theorem 1.5 / Corollary 1.6** ((2k−2)-colouring k-partite graphs, `Ω(n)`). The paper gives
    only a proof sketch and defers to the full version. Not formalized.
20. **Theorems 1.8, 1.10 and Corollaries 1.9, 1.11** are proved only in the full version. Not
    formalized.
