# Differences between the formalization and the paper

Paper: Hilke, Lenzen, Suomela, *Local Approximability of Minimum Dominating Set on Planar Graphs*, PODC 2014 BA
(arXiv 1402.2549 v1).

## Statements

1. **Lemma 1 needs `m − 2T ≥ 3`.** The paper says "for any `m`" (after fixing `m ≫ T`). Its last step ("the
   common output cannot be 0") needs an internal node with an all-internal closed neighbourhood. `lemma_1` assumes
   `2T + 3 ≤ m`. For `m − 2T ∈ {1, 2}`, `T ≥ 1`, the inference fails in `G` alone. The lemma itself (with the paper's
   hypothesis that `A` is correct on *all* planar graphs on `n` nodes) still holds if the view is that of
   `Cslib.Local.IsLocal T` or the induced radius-`T` ball: compare with a taller grid. It fails for `m − 2T = 1` if nodes
   also see the degrees of the nodes at distance `T` (see README). With our weaker hypothesis (correctness only on
   relabellings of `G`) it fails for `m − 2T ∈ {1, 2}`: "join iff a horizontal border is visible within distance `< T`".
   These arguments are in prose only, not in Lean. For `m ≤ 2T` there are no internal nodes and the lemma is vacuous.
2. **`ℓ` is a constant.** The paper's `ℓ = o(r)` with `ℓM > N`. We take any `ℓ ≥ N` (the Ramsey number), which does
   not depend on `r`; `lemma_1` holds for every `r`. In `main_theorem`, `ℓ = N + 1` and `r = (m + 1)ℓ`.
3. **Main theorem: explicit and stronger form.** `main_theorem` gives `W`, `H` (so `n = WH`) depending only on `T`
   and `ε`. It assumes correctness of `A` only on the relabelled copies `lab σ` of the single grid `grid W H`, and
   produces one assignment `σ` and a dominating set `D` with `(7 − ε)|D| < |A(lab σ)|`. Since `γ ≤ |D|`, this
   refutes the approximation ratio `7 − ε`. `no_local_approx_planar` is the paper's formulation: a family
   `A n` (the algorithm may know `n`) that is `T`-local for every `n` cannot output, on every straight-line-planar
   graph on `Fin n`, a dominating set of size `≤ (7 − ε)|D|` for every dominating set `D`.
4. **Approximation ratio.** "Factor `α` approximation" is formalized as `|A(G)| ≤ α · |D|` for every dominating
   set `D` (equivalently `≤ α γ(G)`). It is a ratio, with no additive constant.

## Model

5. **LOCAL model.** We use the extensional CSLib notion `Cslib.Local.IsLocal T`: the output at `v` is a function
   of the edges incident to nodes at distance `< T` and of the identifiers at distance `≤ T`. This is exactly what
   `T` rounds of LOCAL reveal. The paper says the output "only depends on the radius-`T` neighbourhood". If that
   means the induced subgraph on the ball, it also includes the edges between two nodes at distance exactly `T`.
   Such an algorithm is `(T + 1)`-local in our sense. Since the theorem holds for every `T`, it covers both
   readings. Outputs are `Bool` (`A(G, v) ∈ {0, 1}`).
6. **Identifiers** are `Fin n = {0, …, n − 1}` instead of `{1, …, n}`, a harmless shift. Networks are graphs on the
   identifier set (the standard CSLib encoding). A node knows nothing besides its view. The algorithm may depend
   on `n` (or, in `main_theorem`, is arbitrary for the fixed `n`).
7. **Planarity** is formalized as the existence of a straight-line planar drawing (`IsStraightLinePlanar`). This
   is equivalent to planarity for finite graphs by Fáry's theorem, which is not formalized. Since the theorem is a
   lower bound, assuming correctness only on a subclass of planar graphs gives a stronger statement, provided the
   subclass consists of planar graphs; we prove the triangulated grids are planar in this sense.

## Construction

8. **Graph `G`.** Figure 1a only shows `G`. We read it as the `rm × m` piece of the triangular lattice (square grid
   plus the diagonals `(x, y) — (x + 1, y + 1)`), with block `i` = columns `[im, (i+1)m)`. The internal nodes of a
   block are `T ≤ a < m − T`, `T ≤ b < m − T` (block coordinates), so `m′ = m − 2T` as in the paper.
9. **`D*`** (Figure 1b only shows it). `D* = {(x, y) : x + 2y ≡ 0 (mod 7)} ∪ (outer border of the grid)`. The
   residue class is a perfect code of the triangular lattice, and the border nodes are added because they lack
   some neighbours. `|D*| ≤ (W/7 + 1)H + 2H + 2W` (`card_dstar_le`). The paper's "a fraction 1/7 of internal nodes"
   is about the same density. Its bound `|D*| ≤ (1/7 + ε′)n` hides these `O(rm)` border nodes.
10. **Colouring `c(X)`.** The paper defines `c(X)` by placing `X` in `R_v` and "the identifiers from `V \ X`
    arbitrarily". We define it from the view: `outF A f` is the output of `A` at any node with view `f`, which is
    well defined by `out_eq_of_view_eq`, and `colour A X = outF A (placement X)`. The two definitions agree
    whenever the paper's is well defined (`out_eq_outF`). This avoids having to extend a partial assignment to a
    bijection.
11. **Order "by rows".** Both in blocks and in `R_v` we use row-major order. Node `(im + a, b)` of block `i` gets
    the `(bm + a)`-th smallest identifier of `Yᵢ`, and position `(i, j)` of `R_v` gets the `(jk + i)`-th smallest
    of `X`. The paper says "bottom row from left to right"; the orientation is immaterial.
12. **Repeated Ramsey.** `V₀ = Fin n`, `Yᵢ ⊆ Vᵢ` of size `M = m²` (monochromatic when `|Vᵢ| ≥ N`), `Vᵢ₊₁ = Vᵢ \ Yᵢ`.
    The paper assigns the leftover `ℓM` identifiers "arbitrarily". We continue the same procedure for all `r`
    blocks, with no monochromaticity needed for the last `ℓ`. The resulting map is injective, hence a bijection
    by cardinality.
13. **Ramsey's theorem** [5] is proved here (finite, `K`-uniform, two colours, by induction on `K` and `a + b`),
    since Mathlib has no version of it. `N` depends only on `K` and `M`, not on the type of identifiers.

## Constants (`main_theorem`)

14. `m = ⌈7(4T + 72)/ε⌉ + 2T + 3`, `ℓ = N((2T+1)², m²) + 1`, `r = (m + 1)ℓ`. The paper only says "sufficiently
    large `m` and `r`". The count uses `|A(G)| ≥ (r − ℓ)(m − 2T)² = ℓm(m − 2T)²` and `7|D*| ≤ rm² + 35rm`. For
    `ε ≥ 7` the claim is trivial, because the output is nonempty.
