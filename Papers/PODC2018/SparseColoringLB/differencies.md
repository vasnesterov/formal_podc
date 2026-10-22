# Differences between the formalization and the paper

Paper: Aboulker, Bonamy, Bousquet, Esperet, *Distributed Coloring in Sparse Graphs with Fewer Colors*,
PODC 2018; arXiv 1802.05582v4 (numbering as there). Only the lower bounds of §2 (Observation 2.4,
Theorems 2.5, 2.6, 1.5) are formalized; the algorithm of Theorem 1.3 (§3–§6) is not.

## Model

1. **LOCAL model.** An algorithm on `n`-node networks is a function `A : SimpleGraph V → V → β`,
   `|V| = n`: node names are the identifiers (the paper: identifiers in `{1, …, n}`, `n` known — here
   `V` is any type with `n` elements, so `n` is known). It is `r`-round (`BallLocal r A`) if the output
   of a node only depends on the subgraph induced by its closed ball of radius `r`, with identifiers
   (`BallAgree`). This is the paper's own description ("the output of each vertex `v` only depends on
   the labelled ball of radius `r`"). It gives the nodes slightly more information than `r`
   synchronous rounds really do (edges between two nodes at distance exactly `r`), so our lower bounds
   are (slightly) stronger than lower bounds for genuine `r`-round algorithms; `BallLocal.of_isLocal`
   transfers them to CSLib's `Cslib.Local.IsLocal r` (genuine `r` rounds), and
   `BallLocal.isLocal_succ` shows `BallLocal r ⊆ IsLocal (r + 1)`.
2. **"`A` colours `Γ`"** (`ColoursGraph`): for *every* bijective identifier assignment `W ≃ V`,
   adjacent nodes output different colours. The algorithm may depend on `Γ` (it is only required to
   work on copies of `Γ`), which makes "no algorithm colours `Γ`" stronger than needed.
3. **Class statements** ("no algorithm can 3-colour every planar triangle-free graph on `n` vertices
   in `o(n)` rounds", etc.): formalized as "for every `r`-round algorithm on `n` identifiers there is
   an `n`-node network of an explicit family on which it fails", with explicit constants instead of
   `o(·)`. The networks are copies of an explicit graph (`H_{2r+2}`, the `(2r+3)×(2r+3)` grid, a cut
   torus `cutTorus (2r+3) c`) **plus isolated nodes** (`IsCopyOf`), so they are disconnected when `n`
   is larger than the explicit graph. Adding isolated vertices keeps planarity, triangle-freeness and
   bipartiteness.
4. **Planarity is not formalized** (Mathlib has no planarity). The explicit families are planar by
   their drawings: `H_k = C₅ □ P_k` is `k` nested pentagons (Figure 2, right); grids; `cutTorus w c`
   is a triangulated annulus (`w + 1` nested triangles, each consecutive pair joined by a
   triangulated band). Triangle-freeness of `H_k` and bipartiteness of the grid are likewise not
   stated in Lean. The theorems are therefore literally about these explicit families.

## Observation 2.4

5. The paper says "each ball of radius at most `r + 1` in `H` is isomorphic to some ball of radius at
   most `r + 1` in `G`". As stated (unrooted isomorphisms) this is not enough for the argument; we
   assume **rooted** isomorphisms of the subgraphs induced by the balls of radius `r + 1`
   (`observation_2_4`). The conclusion is formalized as: an `r`-round algorithm colouring `G` with
   colours `β` yields a colouring of `H` with colours `β`.
6. The proofs of Theorems 2.5, 2.6, 1.5 do **not** go through Observation 2.4 but through a sharper
   form of the same indistinguishability argument (`coloring_of_views`, `coloring_of_views_family`):
   it suffices that the radius-`r` views of the **two endpoints of each edge** of `H` are realised
   simultaneously by one identifier assignment of `G`. This is what gives the paper's bound in
   Theorem 2.5 (see 8).

## Theorem 2.5 (`H_k`)

7. `H_k` is only drawn for `k = 2ℓ` (Figure 2); we define `H_k = C₅ □ P_k` for all `k`.
8. **The paper's proof does not give the stated bound** (statement true). The paper applies
   Observation 2.4 with `H = G_{5,2ℓ+1}` (Klein bottle) and `G = H_{2ℓ}`. (a) `G_{5,2ℓ+1}` has
   `10ℓ + 5` vertices, more than `H_{2ℓ}` (`10ℓ`), so the hypothesis `|V(H)| ≤ |V(G)|` fails.
   (b) "Balls of radius `< ℓ`" with Observation 2.4 (radius `r + 1`) give only `r ≤ ℓ - 2`, not
   `r < ℓ`. We prove the stated bound `r < ℓ` exactly (`theorem_2_5`), with `klein 5 (2ℓ)`
   (same size as `H_{2ℓ}`) and the edge-view argument (6), and more generally `2r + 2 ≤ k`
   (`hGraph_not_colours`; for odd `k` this is `r < (k-1)/2`, the odd case is not claimed by the paper).
9. Second sentence: with explicit constants, `n ≥ 10(r + 1)` ⇒ the algorithm fails on `H_{2r+2}`
   plus isolated nodes (`theorem_2_5_family`), i.e. `r ≥ n/10 - 1` is needed.

## Theorem 2.6 (grid)

10. **The first sentence is false for every odd `k ≥ 3`.** "No distributed algorithm can 3-colour the
    `k × k` grid in less than `k/2` rounds": for `k = 2t + 1`, `t < k/2` rounds suffice, even for a
    proper 2-colouring, in genuine `t`-round LOCAL (CSLib `IsLocal t`): a node counts the nodes at
    distance exactly `t` (or the whole distance profile up to `t`), which determines `x + y mod 2`.
    Lean: `theorem_2_6_false_odd` (every odd `k = 2t + 1`, using only the number of nodes at
    distance exactly `t`; `Theorem26General.lean`), and the instances `theorem_2_6_false_3`, …,
    `…_11` by kernel computation. The counterexample refutes the statement in the paper's own sense
    (a fixed graph, every identifier assignment, as in Observation 2.4 and item 2; nodes know
    `n = k²`); the algorithm is tailored to the grid. A stronger "uniform" reading (an algorithm that
    3-colours every planar bipartite graph needs `≥ k/2` rounds on the `k × k` grid) is not refuted
    by it and is not addressed here. The error is one round in an exact bound; the `Ω(√n)` content stands.
11. What the paper's argument proves, in its sharp form, is `2r + 3 ≤ k` (`theorem_2_6`, via
    `grid_not_colours` with the Klein bottle grid `klein m m`, `m` the largest odd number `≤ k`). For
    odd `k` this is tight by 10. For even `k` the paper's bound `2r + 2 ≤ k` remains open here (neither
    proved nor refuted; the Klein-bottle argument cannot give it, since it needs an odd side `≥ 2r + 3` and
    at most `k²` vertices). The paper's own bookkeeping (balls of radius `< k` in `G_{2k+1,2k+1}`,
    Observation 2.4 with radius `r + 1`) gives only `r ≤ k - 2` for the `(2k+1)`-grid.
12. Second sentence (`o(√n)` for planar bipartite graphs): `n ≥ (2r + 3)²` ⇒ the algorithm fails on the
    `(2r+3) × (2r+3)` grid plus isolated nodes (`theorem_2_6_family`). True as stated.

## Gallai's theorem (cited)

13. The paper cites Gallai: `G_{2k+1,2ℓ+1}` is 4-chromatic. We prove only the needed half,
    `χ > 3`, but for all odd `m ≥ 3` and **all** `n ≥ 2` (`klein_not_colorable`; winding-number
    argument). The upper bound `χ ≤ 4` is not formalized. Our Klein bottle grid glues
    `(i, n-1) ~ (-i, 0)` (reflection `i ↦ -i` of `ℤ/m`).

## Theorem 1.5 and Fisk's theorem

14. The triangulation of Figure 3 is given only as a picture ("versions of this graph on `n` vertices
    clearly exist for any `n ≡ 1 (mod 3)`"). We define an explicit family `torus w` (`3w + 1`
    vertices: rows of lengths `w + 1, w, w`; all degrees 6 except `4, 7, 7`, the two degree-7
    vertices adjacent) matching the figure up to drawing. That it is a triangulation of a closed
    surface (every edge in exactly two of the `6w + 2` triangular faces, links are cycles) and the
    degree pattern were checked numerically for `3 ≤ w ≤ 8`, not in Lean; they are not needed.
15. Fisk's theorem is cited, not proved, in the paper. We prove non-4-colourability of `torus w`
    directly (`torus_not_colorable`, all `w ≥ 2`) by Fisk's parity argument specialised to this
    family: a transfer argument over the 24 proper colourings of a column triangle, with a 6-class
    invariant preserved between consecutive columns and changed across the defect (finite checks by
    `decide`). The general Fisk theorem is not formalized.
16. Instead of "balls of radius `≤ (n-1)/6 - 3` are planar" + Observation 2.4, we compare `torus w`
    with the cut tori `cutTorus w c` (delete the edges between columns `c` and `c + 1`, choose `c`
    opposite to the edge). Constant: `n ≥ 6r + 10` suffices (`theorem_1_5`), i.e. 4-colouring all
    `n`-vertex planar graphs needs `r ≥ (n - 10)/6` rounds, slightly better than the paper's
    `(n-1)/6 - 4`.

## Not formalized

17. Theorem 1.3 (main algorithm) and its corollaries, Corollary 2.1, Proposition 2.2, Corollary 2.3,
    Theorems 2.10, 6.1, §3–§6; Linial's lower bounds (cited); the upper bound of Gallai's theorem.
