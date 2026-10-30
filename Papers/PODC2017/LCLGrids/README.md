# LCL Problems on Grids — PODC 2017

Sebastian Brandt, Juho Hirvonen, Janne H. Korhonen, Tuomo Lempiäinen, Patric R. J. Östergård,
Christopher Purcell, Joel Rybicki, Jukka Suomela, Przemysław Uznański. *LCL Problems on Grids.*
PODC 2017. DOI [10.1145/3087801.3087833](https://doi.org/10.1145/3087801.3087833). Formalized
version: arXiv [1702.05456](https://arxiv.org/abs/1702.05456) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The 3-colouring lower bound (Theorem 9) holds, with
`n ≤ 8T + 8` for every odd `n`. So do its ingredients: Theorem 10 (`q`-sum coordination is
global) and Lemmas 12–14 (the parity invariant `s`). Theorem 21 (no edge `2d`-colouring for odd
`n`) and Lemma 24 (no `{1,3}`-orientation for odd `n`) hold too. One statement is wrong as
written: the third case of Theorem 22 claims that "no solution exists for infinitely many `n`",
but `{0,3,4}`-orientations exist for every `n ≥ 3`. The problem is still global (Theorem 25), so
only the stated reason is wrong.

## Mistakes in the paper

* **Theorem 22, third case: solutions do exist.** Theorem 22 classifies `X`-orientations: if
  `2 ∉ X`, `{1,3,4} ⊄ X` and `{0,1,3} ⊄ X`, it claims that "no solution exists for infinitely many
  `n`". The set `X = {0,3,4}` falls in this case, yet every `n × n` torus with `n ≥ 3` has a
  `{0,3,4}`-orientation. The same holds for `{0,1,4}`, by reversing all edges. The construction
  is invariant under the diagonal shift `(x, y) ↦ (x+1, y+1)`. Diagonal `k` gets a value `t_k`:
  how many of the two edges between diagonals `k` and `k+1` point to `k+1`. A node then has
  in-degree `2 − t_k + t_{k−1}`. The cyclic sequence `t = 0,2,0,2,…,0,2` (even `n`) or
  `0,2,…,0,2,1` (odd `n`) only produces in-degrees 0, 3 and 4. The classification itself is
  right: the paper proves separately that `{0,3,4}` is global (Theorem 25, via `q`-sum
  coordination), and the introduction says "otherwise it is global". This is an imprecise
  statement with evident intent, not a wrong complexity
  (`exists_orientation034`, `theorem22_third_bullet_false`).
* **Slips that do not affect any statement.** In the proof of Theorem 10,
  `d = A(F₁X₂F₂) − A(F₁X₂F₂)` should be `A(F₁X₂F₂) − A(F₁X₁F₂)`. "The conditions in Section 10"
  means those of Theorem 10. The proof of Lemma 14 swaps the coordinate names. The greedy
  post-processing before the reduction is unnecessary, because Lemmas 12–14 hold for every proper
  3-colouring. Lemma 13's bound `T < n/4` ignores the `O(1)` extra radius needed to read `ℓ`, as
  the paper's conventions allow; we prove it with `4(T+2) ≤ n`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Network.** The oriented toroidal `n × n` grid `ZMod n × ZMod n`. Nodes know `n` and which edge
  points north, east, south or west. They have unique identifiers in `[0, B)`.
* **Algorithms.** Deterministic LOCAL: a `T`-round algorithm is a map from the identifiers on the
  radius-`T` ball `{d : |d₁| + |d₂| ≤ T}` around a node to its output (`GridLocal`). Thanks to
  the orientation this is exactly a node's `T`-round knowledge. The lower bound only assumes
  correctness for identifiers in `[0, 8n²)`, so it holds for every identifier range of size at least `8n²` (eight times the number of nodes), in particular for the usual `poly(n)` ranges.
* **Directed cycles (`q`-sum).** Same model on directed `n`-cycles, with identifiers in `[0, 7n)`
  (`QSum.IsLocal`, `QSum.Solves`).
* **Combinatorial results.** Theorem 21 and Lemma 24 use the `d`-dimensional torus
  `torusGraph d n`, Mathlib's line-graph colourings and CSLib's `SimpleGraph.Orientation`.
* **What we prove differently.** Theorem 10 has a new, shorter proof with a better constant: for
  `8T < n`, any constant output sum `Q` on `n`-cycles must be a multiple of `n` (`sum_eq_mul`).
  Lemmas 12–14 are proved for every proper colouring by finite `3 × 3` block checks (`decide`) and
  flux counting, instead of a cycle decomposition of `H`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 9 (3-colouring is `Ω(n)`; `n ≤ 8T + 8` for odd `n`) | `theorem9`, `theorem9_not_isLittleO` | `Theorem9.lean` |
| Theorem 10 (`q`-sum coordination is `Ω(n)`; `n ≤ 8T`) | `QSum.theorem10`, `QSum.theorem10_of_solves`, `QSum.sum_eq_mul` | `QSum.lean` |
| Lemma 12 (`i_r(C)` independent of `r`) | `lemma12`, `crossing_eq_of_rows` | `Lemma12.lean` |
| Corollary of Lemma 12 (`s` independent of the row) | `rowSum_eq` | `Invariant.lean` |
| Lemma 13 (`s` independent of the identifiers) | `lemma13` | `Lemma13.lean` |
| Lemma 14 (`s` odd for odd `n`; `|s| ≤ n/2`) | `odd_rowSum`, `rowSum_cast_two`, `two_mul_abs_rowSum_le` | `Invariant.lean` |
| Structure of `H` (Figure 5) | `indeg_eq_outdeg`, `ell_eq`, `ell_ne_zero_iff` | `Basic.lean` |
| Theorem 21 (no edge `2d`-colouring, `n` odd) | `not_edgeColouring_torus` | `EdgeColouring.lean` |
| Lemma 24 (no `{1,3}`-orientation, `n` odd) | `not_exists_oneThreeOrientation_torus` | `Orientation.lean` |
| Theorem 22, third case (false) | `exists_orientation034`, `theorem22_third_bullet_false` | `Orientation034.lean` |

**Not formalized.** The classification theorem and the speed-up to `O(log* n)` (Theorem 2), the
undecidability result (Theorem 3), the normal form and synthesis, the upper bounds (Theorems 4
and 15, Lemma 23), Theorem 25, and the `d`-dimensional 3-colouring lower bound.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity checks:
* `globalAlg` (`NonVacuity.lean`) is a `2n`-round algorithm that properly 3-colours every odd
  torus. So the hypotheses of Theorem 9 are satisfiable, and `n ≤ 8T + 8` is tight up to a
  constant factor.
* `torus44_edgeColourable` shows that edge `2d`-colourings exist for even `n`.

The model is self-contained (Mathlib); orientations come from CSLib
`Cslib.Foundations.Combinatorics.SimpleGraph.Orientation`. CSLib candidates (marked
`-- CSLib candidate`):
* `QSum.lean`: LOCAL on directed cycles and the `q`-sum lower bound;
* `torusGraph`;
* `even_card_of_lineGraph_coloring`;
* `two_mul_sum_inDeg`;
* `orientationOfFwd` and `inDeg_orientationOfFwd`: orientations of `(ℤ/n)^d` given by a
  "forward" predicate (`Orientation034.lean`).
