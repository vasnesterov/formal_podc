# Local Approximability of MDS on Planar Graphs — PODC 2014

Miikka Hilke, Christoph Lenzen, Jukka Suomela. *Brief Announcement: Local Approximability of Minimum Dominating
Set on Planar Graphs.* PODC 2014. DOI [10.1145/2611462.2611504](https://doi.org/10.1145/2611462.2611504).
Formalized version: arXiv [1402.2549](https://arxiv.org/abs/1402.2549) v1 (3 pages, complete proof); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** The main theorem holds as stated: no deterministic `T`-round LOCAL algorithm finds a
`(7 − ε)`-approximation of a minimum dominating set on planar graphs. The Ramsey argument of Lemma 1 and the
construction of Figure 1 work as described. The only imprecision is that the last step of the proof of Lemma 1
needs internal areas of at least `3 × 3`, while the lemma says "for any `m`". The paper fixes `m ≫ T` just before,
and the theorem takes `m` large anyway.

## Mistakes in the paper

* **Lemma 1, last step, degenerate case.** "The common output cannot be 0; otherwise there would be nodes that
  are not dominated" needs an internal node whose whole closed neighbourhood is internal, i.e. `m' = m − 2T ≥ 3`.
  For `m' ∈ {1, 2}` (and `T ≥ 1`) this inference fails *in `G` alone*: the boundary rows can dominate the internal
  nodes. Whether Lemma 1 itself still holds there depends on the reading of "radius-`T` neighbourhood". (a) If the view
  is the edges at distance `< T` plus the identifiers at distance `≤ T` (our model) or the induced radius-`T` ball, the lemma
  still holds: an internal node of `G` then has the same view as a deep interior node of a taller planar grid `H` on `n`
  nodes, so `c` is also the colouring of `H`. Every monochromatic set of size `(2T + 3)²` therefore has colour 1, and
  the Ramsey step with that size goes through. (b) If nodes also see the degrees of the nodes at distance `T`, the
  lemma fails for `m' = 1`: "output 0 iff your view is exactly that of the middle node of a `(2T+1)`-high strip"
  dominates every planar graph, and it puts no internal node of `G` into the output. In either case the paper has already fixed
  `m ≫ T` ("Pick sufficiently large `m ≫ T`"), so this is a minor gap in a degenerate case. The theorem is unaffected.
  We prove Lemma 1 under `2T + 3 ≤ m` (`lemma_1`). Our `lemma_1` assumes correctness only on relabellings of
  `G`. Under that weaker hypothesis Lemma 1 fails for `m' ∈ {1, 2}` already in model (a), via "join iff a horizontal border is
  visible at distance `< T`". Neither argument is formalized.
* Smaller points, all harmless: the graph `G` and the set `D*` are given only by Figure 1. The paper says `D*`
  contains 1/7 of the *internal* nodes, but it must also dominate the border of the whole grid; the bound
  `|D*| ≤ (1/7 + ε′)n` is right once these `O(rm)` extra nodes are added. Also, `ℓ = o(r)` can be taken as a
  constant `N(K, m²)` that does not depend on `r`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic LOCAL model with unique identifiers, extensional form (CSLib `Cslib.Local.IsLocal T`). The nodes of a
  network are its identifiers `Fin n = {0, …, n − 1}`. An algorithm is `A : SimpleGraph (Fin n) → Fin n → Bool`, and
  its output at `v` may depend only on the edges at nodes within distance `< T` of `v` and on the identifiers within
  distance `≤ T`. An algorithm that reads the whole induced radius-`T` ball is `(T + 1)`-local, so it is
  covered too, because the theorem holds for every `T`. There is no randomness and no failures. The algorithm may depend on `n` (`A n` in
  `no_local_approx_planar`); in `main_theorem` `n` is fixed and `A` is arbitrary for that `n`.
* The identifier space is exactly `{0, …, n − 1}`, the most restrictive choice. A lower bound for this choice
  implies the bound for any larger identifier space.
* Instances: `G = grid (r·m) m` is the `rm × m` triangulated grid: the triangular lattice `(x, y) ~ (x ± 1, y),
  (x, y ± 1), (x + 1, y + 1), (x − 1, y − 1)`. It has `r` blocks of `m × m` nodes side by side, as in Figure 1a.
  An instance is an identifier assignment `σ : GV W H ≃ Fin n`, and the network is `lab σ` (the grid relabelled by
  `σ`).
* Planarity: Mathlib has no planarity, so we use straight-line planar drawings (`IsStraightLinePlanar`: injective
  points in `ℝ²`, edges as segments meeting only at common endpoints, no vertex on a non-incident edge). By Fáry's
  theorem this is equivalent to planarity for finite graphs. We prove that every piece of the triangular lattice
  has such a drawing.
* The theorem is stronger than the paper's in two ways. In `main_theorem`, `A` only needs to be correct on the
  relabelled copies of one grid. The grid sizes `W`, `H` (and hence `n`) depend only on `T` and `ε`, not on `A`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Main theorem (abstract, Section 2), as stated | `no_local_approx_planar` | `Main.lean` |
| Main theorem, explicit form (`W`, `H` depend only on `T`, `ε`) | `main_theorem` | `Main.lean` |
| Lemma 1 (with `2T + 3 ≤ m`, `ℓ ≥ N(K, m²)`) | `lemma_1` | `Lemma1.lean` |
| Colouring `c(X)` of `K`-sets, monochromatic block ⇒ common output | `colour`, `out_internal` | `Lemma1.lean` |
| "Common output cannot be 0" | `common_output_true` | `Lemma1.lean` |
| Repeated Ramsey `Vᵢ`, `Yᵢ` | `rest`, `blockIds`, `blockIds_homogeneous`, `blockIds_disjoint` | `Lemma1.lean` |
| Identifiers of block `i` in increasing order by rows; `X_v` in increasing order | `asgEquiv`, `view_asg_internal` | `Blocks.lean` |
| Figure 1c: output depends only on the `k × k` region `R_v` | `out_eq_of_view_eq` | `Grid.lean` |
| Figure 1a: graph `G`, planarity | `grid`, `grid_isStraightLinePlanar` | `Grid.lean` |
| Figure 1b: `D*` | `dstar`, `dstar_isDominatingSet`, `card_dstar_le` | `Main.lean` |
| `|D| ≥ (1 − ε′)n` | `card_output_ge` | `Main.lean` |
| Ramsey's theorem [5] (hypergraph, finite) | `Cslib.exists_homogeneous` | `Podc/Foundations/Combinatorics/HypergraphRamsey.lean` |

In the explicit form we take `m = ⌈7(4T + 72)/ε⌉ + 2T + 3`, `ℓ = N((2T+1)², m²) + 1` and `r = (m + 1)ℓ`. Then
`|A(G)| ≥ ℓm(m − 2T)²` and `7|D*| ≤ rm² + 35rm`, which gives `(7 − ε)|D*| < |A(G)|`.

**Not formalized.** Fáry's theorem itself (equivalence of straight-line and topological planarity), and the
prose arguments about Lemma 1 for `m − 2T ≤ 2`.

**Trust.** No `sorry`. `main_theorem`, `no_local_approx_planar` and `lemma_1` use only the axioms `propext`,
`Classical.choice`, `Quot.sound`. Non-vacuity: the algorithm "every node joins" satisfies all hypotheses (the
`example` at the end of `Main.lean`). The locality notion comes from CSLib
(`Cslib.Computability.Distributed.Local.Locality`), and dominating sets from `Cslib...SimpleGraph.Ball`. Two new
CSLib candidates are staged in `Podc/`: `Podc/Foundations/Combinatorics/HypergraphRamsey.lean` (finite
hypergraph Ramsey theorem) and `Podc/Foundations/Combinatorics/SimpleGraph/StraightLineDrawing.lean`
(straight-line planarity, a planar drawing of the triangular lattice).
