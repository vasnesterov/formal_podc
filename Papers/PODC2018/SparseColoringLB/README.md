# Lower bounds for colouring sparse graphs — PODC 2018

Pierre Aboulker, Marthe Bonamy, Nicolas Bousquet, Louis Esperet. *Distributed Coloring in Sparse Graphs
with Fewer Colors.* PODC 2018. DOI [10.1145/3212734.3212740](https://doi.org/10.1145/3212734.3212740).
Formalized version: arXiv [1802.05582](https://arxiv.org/abs/1802.05582) v4; numbering follows it.
Only the lower bounds of §2 are formalized (Observation 2.4, Theorems 2.5, 2.6, 1.5).

**Verdict: ❌ False claim.** **Theorem 2.6 is false as stated for every odd `k ≥ 3`**: the `k × k` grid
*can* be 3-coloured (even 2-coloured) in `(k-1)/2 < k/2` rounds. The asymptotic statements (Ω(√n) for
planar bipartite graphs, Theorem 2.5, Theorem 1.5) are correct; we prove them with explicit constants,
Theorem 2.5 with exactly the paper's bound, and the non-colourability facts the paper cites (Gallai,
Fisk) for the graphs used.

## Mistakes in the paper

* **Theorem 2.6 is false for odd `k`.** "No distributed algorithm can 3-color the rectangular `k × k`
  grid in the plane in less than `k/2` rounds." Take `k = 2t + 1`. After `t` rounds a node knows how
  many nodes are at distance exactly `t` from it, and in the `(2t+1) × (2t+1)` grid this number
  determines `x + y mod 2`: with `a, b` the distances to the nearest horizontal and vertical side, it
  is `t + 1 + a + b` if `a + b < t` (values `≤ 2t`), `2(a + b) + 2` if `a + b ≥ t` and `a, b < t`
  (even values `≥ 2t + 2`), `2t + 1 + 2b` if `a = t > b` (odd values) and `4t` at the centre. So
  "output `0` or `1` according to this count" is a proper 2-colouring in `t < k/2` rounds. Already
  for `k = 3`: in one round a node knows its degree, and colouring by degree (2 and 4 vs 3) works.
  The algorithm is a genuine `t`-round LOCAL algorithm (CSLib's `IsLocal`), and ignores identifiers.
  It is designed for the grid, which the statement allows: like Observation 2.4, from which the paper
  derives it, Theorem 2.6 is about colouring one fixed graph under every identifier assignment (and nodes
  know `n = k²`). Under a stronger "uniform" reading (an algorithm correct on all planar bipartite graphs
  needs `k/2` rounds on the `k × k` grid) the counterexample does not apply; that reading is not settled here.
  The error costs one round: the asymptotic content (`Ω(√n)`) is unaffected.
  The correct bound from the paper's method is `2r + 3 ≤ k`, which we prove; for odd `k` it is tight.
  For even `k` the paper's bound `r < k/2` is neither proved nor refuted here. The "in particular"
  part (`Ω(√n)` rounds for planar bipartite graphs) is true. (`theorem_2_6_false_3`, …,
  `theorem_2_6_false_11`, `theorem_2_6_false_odd`; repaired: `theorem_2_6`)
* **Theorem 2.5: the proof does not give the stated bound; the statement is true.** The paper applies
  Observation 2.4 to `H = G_{5,2ℓ+1}` (Klein bottle) and `G = H_{2ℓ}`. But `G_{5,2ℓ+1}` has `10ℓ + 5`
  vertices, more than `H_{2ℓ}` (`10ℓ`), violating the hypothesis `|V(H)| ≤ |V(G)|`. And "balls of
  radius `< ℓ`" combined with Observation 2.4 (balls of radius `r + 1`) only gives `r ≤ ℓ - 2`. We
  prove the stated bound `r < ℓ` with the Klein bottle grid `G_{5,2ℓ}` (same size as `H_{2ℓ}`) and a
  sharper form of the indistinguishability argument: only the views of the two endpoints of each edge
  must be realised by one identifier assignment. (`theorem_2_5`)
* **Theorem 2.6: the proof, as written, gives less.** Balls of radius `< k` of `G_{2k+1,2k+1}` and
  Observation 2.4 give `r ≤ k - 2` for the `(2k+1)`-grid, i.e. `2r + 5 ≤ N` for side `N`; the sharp
  form of the same argument gives `2r + 3 ≤ N` (`theorem_2_6`), which is optimal for odd `N` by the
  first item.
* **Observation 2.4 is imprecise.** "Each ball of `H` is isomorphic to some ball of `G`" must be read
  with *rooted* isomorphisms (the centre must go to the centre), otherwise the argument fails. With
  that reading it is correct. (`observation_2_4`)
* Minor: Theorem 2.5 speaks of `H_k`, which is only defined for even `k` (Figure 2); Theorem 1.5's
  graph is only given by a picture ("versions … clearly exist"), we give an explicit family.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous LOCAL model, deterministic, unique identifiers: the node set of a network is the
  identifier type `V` with `|V| = n` (so `n` is known). An algorithm is `A : SimpleGraph V → V → β`
  (the colour output by each node); it is `r`-round (`BallLocal r A`) if a node's output only depends
  on the subgraph induced by its closed `r`-ball, identifiers included — the paper's own description.
  This gives nodes slightly more than `r` real rounds, so the lower bounds are slightly stronger; they
  transfer to CSLib's `Cslib.Local.IsLocal r` (`BallLocal.of_isLocal`). The counterexamples to
  Theorem 2.6 are `IsLocal` (genuine `t` rounds), hence also `BallLocal`.
* "`A` colours `Γ`" (`ColoursGraph`): proper for every bijective identifier assignment. Algorithms may
  be tailored to `Γ`. Class statements ("every planar … graph on `n` vertices") are formalized as: for
  every `r`-round algorithm on `n` identifiers, some `n`-node network of an explicit family (copies of
  `H_{2r+2}`, of the `(2r+3)`-grid, of a cut torus, plus isolated nodes) defeats it.
* Planarity is not formalized (no Mathlib notion); the explicit families are planar by their drawings
  (nested pentagons, grids, triangulated annuli).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Observation 2.4 (rooted balls) | `observation_2_4` | `Model.lean` |
| Sharp indistinguishability principle | `coloring_of_views`, `coloring_of_views_family` | `Model.lean` |
| Gallai: `G_{2k+1,2ℓ+1}` not 3-colourable (cited) | `klein_not_colorable` (odd `m ≥ 3`, any `n ≥ 2`) | `Klein.lean` |
| Theorem 2.5 (`H_{2ℓ}`, `r < ℓ`) | `theorem_2_5`; general `hGraph_not_colours` (`2r + 2 ≤ k`) | `Theorem25.lean` |
| Theorem 2.5, second sentence | `theorem_2_5_family` (`n ≥ 10(r+1)`) | `Theorem25.lean` |
| Theorem 2.6 (repaired: `2r + 3 ≤ k`) | `theorem_2_6`, `grid_not_colours` | `Theorem26.lean` |
| Theorem 2.6, second sentence | `theorem_2_6_family` (`n ≥ (2r+3)²`) | `Theorem26.lean` |
| Theorem 2.6 as stated: **false** | `theorem_2_6_false_3/5/7/9/11`, `theorem_2_6_false_odd` | `Theorem26Counterexample.lean`, `Theorem26General.lean` |
| Fisk: Figure 3 triangulation not 4-colourable (cited) | `torus_not_colorable` | `Torus.lean` |
| Theorem 1.5 | `theorem_1_5` (`n ≥ 6r + 10`) | `Theorem15.lean` |

`klein_not_colorable` is the winding-number argument (edge slopes `±1` in `ℤ/3`, face sums `0`, the
twisted gluing reverses the column cycle). `torus_not_colorable` is Fisk's parity argument for the
3-row triangulations, as a transfer argument: the colourings of a column triangle fall into 6 classes
that consecutive columns preserve and the defect changes. For Theorems 2.5, 2.6 and 1.5 the planar
graph and the non-colourable graph live on the same vertex set and differ only by a few "seam" edges
(the twisted edges of the Klein bottle, the cut of the torus); an automorphism or a choice of the
seam puts it far from the edge being looked at (`ballAgree_of_le`).

**Not formalized.** The algorithmic part (Theorem 1.3, §3–§6) and its corollaries; planarity; the
upper bound of Gallai's theorem; Fisk's theorem in general (only for our family).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Finite checks use `decide` / `decide +kernel`. The counterexamples exhibit algorithms,
so the model is not vacuous. The LOCAL view notions come from CSLib
(`Cslib/Computability/Distributed/Local/Locality.lean`: `GAgree`, `IsLocal`).
