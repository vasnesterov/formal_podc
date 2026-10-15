# A Tight Lower Bound for 3-Coloring Grids in the Online-LOCAL Model

Yi-Jun Chang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, Yu-Cheng Yeh. PODC 2024, pp. 106–116.
DOI [10.1145/3662158.3662794](https://doi.org/10.1145/3662158.3662794); full version arXiv
[2312.01384](https://arxiv.org/abs/2312.01384) (not needed: everything formalized here is fully proved in
the conference version; the local PDF is the ACM version).

**Status: complete for Theorems 1.1 and 1.3 and Lemmas 3.3–3.6. No `sorry`, no axioms beyond
`propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms` / `lean_verify`).**
Theorem 1.5 ((2k−2)-colouring k-partite graphs, only sketched in the paper) and Theorems 1.8/1.10
(proved only in the full version) are not formalized.

## Model (explicit assumptions)

Defined generally in `Cslib/Computability/Distributed/Local/OnlineLocal.lean` (now in CSLib), following §2.2 of the paper
(Akbari et al., ICALP 2023):

* **Deterministic** algorithms: `Algorithm ι L := View ι → L` (no randomness). Determinism makes
  adaptive and oblivious adversaries equivalent, so a lower bound only exhibits one bad input.
* **Identifiers.** Nodes are identified by elements of a type `ι`. For a host graph `G` on positions
  `V` (grid / cylinder / torus), an input is an identifier placement `pos : ι ≃ V`, i.e. the input
  graph is `G.comap pos`. The identifier space has exactly `n` elements (the paper allows
  `{1, …, poly(n)}`); this only *weakens* the adversary, so our lower bounds are stronger. The
  algorithm may depend on `n` and on `G` arbitrarily (all theorems quantify over all algorithms for
  fixed `m`, `T`).
* **Reveal order.** A list `σ` listing every identifier exactly once (`IsOrder σ`).
* **What the algorithm sees** when `vᵢ` is revealed: `view H T [v₁,…,vᵢ]` = the node set
  `B({v₁,…,vᵢ}, T)` (`ball`), the subgraph of `H` induced by it (with identifiers), and the sequence
  `[v₁,…,vᵢ]`. Its output is the label of `vᵢ` (`Algorithm.label`). Labels are never revised.
  This is exactly the paper's `Gᵢ = G[⋃ⱼ B(vⱼ, T)]` plus the global memory.
* **Correctness.** `A.Colors G T`: for every placement `pos` and every order `σ`, the labels form a
  proper colouring of `G.comap pos`.
* **Adversary power** = choice of `pos` and `σ`, nothing else. The paper's "re-embedding of
  not-yet-connected parts" is a *proof technique*, justified here by the indistinguishability lemma
  `label_eq_of_agreeOn` (if two inputs agree on all edges seen from the revealed nodes, all revealed
  nodes get the same labels) and realized by `exists_move` / `grid_exists_move`.
* **Non-vacuity.** `seeAll` (properly colour the whole discovered graph by a fixed choice function)
  is correct as soon as radius-`T` balls cover the graph (`seeAll_colors`): locality `2m` suffices on
  the `m × m` grid, `a + b` on the `a × b` cylinder/torus (`NonVacuity.lean`). So the model admits
  correct algorithms, and Theorem 1.3 is tight up to constants.
* Colours: `Fin 3 = {0,1,2}`; our colour `2` is the paper's colour `3`.

## Main results ↔ Lean

| Paper | Lean | File | Status |
|---|---|---|---|
| Online-LOCAL model (§2.2) | `ball`, `View`, `view`, `Algorithm`, `Algorithm.label`, `IsOrder`, `Algorithm.ProperOn`, `Algorithm.Colors` | `Cslib/Computability/Distributed/Local/OnlineLocal.lean` | definitions |
| indistinguishability / re-embedding | `label_eq_of_agreeOn`, `label_append`, `agreeOn_comap`, `agreeOn_of_fix`, `exists_move` | same | proved |
| grids, cylinders, tori (§2.1) | `grid a b = P_a □ P_b`, `cylinder a b = P_a □ C_b`, `torus a b = C_a □ C_b` | `Defs.lean`, `Theorem13.lean` | Mathlib's `pathGraph`, `cycleGraph`, `□` |
| Def 3.1 (a-value), Def 3.2 (b-value) | `aval`, `ind`, `bval` (walks), `S` (row paths) | `Defs.lean`, `BValue.lean`, `Rows.lean` | definitions |
| Lemma 3.3 | `aval_cell`, `bval_four_cycle` | `Defs.lean`, `BValue.lean` | proved |
| Lemma 3.4 | `grid_bval_closed` (every closed walk, not only simple cycles), via `grid_exists_potential` | `BValue.lean` | proved (no Jordan curve) |
| Lemma 3.5 | `bval_parity`, `bval_closed_parity`, `S_parity` | `BValue.lean`, `Rows.lean` | proved |
| (3.3) rows of cylinders/tori have equal b-values; odd rows have odd b-value | `rowSum_eq_of_reachable`, `rowSum_odd`, `rowSum_reflect` | `BValue.lean` | proved |
| Lemma 3.6 | `lemma36` (statement `Lemma36`), core step `choose_move` | `Lemma36.lean` | proved, segment length `< 2^k(2T+3)` |
| Thm 1.1 (explicit) | `theorem_1_1`: `2^(4T+5)(2T+3) ≤ m` ⇒ `¬ A.Colors (grid m m) T` | `Theorem11.lean` | proved |
| Thm 1.1 (`Ω(log n)`) | `theorem_1_1_log`: `A.Colors (grid m m) T` ⇒ `log₂(m²) < 12T + 14` | `Theorem11.lean` | proved |
| Thm 1.3 (cylinder) | `theorem_1_3_cylinder`: `4T+3 ≤ a`, `b ≥ 3` odd ⇒ `¬ A.Colors (cylinder a b) T`; `theorem_1_3_cylinder_square` (`m < 4T+3`) | `Theorem13.lean` | proved |
| Thm 1.3 (torus) | `theorem_1_3_torus`: `4T+4 ≤ a`, `b ≥ 3` odd; `theorem_1_3_torus_square` (`m < 4T+4`) | `Theorem13.lean` | proved |
| Cor 1.4 (Online-LOCAL part: `Θ(√n)`) | `torus_square_tight`, `cylinder_square_tight` | `NonVacuity.lean` | proved |
| non-vacuity for Thm 1.1 | `grid_colors_of_le`, `grid_bounds` | `NonVacuity.lean` | proved |
| Cor 1.2 (`Θ(log n)`), Cor 1.4 for other models | needs Akbari et al.'s `O(log n)` algorithm / model simulations | — | not formalized |
| Thm 1.5, Cor 1.6 | sketched only in the paper | — | not formalized |
| Thm 1.8, Thm 1.10, Cor 1.9, 1.11 | proofs only in the full version | — | not formalized |

## Proof structure

* `GridGeometry.lean`: balls in the simple grid are Manhattan balls (`mem_ball_grid`); moving a row
  piece by a column translation/reflection is invisible if it stays `T` away from the border and
  `2T+2` away from the rest (`grid_exists_move`).
* `Lemma36.lean`: induction on `k`. State = (revealed list, identifier placement). Build segment 1
  in `[a, a+s)`, segment 2 in `[a+s+2T+2, a+2s+2T+2)`, then move segment 2 (choosing orientation and
  gap `ℓ ∈ {2,3}` by `choose_move`, a purely combinatorial lemma on row colourings) and reveal the gap.
  The invariant is "if the segment is properly coloured, it contains a row path with `|b| ≥ k`".
* `Theorem11.lean`: `k = 4T+5`; Lemma 3.6 in row `T`; reveal the path above it in row `3T+2`, reflect
  it if needed; the rectangle has `b = 0` by the potential, but the vertical sides have `|b| ≤ 2T+2`.
* `Theorem13.lean` (generic `not_colors_of_rowLike`): reveal rows `T` and `3T+2`; reflect all rows
  `≥ 2T+2`; row sums are equal (cells), odd (Lemma 3.5) and negated by the reflection.

## CSLib candidates

* `Cslib/Computability/Distributed/Local/OnlineLocal.lean` (whole file): the Online-LOCAL model, `ball` API (`mem_ball_iff_walk`,
  `ball_union`, `ball_add`, `ball_comap_equiv`), `AgreeOn` + indistinguishability, `exists_perm_extend`
  (injective-on-a-set ⇒ permutation), `exists_move`, `completeOrder`, `seeAll` non-vacuity.
* `GridGeometry.lean`: `grid_adj_iff`, `mem_ball_grid` (Manhattan balls in `P_m □ P_m`).
* `NonVacuity.lean`: `ball_boxProd`, `ball_eq_univ_of_preconnected`; `Theorem13.lean`:
  `fst_mem_ball_boxProd`, `cycleGraph_adj_val`.
* `BValue.lean`: `grid_exists_potential` (3-colourings of grids have a "height" for the 1–2 edges) is a
  general combinatorial fact.

## Token spend

Roughly 0.8M tokens in total (main agent ≈ 0.65M, one subagent ≈ 0.15M for `BValue.lean`,
`Theorem13.lean`, `NonVacuity.lean`).
