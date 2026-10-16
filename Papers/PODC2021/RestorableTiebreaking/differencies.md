# Differences between the formalization and the paper

Bodwin–Parter, *Restorable Shortest Path Tiebreaking for Edge-Faulty Graphs*, PODC 2021,
arXiv:2102.10174v4 (numbering follows the arXiv version).

## Errors and imprecisions in the paper

1. **Definition 17 has no connectivity hypothesis.** *False only in a degenerate case.* Definition 17
   requires a replacement path for *all* `s, t` and all nonempty `F` with `|F| ≤ f`. If `F` disconnects `s`
   from `t` there is no replacement path. So no scheme is restorable on any graph in which some fault set
   with `|F| ≤ f` separates two vertices: any graph with a bridge when `f ≥ 1`, and any disconnected graph
   with at least one edge. As a consequence Theorem 19, read literally, is false (e.g. on `K₂`). Theorem 2 has the right hypothesis
   ("an `s ⇝ t` path remains in `G \ {e}`"), and we add it to Definition 17 (`IsRestorable`).
   Lean: `IsRestorableLiteral`, `not_isRestorableLiteral`, `theorem19_literal_false`.
2. **Corollary 22: the union bound miscounts the fault sets.** *A false intermediate claim; the corollary
   holds with a larger constant.* The proof bounds the number of choices of `s, t, F` by `n^{f+2}`. There
   are `n² · N_f` choices, where `N_f = #{F ⊆ E : |F| ≤ f}` can be as large as about `n^{2f}`. For `K₄` and
   `f = 1` there are `16 · 7 = 112 > 4³` choices with *ordered* pairs `(s, t)` (still `12 · 7 = 84 > 64`
   when `s ≠ t` is required; with unordered pairs `6 · 7 = 42`, but the count grows like `n^{2f+2}`
   anyway). So with `W = n^{f+4+c}` the paper's *union bound* only gives about `n^{f-c}`, not `n^{-c}`.
   Taking `W = n^{2f+4+c}`, or `c > f`, restores the claim, and the bit complexity is still `O(f log n)`.
   Lean: `paper_count_false`. `corollary22` proves the correct bound: the failure probability is at most
   `n² N_f |E| / (2W+1)`. The final arithmetic (`N_f ≤ n^{2f}`, choice of `W`, `O(f log n)` bits) is not
   stated in Lean.
3. **Theorem 23's proof picks the wrong minimum.** *Proof gap; the statement is true.*
   - The main gap: it takes "the edge in `π₁ \ π₂` with smallest ID". It should be the smallest ID in the
     whole *symmetric difference*; otherwise an edge of `π₂ \ π₁` with smaller ID can dominate.
   - Minor: it speaks of "distinct (not-necessarily-shortest) paths" and concludes that `π₂` is shorter,
     which ignores the lengths. Edges used by both paths in opposite directions contribute `±2r(e)`; this
     is harmless for `C` large enough.

   The argument is clean for *shortest* paths of `G \ F`, which have equal length and traverse common
   edges in the same direction (`IsShortestIn.dart_eq_of_edge_eq`). The first bullet of the proof already
   reduces to that case. We prove it this way (`coeff_of_ne`, `theorem23`), with `C = 2`.
4. **Theorem 20: the proof is fine (clarification only).** For `e ∈ q₁ \ q₂` the coefficient of `r(e)`
   in the weight difference is `±1` simply because `e ∉ q₂`, so "at most one value of `r(e)` makes
   `q₁, q₂` tie" is correct as written. Our Lean proof goes through the coefficient vector of the whole
   difference instead (`coeff_of_ne`, `volume_degenerate`, `theorem20`).
4a. **Corollary 22 applies the isolation lemma to signed weights without comment.** *Proof gap; the
   statement is true.* The weight of a path in `G*` is `∑ ±r(e)`, with the sign given by the direction in
   which the path crosses `e`. Applying Theorem 21 to the family of shortest `s ⇝ t` paths needs two
   facts the proof does not state:
   - all shortest `s ⇝ t` paths of `G \ F` cross each edge in the same direction, so each edge has one
     sign `τ(e)` for the whole family;
   - the weight distribution is symmetric under negation, so the signed weights `τ(e)·i(e)` are again
     uniform on `{−W,…,W}`.

   Lean: `cnt_eq_tau` and `tau` (common sign), and the sign flip `i ↦ τ·i` in `corollary22`.
5. **Theorem 21 (isolation lemma) needs distinct edge sets.** *Under-specified.* It is stated for "a set of
   paths `Π`". The paths must have pairwise distinct edge sets (a path and its reverse always tie). In the
   application all paths go from `s` to `t`, and distinct shortest `s ⇝ t` paths have distinct edge sets
   (`IsShortestIn.exists_mem_edges_not_mem`). Our isolation lemma (`Podc.Isolation.card_not_uniqueMin_le`)
   is stated for a family of sets.
6. **Theorem 30's proof uses the wrong `f`.** *Typo/slip.* It takes "a consistent stable restorable
   `f`-RPTS". For `f + 1` faults it needs an `(f+1)`-restorable `(f+1)`-RPTS whose `f`-fault overlays are
   stored, as in Theorem 31. Lean: `theorem30_correct`.
7. **Lemma 32's correctness proof misses a case.** *Proof gap; the statement is true.* It takes "the first
   and last clustered vertex" of the replacement path but does not treat paths without clustered vertices.
   Then every edge of the path is in `H`. Lean: `lemma32_correct`.
8. **Theorem 19's proof is terse but correct.** Two steps are left implicit, and we prove both:
   - The strict inequality "the `u ⇝ y` path through `v` is shorter than the one through `x`" needs
     `π(u,x) ∘ (x,y) ≠ π(u,y)`. Otherwise `π(s,x)` would contain `(u,v)`.
   - `(v,u) ∈ π(t,x)` forces `π(v,x) = (v,u) ∘ π(u,x)`, by consistency and the orientation of `e` along
     shortest paths from `t`.

   Lean: `restore_one`.
9. **Appendix B (Theorem 27) has several slips. Not formalized.**
   - `W : E → (1, 1 + 1/n²)`, but the bipartite weights are set to `(λ − j)/n⁴`. They should be
     `1 + (λ − j)/n⁴`.
   - The vertex `v*` is never defined.
   - `Label(z)` is undefined for the leaves of the last copy `G'_d` (the edge `(u_d, u_{d+1})` does not
     exist), at every level. Only about a `∏ₖ(1 − d^{-1/2^k}) ≥ 2^{-f}` fraction of the bipartite edges is
     forced. This only changes constants.
   - Observation 1(c) states `N(f,d) = 2^f d²` where `≤` is meant.
   - `W` does not break all ties: `z_j – x₁ – z_k` and `z_j – x₂ – z_k` have equal weight. So the scheme
     needs a further generic perturbation before it is a full consistent stable symmetric RPTS.

   A numerical check of the key claim, for `f ≤ 3` and small `d`, confirms that the corrected construction
   forces the expected bipartite edges (script below).
10. **Theorem 26 (cited from [9]) is not formalized; it has only a proof sketch.** It is the size bound
    behind Theorems 30, 31 and 33. `theorem31_of_theorem26` makes this dependence explicit. The case
    `f = 0` (a union of `|S|` trees) is proved unconditionally: `card_overlay_zero_le`, `theorem31_f0`,
    `theorem30`.

## Modelling choices and differences in the formalization

- **Graphs, faults, distances.** Graphs are finite `SimpleGraph V`. Fault sets are arbitrary
  `Finset (Sym2 V)`; non-edges are allowed and harmless, so the positive results are slightly stronger.
  Distances are `edist` (`ℕ∞`). A "shortest path of `G \ F`" is a walk of `G` that avoids `F` and has
  length `d_{G\F}`. Such walks are paths (`IsShortestIn.isPath`).
- **RPTS.** An RPTS is a function `F ↦ s ↦ t ↦ Option (G.Walk s t)`; `none` stands for "`∅`, no path".
  Definition 12 is required only for pairs connected in `G \ F`.
- **Consistency.** "`u` precedes `v` on `π(s,t)`" is formalized as a decomposition
  `π(s,t) = p₁ ++ q ++ p₂` with `q : u ⇝ v`. Then `π(u,v) = q`.
- **Definition 18 has two readings, and both are covered.** With possibly negative `r`, "unique shortest
  path of `G* \ F`" can mean the lightest *simple path* (`IsATWPath`) or the lightest *walk* (`IsATW`).
  We prove the readings are equivalent (`isATW_iff_isATWPath`). The simple-path reading already forces
  every closed walk of `G*` to weigh at least 2. So Theorem 19 holds for both (`theorem19`,
  `theorem19_path`).
- **Weights are indexed by unordered pairs.** We write `r(u,v) = sgn(u,v) · ρ({u,v})` with `ρ` indexed by
  *all* unordered pairs `Sym2 V`, not only by edges. In Theorem 20 the extra coordinates are independent
  and unused, so the distribution on the edge coordinates is the paper's. In Corollary 22 the isolation
  bound still only involves `|E|`.
- **Theorem 20 is stated as an almost-sure statement.** `ρ` is drawn from the uniform probability measure
  on `[-ε, ε]^{Sym2 V}` (`volume[|box V ε]`, a probability measure by `isProbabilityMeasure_box`). The
  hypothesis on `ε` is weakened: `(2n−1)ε < 1` suffices in `hasMinWalks_of_generic`.
- **Theorem 23 is stated for existence only.** It uses `C = 2`, with IDs `i(e) = N − id(e) ∈ {1,…,N}` for
  any numbering `id` of `Sym2 V`. The bit complexity and running-time claims are not formalized.
- **Corollary 22 is stated in counting form.** It counts bad draws `i ∈ {−W,…,W}^{Sym2 V}`. The running
  time is not formalized.
- **Theorem 2 is proved for all `f` simultaneously.** One scheme works for every `f` (`theorem2`).
  `theorem2_single` is the paper's one-fault phrasing.
- **Theorem 37 is proved in a stronger form.** Symmetry is assumed only for the non-faulty paths, and only
  the non-faulty paths need to be shortest.
- **Applications: correctness only, apart from the `f = 0` sizes.**
  - We formalize the correctness of Theorems 29, 30 and 31 and of Lemma 32.
  - Sizes are proved for `f = 0`: `≤ |S|(n−1)` edges and `≤ n−1` edges per label.
  - For larger `f`, sizes are conditional on Theorem 26.
  - Theorem 33 is reduced to its exponent arithmetic (`theorem33_exponent`). Its spanner size bound
    needs Theorem 26 and the expectation/Chernoff bound of Lemma 32, neither of which is formalized.
- **Not formalized.**
  - All running-time and bit-complexity statements: Theorems 3, 23, 28, 29 (runtime) and the label
    lengths in bits.
  - The CONGEST-model results: Theorem 8, Corollary 9, Lemmas 34–36, Theorem 35 (cited).
  - Theorem 25 (cited) and Theorem 27 (lower bound, Appendix B).
  - The Afek et al. restoration lemmas (Theorems 1 and 11; they are not used).

## Numerical check of Appendix B

Script: [`scripts/thm27.py`](scripts/thm27.py). It builds the graph
with the corrected weights and runs Dijkstra in `G \ Label(z_j)` for every leaf with a defined label. In
all tested instances every shortest `s ⇝ x_i` path is unique and ends with the edge `(z_j, x_i)`:

| f | d | χ | bipartite edges forced |
|---|---|---|---|
| 1 | 4 | 20 | 60 / 80 |
| 2 | 9 | 100 | 1600 / 2700 |
| 3 | 16 | 100 | 4500 / 12800 |

The unforced edges are exactly those at leaves with an undefined label.
