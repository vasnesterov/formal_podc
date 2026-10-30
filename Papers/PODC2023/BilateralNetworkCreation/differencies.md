# Differences between the formalization and the paper

Paper: T. Friedrich, H. Gawendowicz, P. Lenzner, A. Zahn, *The Impact of Cooperation in Bilateral
Network Creation*, PODC 2023 (arXiv:2207.03798v2, numbering of the full version). Verdict rules: see
`.claude/skills/formalize-paper/verdicts.md`.

## Errors in the paper

1. **Lemma 2.4, explicit range in the proof (odd `n`).** The proof claims that `C_n` is in BSE for
   `(n+1)(n-1)/4 - (n-1) < α < (n+1)(n-1)/4` when `n` is odd. For `(n-1)²/4 < α < (n²-1)/4` the cycle
   is not in RE. Dropping an edge saves `α` and costs `n(n-1)/2 - (n²-1)/4 = (n-1)²/4`.
   `cycle_odd_not_BSE` proves this for every odd `n ≥ 3`; `C5_not_BSE` is the instance `n = 5`,
   `α = 5`, `M = 626`, with claimed range `(2, 6)`. The correct right end is
   `n(n-1)/2 - ⌊n²/4⌋` (`cycleHi`): `(n-1)²/4` for odd `n`, and `n(n-2)/4` for even `n`, which
   matches the paper. **Rule:** R1. The explicit range appears only inside the proof, and the lemma
   ("for some range of `α ∈ Θ(n²)`") is true (`lemma_2_4`), so this is a proof repair (🛠️).
2. **Lemma 2.4, other slips in the proof.**
   * `dist_{C_n}(u) = (n-1)(n-2)/4` for odd `n` should be `(n²-1)/4`; the bound derived from it uses
     the correct value.
   * "If every node in `G'` has degree 2, then `G'` is isomorphic to `C_n`" ignores disjoint
     unions of cycles. Those are disconnected and excluded by the penalty `M`.
   * In the path case, "one of its end nodes `u` must be part of the coalition" is unjustified: the
     end node may have lost its edge through its neighbour.
   We replace the case analysis by a uniform argument (`Levels.lean`). In a connected graph of
   maximum degree 2, a vertex of degree `c` has at most `c` vertices at each distance, so its
   distance cost is at least `⌊n²/4⌋` (`c = 2`), `n(n-1)/2` (`c = 1`) or `n(n-1)` (`c = 0`). Every
   coalition member is then not better off. A vertex of degree `≥ 3` in `G'` is necessarily in the
   coalition, and it pays `α` more while saving at most `⌊n²/4⌋ - (n-1)`.
3. **Lemma 3.5, case `α ≥ n/2`.** "The claim holds by definition of the 1-median" is false
   reasoning for `ℓ(u) ≥ 3`, since `|T_u| ≤ n/2 ≤ α` does not imply `|T_u| ≤ α/(ℓ(u)-1)`. The
   swap argument of the other case works for all `α`, and `lemma_3_5` uses it with no case split.
   **Rule:** R1, proof repair.
4. **Lemma 3.4, unproved step.** "For all `w ∈ T_u` with `ℓ(w) ≥ ℓ(v)+1` it holds that
   `|T_w| ≤ |T_u|/2`" is justified "by definition of the `T_u`-1-median". It follows from the
   component-size characterization of 1-medians that Section 3.2 states as "equivalent" without
   proof (`T_w` does not contain `v`, so it lies in one component of `T_u - v`). We prove it from
   the minimality of `v` (`two_mul_card_sub_le_of_subMedian`): otherwise moving from `v` to a
   child, or to the parent, of `v` lowers the distance cost within `T_u`. Note that `w` need not
   lie below `v`. Minor gap (R1, inside a proof).

## Modelling choices and imprecisions

5. **States are graphs.** As in the paper, a state is the created graph and an agent pays `α` per
   incident edge. Strategy vectors with unreciprocated requests are not modelled.
6. **Distance penalty `M`.** `d M G u v = M` for disconnected pairs, `M ∈ ℕ`. All theorems assume
   the paper's `M > α n³` together with the paper's standing assumption `α ≥ 1`. Without `α ≥ 1`,
   `M > α n³` does not make disconnection worse than every connected state (e.g. `n = 3`,
   `α = 0.01`, `M = 1`: a vertex of the triangle drops both edges). For `n = 3` the corrected range
   of Lemma 2.4 is `(0, 1]`, so with `α ≥ 1` only `α = 1` remains. **Rule:** R2/R4; not used anywhere
   in the paper's results.
7. **BSE needs a nonempty coalition** (`KBSE`). Literally, the empty coalition with the empty move
   satisfies "all members strictly benefit", and no graph would be in BSE. Evident intent (R3).
8. **`ρ` and the social optimum.** `optCost` is the infimum of the social cost over all graphs on
   `V`. The paper takes the optimum value `2(n-1)(α+n-1)` for `α ≥ 1` from [14]; we prove both
   bounds (`socialCost_ge`, `optCost_le_star`). Statements about `ρ` assume `n ≥ 2`; for `n = 1` the
   ratio is `0/0`. Degenerate (R2).
9. **1-medians.** A 1-median is a vertex of minimum distance cost (`IsMedian`), and a
   `T_u`-1-median minimizes `∑_{x∈T_u} d(v,x)` over `v ∈ T_u` (`IsSubMedian`). Distances in `T_u`
   equal distances in `G` because `T_u` is convex. We never use the paper's "equivalently, removal
   leaves components of size `≤ n/2`" as a definition; the needed consequences (`|T_u| ≤ n/2` for
   `u ≠ r`, `two_mul_card_sub_le`) are proved from minimality.
10. **Lemma 3.3** is stated for the minimizing `T_u`-1-median we construct. The paper picks, among
    two medians, the one closer to `u`; we pick `u` itself if it is a median, else any median. The
    conclusion is the paper's.
11. **Theorem 3.6** assumes `α ≥ 1` (the paper's standing assumption). For `α < 1` the bound
    `2 + 2 log α` is below 1 and false, since `ρ ≥ 1`. It also assumes `n ≥ 2` (degenerate
    otherwise). Trees are in RE because `M ≥ α + 1` (`tree_RE`).
12. **Lemma B.1 and Proposition A.2.** The paper invokes "RE = NE" (Prop. A.2). We prove only the
    direction used: in RE no agent gains by dropping any set of incident edges
    (`RE.cost_le_delAt`). The reason is that a shortest path from `v` uses one edge at `v`, so the
    distance increases are superadditive. The BFS tree is CSLib's `bfsParent`.
13. **Corollary 3.2.** The queue entry said `1 + n/α`; the paper says `ρ ≤ 1 + n²/α`, which is what
    we prove.
14. **Proposition 3.8: different proof.** We do not formalize Lemmas D.2, D.3, D.5, D.6 or the
    case analysis of the proof of D.7. Instead we prove the statements of Lemma D.4 (BAE) and
    Lemma D.7 (BSwE for `α ≥ 7kn`) for every tree whose subtree sizes depend only on the layer and
    halve every `k` layers (`LayerSized`, `LayerTree.lean`). The stretched binary tree satisfies
    this (`stretched_layerSized`).
    * Lemma D.4 holds already for `α ≥ 2kn` (paper: `5kn`).
    * BSwE: if both `u` and `w` gain, then `w` lies on `v`'s side `C_v`, `v` is strictly less
      central in `C_v` than `w`, and `|C_u| d(v,w) > α` (`swap_core`). The two orientations of
      `uv` are excluded by `caseA_contra` and `caseB_contra`.
    The paper's own proof of D.2–D.7 was not checked step by step.
15. **The stretched binary tree** is the explicit graph `stretchedTree d k` on
    `Σ ℓ : Fin (dk+1), Fin 2^⌈ℓ/k⌉`. Layer `ℓ` has `2^⌈ℓ/k⌉` vertices, and the parent of `(ℓ, j)` is
    `(ℓ-1, j/2)` at the start of a stretched segment and `(ℓ-1, j)` otherwise. This is isomorphic to
    the paper's construction, a complete binary tree of depth `d` with every edge replaced by a path
    of `k` edges; it is a tree with `(2^(d+1)-2)k + 1` nodes (`stretchedTree_isTree`, `card_SVert`).
16. **Proposition 3.9: explicit threshold.** "For sufficiently large `η`" becomes `η^γ ≥ 512` in
    `prop_3_9`, which follows the paper's proof. That threshold depends on `γ`, and so does the
    paper's proof (it needs `2k + 1 ≤ η/14` for `k = ⌈α/η⌉ ≈ η^(1-γ)`). The statement can also be
    read with `η₀` independent of `γ`; this reading is true as well (`prop_3_9_uniform`, for all
    `η ≥ 512`): if `η^γ < 512` then `25/32 + (γ/96) log₂ η < 1 ≤ ρ` (`one_le_rho`), and the
    complete binary tree (`k = 1`) with `η/42 ≤ n ≤ η/14` is in BGE by Proposition 3.8 since
    `7n ≤ η/2 ≤ α`. The tree in BGE is obtained for every `M > α n³`.
    * The proof uses Lemma D.8 in the form `t/3 ≤ n ≤ t` and `t < 2^(d+2) k`, i.e.
      `depth(B) > log(t/(4k))`, slightly stronger than the paper's `log(t/(6k))`
      (`exists_depth`).
    * The denominator is bounded by `15α/7` instead of `16α/7`.
    * The step "lower bound `n α/η` by `α/42`" needs `γ log η ≥ 9`, which follows from `η^γ ≥ 512`.
    * The upper bound `depth(T) ≤ k log t` of Lemma D.8 is not needed and not formalized.
17. **Lemma 2.4's right end** is included in our range (`α ≤ cycleHi n`); the paper uses strict
    inequalities. The theorem also requires `α ≥ 1`. `lemma_2_4` states the order of magnitude as
    `n²/8 ≤ cycleLo n` (for `n ≥ 8`) and `cycleHi n ≤ n²/4`, and asserts that admissible `α ≥ 1`
    exist for every `n ≥ 3`.
18. **Logarithms** are binary (`Real.logb 2`). The paper does not fix the base; base 2 is the
    standard convention and matches its halving arguments (Lemmas 3.4, D.8).
