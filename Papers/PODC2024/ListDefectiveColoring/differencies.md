# Differences between the formalization and [FK24] (arXiv 2405.04648v1)

## Issues in proofs and constructions (with Lean counterexamples)

No stated theorem of the paper is refuted. The three items below are an error in a definition used by an
algorithm, a gap in a proof's construction, and an error in a proof.

1. **Section 4.1, eq. (10)/(11): floor/ceiling slip in the modified defect function.**
   * **What the paper says.** It defines `d'_v(x) := ⌊(d_v(x)+1)/(7θ)⌋ − 1` and states that `d'` is
     non-negative and that `∑(d'+1) ≥ (1/7θ)∑(d+1)`.
   * **Why it fails.** Both statements are false whenever `d_v(x) < 7θ − 1`: then `d' = −1`, and the floor goes
     the wrong way for (11).
   * **Consequence.** With negative `d'` no colour ever satisfies (12). Every `L_{v,i}` and every `H_i` is
     empty, so the Section 4.1 algorithm as defined colours no node.
     * This happens for every colour with `d < 7θ − 1`, including every proper list colouring instance
       (`d ≡ 0`). It is not a degenerate case.
   * **Counterexample** (`Section41Counterexample.lean`). Take the triangle `K₃`: its maximum degree is 2, so
     `Δ = 2` needs no convention. Take `θ = 1`, `S = 1`, `d ≡ 0` and 85 colours per list. This satisfies the
     paper's slack `42θ log₂Δ·S` and the corrected eq. (9).
     * `theorem_1_4_paper_defects_false` and `lemma_4_2_fails`: no node is ever coloured.
     * `eq11_fails`: `∑(d'+1) = 0 < 85/7`.
     * `isRun_ce`: a run exists, so the statement is not vacuous.
   * **Fix.** `d' := ⌈(d+1)/(7θ)⌉ − 1 = ⌊d/(7θ)⌋` (`Sec41.dPrime`). It is non-negative, as the paper intends,
     with `∑(d'+1) ≥ ∑(d+1)/(7θ)` and `7θ d' ≤ d`. Theorem 1.4 then holds (`Sec41.theorem_1_4`).
2. **Lemma 4.5 (colour space reduction): gap in the proof's construction, trivial fix.**
   * **What the paper says.** The subspace-choice instance gives every node *all* `p` subspaces.
   * **Why it fails.** A node may choose a subspace `C_i` with `L_v ∩ C_i = ∅`, because `d_{v,i} = 0` is not
     violated when no neighbour chooses `i`. The node is then left with an empty list, and its sub-instance has
     no solution. The slack chain also divides by `deg(v)`, which may be `0`.
   * **Counterexample** (`ColorSpace.paper_counterexample`): one isolated node, `L = {0}`, two subspaces,
     `ψ ≡ 1`.
   * **Fix.** Give a node only the subspaces that meet `L_v` (`lemma45`). The slack bound
     `∑_i (d_{v,i}+1) > σ deg(v)` survives because `L_v ≠ ∅`.
   * The lemma's round-time statement (17) is not refuted.
3. **Lemma A.1: genuine error in the proof (existence of a colouring unaffected).**
   * **What the paper says.** `H_i` is the set of nodes with `≤ Δ/2` coloured neighbours. The proof claims
     `∑_{L'}(d'+1) > deg(v) − deg~(v) ≥ Δ − Δ/2 ≥ µ deg_{G_i}(v)`.
   * **Why it fails.** The step `deg(v) − deg~(v) ≥ Δ − Δ/2` fails for nodes of degree `< Δ`.
   * **Counterexample** (`SlackReduction.paperA1_counterexample`): 15 nodes, `Δ = 6`, `µ = 2`, `ε = 1/4`.
     * Node `v` has degree 4, 3 coloured neighbours and 1 neighbour in its class.
     * Its residual weight is `2 = µ·deg_{G_i}(v)`, so the sub-instance does not have slack `µ`.
     * It still has slack 1, so the round-complexity argument breaks, not the existence of a colouring.
   * **Fix** (`lemmaA1`, `lemmaA1_halving`, `two_pow_le_of_halving`).
     * Test `deg~(v) ≤ r(v)/2`, where `r(v)` is the residual degree at the start of the phase.
     * Take the defective colouring relative to the residual graph.
     * Per-node residual degrees then halve in every phase, giving `O(log Δ)` phases.

## Gaps in proofs (results correct; fixed in the formalization)

* **Lemma 3.1, case `|L_v| > p`.**
  * **The flaw.** The final pigeonhole step bounds `|N_>(v)| + ∑_{x∈S_v} k_v(x)` by the average over all
    `p`-subsets and then by `∑_{x∈L_v}(d_v(x)+1)`. That does not give (4), whose right-hand side is
    `∑_{x∈S_v}(d_v(x)+1)`.
  * **Correct argument.** Average the *difference* of the two sides of (4) over all `p`-subsets. Equivalently, a
    best subset is at least as good as the average (`IsBestSubset.mul_sum_le` with `sum_powersetCard_sum`).
    This also proves the Remark: the subset chosen by Algorithm 1 satisfies (4).
  * **What we prove.** Lemma 3.1 is true (`lemma_3_1`, `IsBestSubset.lemma_3_1`).
* **Lemma 3.2.**
  * The text "some colour `x_v` such that `r_v(x_v) + k_v(x_v) ≤ |N_>(v)| < d_v(x_v) + 1`" is garbled (and
    "`l'_v`" is a typo for `S_v`).
  * The correct step is a pigeonhole on sums: if every `x ∈ S_v` had `k + r ≥ d + 1`, summing would contradict
    (6) (`exists_phaseII_color`).
* **Section 4.1, setup of Lemma 4.2.** The paper writes `deg~(v,i) ≤ ∑_x a_v(x,i)`. The proof needs the reverse
  inequality, which is the true one: neighbours with colours outside `L_v` exist.
* **Eq. (9) omits the factor `deg(v)`.** It must read `∑(d+1) > 21θ(⌈log Δ⌉+1)S·deg(v)`, as in Definition 1.1
  and in the theorem statement.
* **Lemma 4.2's proof needs `d' ≥ 0`.** This holds only for the corrected `d'`. The pigeonhole over iterations
  can be replaced by summing the per-iteration bound `∑_{L_{v,i}}(d'+1) ≤ 2S deg(v)`.
* **Lemma 4.3 is stronger than stated.**
  * Claim 4.1's argument applies directly to `W_j = {u ∈ N(v) | u coloured with x in iteration j}`. The
    auxiliary graph `G_{x,j}(v)` is not needed.
  * `∑_{j≤i}(2d_j+1) = 2^{i+2} − i − 3 ≤ 4d_i` for `i ≥ 1`, so `X_v ≤ 4θ d'_v(x)`
    (`Sec41.lemma_4_3_sharp`). The constant 7 in (10), and the 21/42 in the slack, could be 4 and 12/24.
* **Theorem 1.4, w.l.o.g. assumption.**
  * The paper's "w.l.o.g. `d_v(x) ≤ Δ`" (p. 18) is a hypothesis (`hdΔ`). The reduction to this case is not
    formalized.
  * The step from the slack `42θ log₂Δ·S` to `21θ(⌈log₂Δ⌉+1)S` is proved (`clog_add_one_le_two_logb`, via
    `2^{⌈log Δ⌉+1} ≤ Δ²`).
* **Theorem 1.2, round count (remark, not formalized).**
  * The paper's argument as written combines Lemma 3.5 (time `O(T(4)·⌈log₄ C⌉)`) with
    `T(4) = O(log²C + log* q)`. That gives `O(log³C + log C · log* q)`, not the claimed `O(log³ C + log* q)`.
  * The reason is that the defective colouring of Lemma 3.4 depends on the current out-degrees and is recomputed
    at each of the `⌈log₄ C⌉` levels. We have not checked whether it can be shared across levels.
  * Minor: for `C = 1`, `ε = 1/(3·0)` is undefined. Lemma 3.5 assumes "`≥`" while Theorem 1.1 gives "`>`"
    (harmless).
* **Lemma A.1, round count (remark, not formalized).** As written, every phase recomputes Lemma 3.4. That
  would give `O(log Δ · log* q)` rather than `+O(log* q)`.
* **Lemma 4.5, hypotheses.** Only `σ > 0` (and `S ≥ 0`) is used, not `1 ≤ σ`.

## Modelling choices and minor differences

* **Conventions of Section 2.** The paper defines `Δ(G) = max(2, maxdeg)`, so `Δ ≥ 2` is a hypothesis of
  `Sec41.theorem_1_4`. For `Δ = 1`, `⌈log Δ⌉ = 0` and the bound `d ≤ 2d_0 = 0` would fail.
  * The paper also defines `β_v = max(1, outdeg)`, and we use this (`beta`).
  * The statements of Theorems 1.1 and 1.2 say "`β_v` is the outdegree of `v`". This is inconsistent with
    Section 2.
  * With the literal outdegree, an isolated node with an empty list would satisfy the hypothesis of
    Theorem 1.2.

* **Out-neighbourhoods.** They are arbitrary finite sets of `G`-neighbours, not necessarily an orientation.
  * The initial colouring only has to be proper along out-edges. This is strictly more general.
  * Section 1.1's list defective 3-colouring corollary needs `out v = N(v)`, which is not an orientation.
* **Colours.** Initial colours are naturals `< q` instead of `{1,…,q}`. List colours have an arbitrary type `α`
  with decidable equality instead of `ℕ`.
* **Algorithm 1, line 4.** "Sort by `d − k` and take the first `p`" is modelled as an arbitrary best
  `min(p,|L_v|)`-subset (`IsBestSubset`). `isBestSubset_take` proves that the sorted prefix is one, so every
  tie-breaking of the sort is covered.
* **Distributed model.** CSLib's synchronous SET-LOCAL round model, with identifiers and local inputs in the
  states.
  * Phase I uses rounds `0..q-1` and Phase II rounds `q..2q-1`, so there are exactly `2q` rounds. The paper says
    `O(q)`.
  * Message sizes (Lemma 3.3: lists of `p` colours, then one colour) are in docstrings only.
* **Theorem 1.1, `ε > 0`.**
  * Lemma 3.4 ([Kuh09, KS18]) is not formalized. Its output, a colouring `Ψ` with `K` colours and at most
    `⌊ε β_v/p⌋` same-colour out-neighbours, is a hypothesis of `fastTwoSweep_correct`.
  * Lemma 3.4 needs `α = ε/p ≤ 1`, which Algorithm 2 leaves implicit.
  * "Let `ε > 0` be an integer" (p. 13) is a typo: `ε` is real.
  * The `min{q, (p/ε)² + log* q}` round bound is the choice between `twoSweep_correct` (`2q` rounds) and
    `fastTwoSweep_correct` (`2K` rounds after Lemma 3.4). It is not formalized as a single statement.
* **`β_v = max(1, outdeg)` (paper's Section 2).** Because of this convention, the corollary "lists of size
  `≥ β² + β + 1`" (`twoSweep_listColoring`) needs `β ≥ 1`. For `β = 0`, slack (2) fails for lists of size 1.
* **"List `d`-defective 3-colouring in `O(Δ + log* n)` rounds whenever `d > (2Δ − 3)/3`."**
  * We prove the `2q`-round statement with `p = 2`, `ε = 0` (`twoSweep_threeColoring`).
  * The `O(Δ + log* n)` bound needs an initial proper `O(Δ)`-colouring computed in `O(Δ + log* n)` rounds (e.g.
    [BEG18]). The paper does not say this.
  * Using Theorem 1.1 with `ε > 0` would need `ε = Θ(1/Δ)` and give `O(Δ²)` rounds.
* **Section 4.1.**
  * The arbdefective subroutine `A` is replaced by its output specification. `IsRun` quantifies over all
    outputs.
  * `Sec41.exists_isRun` (greedy) shows that runs exist for `S ≥ 1` on finite graphs.
  * `Δ` in Lean is any bound on the defects. `deg ≤ Δ` is not needed for correctness.
* **Lemmas 4.4, 4.5, A.1.** These are spec-level reductions; round complexities are in docstrings only.
  `Lemma 4.4` also proves that a colouring exists, by induction over the classes.
* **Not formalized.**
  * Theorem 1.3 and Theorem 1.5 / Lemma 4.6. These are `O`-notation recursions over cited black boxes
    (Theorem 3 and Theorem 4 of [FK23a], Lemma 3.4), and they inherit the Lemma A.1 issue above.
  * We noticed an inconsistency in Theorem 1.5's arithmetic but did not check it formally. Eq. (20) multiplies
    `O(θ² log³Δ)` by `O(C^{1/4} log Δ log³ C)`, which gives `log⁷Δ` for `C = O(Δ)`. The theorem states
    `log⁸Δ`; this only weakens the bound.
