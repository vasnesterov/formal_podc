# Differences between the formalization and the paper

Paper: A. Balliu, S. Brandt, F. Kuhn, D. Olivetti, *Improved Distributed Lower Bounds for MIS and Bounded
(Out-)Degree Dominating Sets in Trees*, PODC 2021 (arXiv:2106.02440v1).

## Errors in the paper

1. **Lemma 15 is false for `Δ = 1`** (`lemma_15_false_delta_one`). The statement says "for all `x ≤ Δ − 1`
   and `a ≥ 1`", and `Δ = 1`, `x = 0`, `a = 1` is allowed. The claimed bound is then `1/Δ⁸ = 1`.
   * *Counterexample.* The family of Δ-regular graphs is `{K₂}`. Output `M` or `A` with probability
     `1/2` each. Both are node configurations of `Π_1(1, 0)` (`M^1X^0` and `A^1X^0`). The algorithm
     fails only on `MM` or `AA`, i.e. with probability `1/2 < 1`.
   * *Where the proof breaks.* The last step `1/(3Δ)² ≥ 1/Δ⁸` needs `Δ ≥ 2`.
   * *Rule.* R2: `Δ = 1` is a parameter corner that is never used and lies outside the interesting
     range. Verdict ⚠️.
   * *What we prove.* `lemma_15` for `Δ ≥ 2`, with failure probability `≥ 1/(36Δ²) ≥ 1/Δ⁸`. The paper's
     argument assumes that the outputs are always node configurations ("there is at least one
     configuration that is used by all nodes with probability at least 1/3"). We count an invalid
     output as a failure and split into two cases: the probability `q` of invalid outputs is
     `≥ 1/(36Δ²)`, or it is small and the paper's argument applies with `1 − q ≥ 1/2` in place of `1`.

## Typos and implicit assumptions (no effect on any result)

2. **§2.3, definition of `R̄`.** `Σ_{Π''}` is said to consist of the sets that appear in configurations of
   `E_{Π''}`, which is circular because `E_{Π''}` is defined via `Σ_{Π''}`. It should be `N_{Π''}`
   (`Problem.alphRbar`). Also the typo "`Σ_{Π''} =⊆ 2^{Σ_{Π'}}`".
3. **Lemma 5** ("for all `a`") needs `k ≤ Δ`, so that `M^{Δ−k}X^k` exists. We assume `k ≤ Δ`, which is
   implied by the family's range `0 ≤ a, x ≤ Δ` and by `k ≤ Δ^ε` (R4, not counted as an error).
4. **Lemma 11** needs `x ≤ Δ` for the same reason (R4, family range).
5. **Lemma 12** "`x ≤ Δ − 1`" is stated as `x < Δ`. This is the same thing for integers, but it rules
   out the truncated-subtraction case `Δ = 0` in Lean.
6. **Lemma 8 proof.** "Each `Yᵢ` contains `B`" is derived after showing `Yᵢ ⊆ OUABPQ`, but this is not
   needed. "At least `x + 1` of the `Yᵢ` contain `A`" does need it.

## Modelling choices

7. **Graph class.** We use the infinite `Δ`-regular tree (Cayley graph of `FreeCox Δ`), not finite
   high-girth graphs or finite trees. The paper's port-numbering bound is stated for "`Δ`-regular trees",
   and finite `Δ`-regular trees do not exist, so the infinite tree is the natural reading.
   On the full tree every combination of local views occurs, so the round-elimination theorem needs no
   `t`-independence or girth hypothesis.
8. **Inputs.** The `Δ`-edge colouring is built into the tree, and port number = colour at both
   endpoints. This is the graph family of Lemmas 12 and 15, and the paper's Theorem 14 also asks for
   port `i` at both ends. Algorithms in the paper's model may see arbitrary port numbers. Since the
   colours are known, the two models are equivalent:
   * a port-numbering algorithm restricted to the family "port = colour" is an algorithm of ours;
   * conversely, an algorithm of ours that ignores the port numbers is a port-numbering algorithm.

   The edge port numbering `{1, 2}` is an `Orientation` (direction bits on darts, antisymmetric along
   each edge).
9. **What a `t`-round algorithm sees.** It is a function of the orientation on the edges with both
   endpoints within distance `t` (`AgreeOn`, `IsLocal`). So a node sees the orientation of its own
   incident edges only after 1 round. This is the paper's convention in the proof of Lemma 12. Under
   the other convention (orientation of incident edges known at time 0), Lemma 12 would fail for
   `a ≤ x + 1`. Example: put `M` on in-edges and `A` on out-edges. An algorithm in the stronger
   convention with `t` rounds is an algorithm of ours with `t + 1` rounds, so the asymptotic bound is
   the same.
10. **Configurations** are colour-indexed tuples `Fin Δ → Λ`. Condensed configurations `ℓ₁^{n₁}ℓ₂^{n₂}`
    are given by label counts (`cnt`); the problems of the family are permutation invariant.
    * *Relaxation (Definition 7).* The permutation `ρ` is absorbed by choosing the relaxed label
      position by position: `lemma_8_relax` gives `σ ∈ N⁺` with `Yᵢ ⊆ toRel(σ i)`.
    * *`Π_rel`* is never built as a separate problem. Its edge constraint, computed by the method of
      §2.3, is checked against `E⁺` after renaming (`toRel_edge`).
11. **Alphabet.** The alphabet of a problem is its whole label type. In `R̄(R(Π))` we allow all nonempty
    subsets of `Finset Λ`, not only subsets of `Σ_{R(Π)}`. Because the node condition is universal,
    a set containing a label outside `Σ_{R(Π)}` never occurs in a node configuration, so this is the
    same problem.
12. **Theorem 3** (Brandt [13], imported by the paper) is formalized only in the direction used,
    "`Π` in `T` rounds ⇒ `R̄(R(Π))` in `max(T−1, 0)` rounds" (`Problem.SolvableIn.Rbar_R_sub`).
    * We use the paper's maximal versions of `R` and `R̄`.
    * The maximal extension of an edge configuration must be chosen consistently by both endpoints.
      The proof does this with the edge orientation, which the paper has as an input (§2.1).
13. **Lemma 6.**
    * *Renaming.* It is stated as a correspondence `toSet : L8 → Finset L5`: the alphabet is the range
      (`alphR_Pi`), the edge constraint is `XQ, OB, AU, PM` (`edgeMax_toSet`), and the node constraint
      is the condensed form (`R_Pi_node`).
    * *Hypothesis.* We only need `x, a ≤ Δ`; the paper assumes `x + 2 ≤ a ≤ Δ`.
    * *Figure 5.* The paper's node diagram is not formalized. We use only the direction "a larger set
      of `Σ_{R(Π)}` is at least as strong" (`R_nodeStronger`), which is all Lemma 8 needs.
13a. **Lemma 8** says `Π⁺_Δ(a, x)` "has time complexity `max{T − 1, 0}`". The proof (a 0-round
    reduction from `R̄(R(Π_Δ(a, x)))`) only gives "at most `max{T − 1, 0}`", which is also how
    Corollary 10 phrases it and all that is used. We state the upper bound (`lemma_8`); the reading
    "exactly" is neither claimed by the proof nor refuted here (not counted as an error).
14. **Lemma 13** is stated with the explicit condition `8^t (k + t + 1) ≤ Δ` instead of "`t = ε log Δ`,
    `x ≤ Δ^ε`, `Δ` large enough". The asymptotic form `odsLowerBound_log` uses `ε = 1/6`:
    `t = ⌊log₂Δ / 6⌋` and `k ≤ 2^t`, for all `Δ`.
    * *Logarithm base.* The paper writes `ε log Δ` without a base; base 2 matches its `2^{3i}`.
    * *Item 4.* "All problems use at most 5 labels" becomes the label type `L5`.
15. **Port-numbering lower bound.** The paper derives "`Π_0` needs `≥ t` rounds" informally from Lemma 13
    and Theorem 3. We prove the statement for `k`-ODS directly (`odsLowerBound`), with Lemma 5 costing
    one round: `k`-ODS needs `≥ t` rounds, i.e. `Π_Δ(Δ, k)` needs `≥ t + 1`.
16. **Randomized model (Lemma 15).** A randomized 0-round algorithm is one probability vector `p` on
    configurations, used independently by all nodes (they all have the same 0-round view). We work with
    real-valued finite sums instead of measure theory.

## Not formalized

17. Theorem 14 (lifting from port numbering to LOCAL, imported from [4, 5, 15]) and hence Theorem 1 and
    Corollary 2 in the LOCAL model. The `log_Δ n` / `log_Δ log n` terms and the choice of `Δ` in
    Corollary 2 are not formalized.
18. The converse direction of Theorem 3.
19. The first half of Observation 4 (labels of `R(Π)` are right-closed w.r.t. `E_Π`) as a general
    statement. It is only used to list the candidate labels in Lemma 6; we compute the alphabet of
    `R(Π_Δ(a, x))` directly (`alphR_Pi`, by exhaustive check over `Finset L5`).
