# Differences between the formalization and the paper

Paper: Bentert, Avin, Schmid, *A Separation Between Optimal Demand-Oblivious and Demand-Aware
Network Throughput*, PODC 2026, arXiv 2605.04699v1.

## Modelling choices

1. **Multigraphs and capacities.** A network is an `ℕ`-adjacency matrix. A `(2n−1)`-regular
   network has all row and column sums equal to `2n−1`. As in the paper's "more formally"
   paragraph (§1.1), arcs get capacity `1` and the demand is scaled by `2n−1`.
2. **Paths and the capacity charge.** A path is a vertex sequence `src :: rest` with `rest ≠ []`,
   i.e. at least one arc, as in the paper. The paper's capacity constraint is per arc of the
   multigraph: `∑_i 1_{e∈P_i} d_i ≤ 1`, where the arc identities of `P_i` are part of the flow. We do
   not model arc identities. Instead we use two aggregated semantics:
   * `CanRoute`: on the pair `(u, v)`, `∑_i d_i · #{times P_i traverses (u,v)} ≤ A u v`. This is at
     least as strict as the paper's rule: the amounts can be split fractionally over the `A u v`
     parallel arcs, filling them one after another, and reusing an arc is only cheaper in the paper. All **yes-instances** of the multi-hop problems are proved for it: Theorem 5, Observation 3
     and `example_M1_throughput`.
   * `CanRouteRel`: `∑_i d_i · 1[(u,v) ∈ P_i] ≤ A u v`. The paper's rule implies it, since a path
     through `(u,v)` uses at least one of the `A u v` parallel arcs. All **no-instances** of the
     multi-hop problems are proved for it (`proposition_1_rel`, `proposition_4_weak_rel`,
     `example_M2_not_throughput_rel`), and `DAThroughput.rel` transfers them to `CanRoute`.
   * For direct routing (single arcs) the three semantics coincide (`canRouteDirectly_iff`:
     `0 ≤ D ≤ A` entrywise).

   Hence every checked statement transfers to the paper's exact semantics.
3. **Throughput as a maximum.** The paper defines throughput as "the largest `θ` such that `G` can
   host `θM`". We render "throughput `≥ κ`" as "∃ `θ ≥ κ` such that `G` hosts `θM`". This is the
   same as "max ≥ κ" whenever the maximum exists, as the paper assumes. Hosting is downward closed
   for `κ ≥ 0` (`CanHost.of_le`). The weak variants likewise read "∃ `M' ≤ M` hosted with
   `∑M'/n ≥ κ`".
4. **Range of `κ`.** The problems take `κ ∈ [0, 1]`; our definitions accept any real `κ`.
   * Proposition 1 is stated for all `κ > 5/6`. The paper's matrix `M_κ` needs `ε = κ − 5/6 ≤ 1/6`;
     for `κ > 1` we use the matrix of `κ = 1`.
   * Observation 2 needs `0 ≤ κ ≤ 1` (as in the paper) and `n ≥ 1`.
   * Propositions 2 and 3, Observation 3 and Theorem 6 need `n ≥ 1`; `n = 0` is degenerate.
5. **Randomness.** Theorems 3 and 4 are stated on finite probability spaces (`FinDist`: a
   non-negative weight function summing to `1`). "With probability 1" means "for every outcome of
   positive weight". Theorem 4 is stated for an arbitrary finite index type instead of `[t]`.
   Theorem 3 is the special case the paper uses: `n × n` matrices with integer row and column sums.
6. **Theorem 2 / Theorem 5 conclusion.** `theorem_2` concludes `DAThroughput M (5/8 − ε)`. For
   `ε > 5/8` this is vacuous (negative target), consistent with the problem definition.

## Proofs that differ from the paper

7. **Proposition 2.** The paper uses the greedy algorithm. We pad `⌈n·M_ij⌉`, whose row and column
   sums are `< 2n` and hence `≤ 2n−1`, to a regular matrix with CSLib's `Matrix.exists_regular_above`.
   The paper's greedy argument is not checked. It also needs a small care point: one should consider
   whichever of row `i*` and column `j*` becomes full first. Randomized exhaustive comparisons for
   `n ≤ 4` (script in the work folder) found the greedy optimal; this is not a proof.
8. **Observation 3** is derived from Proposition 2 and Observation 1, not from the external Theorem 1
   of Keslassy et al. (which is not formalized). Theorem 5's case `κ ≤ n/(2n−1)` uses the same
   route.
9. **Proposition 1 and Proposition 4 (first part)** use two cut inequalities valid for every flow
   on two nodes (`two_node_bounds_rel`), instead of the paper's per-graph reasoning:
   `D_ab ≤ A_ab` and `D_ab + D_aa + D_bb ≤ A_ab + A_aa + A_bb`. For the second part of Proposition 4
   we use the per-entry bound `min(e, A) ≤ A/2 + e/2 − 1/4 (+1/4 on the diagonal for odd n)`,
   instead of counting "fully usable arcs".
10. **Theorem 3 and Lemma 1.** The paper (and Gandhi et al.) find a simple cycle in the bipartite
    graph of fractional entries. We instead obtain a direction with zero line sums by a dimension
    count (`exists_circulation`). For Theorem 3, a minimal-support direction has at most two
    nonzero entries per line (`exists_cycle_direction`), which is all the negative-correlation step
    needs. In Lemma 1 the sign of the direction is chosen so that `∑ a·c` does not decrease. We use
    `∑ x² ≥ X²/n²` (Cauchy–Schwarz) as in the paper.

## Errors and gaps in the paper (with the deciding rule)

11. **Theorem 5, application of Theorem 4 (proof repair, 🛠️).** "`t = n + Y_i`" with
    `Y_i = ∑_j (1 − b'_ij)` treats `Y_i` as an integer number of constant variables of weight `1`,
    but `Y_i` is not an integer in general. Repair: `n` constant variables (`X ≡ 1`, `x = 1`) of
    weight `1 − b'_ij` (`line_bad_prob_le`). This is a claim inside a proof (R1), not a statement.
12. **Theorem 5, choice of `n_κ` (routine gap).** The conditions are imposed at `n_κ` only and used
    for all `n ≥ n_κ`. They do hold for all `n ≥ n_κ`: `2n e^{−cn}` is `> 1` up to its maximum at
    `1/c` and decreasing afterwards, for `c = 2ε²/3` small. Formalized via `eventually_large`.
13. **Theorem 5, sign typo.** "`ε = κ − 5/8 > 0`" should be `ε = 5/8 − κ`. Also "`b_ij < (2n−1)κ a_ij`"
    is only `≤` when `a_ij = 0`, and "`b_ij < min(a_ij, d_ij)`" should be `b_ij < d_ij`. These are
    inside a proof, so R1 does not apply.
14. **Proposition 1's proof.**
    * The equation `5/6 − 5ε/12 − ε²/2 = 5/6 − 5ε/6 + ε − ε − ε²/2` is false. The final inequality is
      still true: `5/6 − 5ε/12 − ε²/2 < (5/6+ε)(1−ε)` iff `ε²/2 < 7ε/12`.
    * The bottom graphs are dismissed without a real argument ("since `1 − ε > 2/3`").

    The statement is true (R1: proof repair).
15. **Problem definition typo (⚠️, R3).** The box for Demand-Aware Weak Direct Throughput asks
    whether "the direct throughput of `G` … is at least `κ`". Read literally, the problem is
    Demand-Aware Direct Throughput, and Theorem 6 (`κ ≤ (7n−4)/(8n−4)` ⇒ yes) would contradict
    Proposition 3 for `n ≥ 2`. The intended "weak direct throughput" is defined in §1.1 and is clear
    from the problem's name, Observation 4 and the proof of Theorem 6; the fix is one word. We
    formalize the intended problem (`DAWeakDirectThroughput`).
16. **Proposition 3 typo (⚠️, R3).** The statement constructs `M_κ` but says "`(M, κ)` is a
    no-instance" (checked on the rendered page; `M` carries no subscript). The intent `(M_κ, κ)` is
    evident from the proof. Items 15 and 16 set the verdict to ⚠️. Borderline: both are pure
    presentation typos, so one could argue for 🛠️ (through the proof repairs above); we keep ⚠️
    because item 15 makes Theorem 6 false if read at the paper's word.
17. **§2 example (no error).** pdftotext renders the stacked fraction of "`(M₁, 8/9)` is a
    yes-instance of Demand-Aware Throughput" as "98"; the rendered page reads `8/9`, which we prove
    (`example_M1_throughput`, `example_M1_not_weakDirect`).
18. **Numerical remark after Theorem 5.** "For `n ≥ 26000` … `κ = 0.6`": the proof's two conditions
    first hold at `n = 26068`. The other values check out: improvement over `n/(2n−1)` from `n ≈ 701`,
    `κ = 0.55` from `n = 2243 ≤ 2250`, `κ = 0.624` at ≈ 26.7 million. The two conditions are only
    sufficient, so the claim for `26000 ≤ n < 26068` is unsupported rather than refuted; it is a
    remark, not a statement.

## Not formalized

- Theorem 1 (Keslassy et al., demand-oblivious bound), which is external and not needed.
- Propositions 5 and 6 (algorithms and running times).
- Theorem 7 (NP-hardness of Demand-Aware Weak Throughput).
- The paper's statements about Table 2.
- In Table 1, the gaps that the paper itself leaves open.
