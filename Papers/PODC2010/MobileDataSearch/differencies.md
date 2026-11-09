# Differences between the formalization and the paper

Paper: Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010 (8-page conference version; no full version exists).

## Mistakes and proof gaps (labelled)

1. 🛠️ **Lemma 4, proof (used for Theorems 4 and 5).** "FRO₄ = ⟨{C_A C_B}, {C_C C_D}⟩ … thus
   cost(FRO₄) ≥ cost(FRO_N)" is false. FRO on the merged instance minimises over more splits, and
   `cost(FRO₄) ≤ cost(FRO_N)` holds instead. Counterexample `lemma4_proof_step_fails`: `p = (8,1,6,5,1)`,
   `w = (1,1,7,6,4)`, FRO 246, OPT 243; merged `p = (8,1,5,7)`, `w = (1,1,6,11)`, FRO 245, OPT 243. The
   statement of Lemma 4 is still true (`lemma4`), but only as a corollary of Theorem 4 and Lemma 7.
2. 🛠️ **Lemmas 5, 6 (proofs omitted, "tedious case analysis") and Theorem 5 (proof outline only).** Replaced
   by a direct proof for every `N` (`bracket_gen`, `key_real`, `typ_real`). This is a new argument, not the
   paper's case analysis.
3. ✏️ **Lemma 1, proof (degenerate case).** From `j < i` it concludes the strict `p_i < p_j`, `w_i > w_j`,
   which is false with ties. For positive costs, "cost(A') < cost(A)" still holds unless `C_i, C_j` are
   identical boxes or both have probability 0 and lie in a round of probability 0; only then does the
   contradiction fail (and "every optimal strategy respects the order" is false). It also assumes the inversion lies between
   adjacent rounds; with non-empty rounds an adjacent inversion exists, but this is not said. Repaired by a
   weak-inequality exchange argument with a potential function (`cost_comp_swap_le`,
   `exists_monotone_cost_le`, `lemma1_isOptimal`).
4. ✏️ **Lemma 7 / "8/7 is attainable".** The instance has the tie `p₁/w₁ = p₂/w₂ = 5/4`. FRO attains `8/7` only
   with the adversarial tie-breaking (order 1, 2, 3, …); with order 2, 1, 3, … it is optimal. Section 5.2
   states this convention for typical tokens only. We use it throughout: our FRO is "any minimum among the
   strategies respecting a given ratio-sorted indexing".

## Typos (no claim affected)

- Section 4: "X = (1 + Y)/2" (X load balancing, Y search) should be `Y = (1 + X)/2`.
- Lemma 1, proof: "non-decreasing order of the ratios" should be non-increasing.
- Lemma 3, proof: "greater than 1/D and smaller than 1" should be `≥ 1/D`, `≤ 1`.
- Abstract and Theorem 5: the ratio is printed as `(7 − 2√7)/(28 − 10√7)`; it equals `(4 + √7)/6`, the form
  we use.
- Lemma 4, proof: "if there are at least two empty sets among A, B, C, D, then OPT is FRO". For `A = D = ∅`
  the partitions are `⟨C, B⟩` and `⟨B, C⟩`, not the same; they have equal cost by Lemma 2, so the conclusion
  (ratio 1) holds.

## Modelling choices

- **Strategies.** A strategy is a map `Fin N → Fin D` (round of each box), so empty rounds are allowed; the
  paper uses ordered `D`-partitions, presumably into non-empty sets. This changes no optimum (merging away an
  empty round, or splitting a round, never increases the cost). For two rounds, FRO's candidates include the
  two trivial splits, of cost `P·W`, which is never below a proper split.
- **Normalization.** `p` need not sum to 1 (Proposition 2 makes this harmless). `prop3`, `lemma3`, `lemma7`
  and `lemma8` use normalized instances, as the paper does.
- **Costs.** Theorems 4, 5 and Lemmas 1, 2 allow `w i = 0`; the paper assumes positive costs (needed for the
  ratios `p_i/w_i`). `RatioSorted` is the cross-multiplied form `p_j w_i ≤ p_i w_j` for `i ≤ j`, equivalent
  for positive costs. The Lemma 7 instance has positive costs (`w7_pos`). The Lemma 8 instance has zero
  probabilities and costs for boxes 4…N, which the paper handles by "0/0 = 1".
- **FRO.** The boxes are indexed in ratio order, and FRO is any minimum-cost monotone strategy (`IsFRO`). The
  paper's FRO is a specific dynamic program; any implementation returns a minimum of the same family. Ties in
  the ratio order are fixed by the indexing, so our theorems cover every tie-breaking.
- **Theorem 4.** Proved for every `N ≥ 0` (the paper: `N > 2`). The paper speaks of an approximation
  *algorithm*; we state it per instance: every FRO output `A` and every strategy `B` satisfy
  `cost A ≤ 8/7 · cost B`.
- **Theorem 5.** Typical token `p = w`, any order (all orders are ratio orders), any `N`. The ratio is
  `(4 + √7)/6`.
- **Lemma 4.** We prove its statement in the form: for every instance there is a 3-box instance with FRO
  ratio at least as large (via Lemma 7), and separately refute the proof step.
- **Lemmas 7, 8.** Instances for `N = m + 3`, exactly as in the paper. We prove that every FRO output has the
  stated cost and every optimal strategy has the stated optimum, so the ratio is exactly `8/7`, resp.
  `(4+√7)/6`.
- **Corollary 1.** Proved in a stronger form: the sequential ratio-order strategy is at least as good as
  every strategy with any number of rounds (`corollary1`).
- **Lemma 2.** Stated without division: `P_{d+1} W_d ≤ P_d W_{d+1}`.
- **Lemma 3.** Stated per instance for a strategy `A` with `lbCost A ≤ (1+ε) lbCost O`, `O` an optimal
  load-balancing allocation. Conclusions: `O` is search-optimal, the ratio is `≤ 1 + ε·O/(1+O) ≤ 1 + ε/2`
  (strict for `ε > 0`), and `≥ 1 + ε/(D+1)` when `lbCost A = (1+ε) lbCost O` (the "tight" hypothesis of the
  paper is made explicit).

## Not formalized

Theorem 1 (`Θ(ND)` dynamic program), Theorem 2 (strong NP-hardness), Theorem 3 and Table 1 (results quoted from
the load-balancing literature [2, 8, 10]), Section 5.3 (PTAS), Section 6 (conjecture for `D > 2`).
