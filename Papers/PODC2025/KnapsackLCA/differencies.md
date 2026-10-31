# Differences between the formalization and the paper

Paper: C. L. Canonne, Y. Li, S. W. Umboh, *Local Computation Algorithms for Knapsack: impossibility
results, and how to avoid them*, PODC 2025 (brief announcement); full version arXiv:2504.01543v1,
whose numbering is used throughout.

## Errors in the paper

1. **Theorem 4.1 is false** (headline; `Sec4.theorem_4_1_false`, `Sec4.lcaKP_not_correct`,
   `Sec4.answerKP_uniform`).
   *Instance.* `N` items with normalised profit `1/N` and weight `1/N`, weight limit `1/2`. In
   integer form: weights `1`, limit `N/2`, which satisfies Definition 2.2. Parameters: `ε = 1/m`,
   `m ≥ 30`, `N ≥ m²`.
   *Run.* No item is large. So `L(Ĩ) = ∅`, `q = ε + ε²/2`, and `t = ⌊1/q⌋ ≤ m − 1`
   (`quantile_range`). For every `1 ≤ k ≤ t` we have `τ < 1 − kq < 1 − τ`. Since the efficiency
   distribution is the point mass at `1`, the only `τ`-approximate `(1 − kq)`-quantile is `1`
   (`uniform_quantile_eq_one`). So on every accurate run `ẽ_k = 1` for all `k ≤ t`, and `t' = t`.
   Every item of `Ĩ` is then `(ε², ε²)` with efficiency `1`. Line 3 of CONVERT-GREEDY has no
   `k ≤ t'` with `ẽ_k > p_j/w_j = 1`, so `k < 3` and `e_small = −1` (`convertGreedy_esmall`). No
   item is large, so Lines 20–24 answer "no". This holds for every sample `R` and every order of
   `Ĩ`, sorted or not.
   *Failure.* A `(1/2, 6ε)`-approximate solution has at least `(N − 1)/4 − 6εN` items
   (`card_of_approx`), since `⌊N/2⌋` items are feasible. Suppose each run is accurate with
   probability `≥ 1 − η`, a seed-dependent solution `C` exists, and each answer agrees with `C`
   with probability `≥ 1 − δ`. Averaging over the `N` queries gives
   `δ + η + 6ε ≥ (N − 1)/(4N)`. With `δ = ε` (Theorem 4.1) and `η = ε/36` (Theorem 4.5 with
   `β = ρ/2 = ε²/36`, union bound over `t ≤ 1/ε` calls, as in Lemmas 4.6 and 4.9), this fails for
   `m ≥ 30`. The refuted statement is the weakest, per-query reading of "provides query access
   with failure probability `ε`". The global reading of Lemma 4.9 (all answers consistent with one
   solution with probability `1 − ε`) is stronger and therefore also refuted.
   *What was modelled.* Algorithm 2 Lines 1–5 and 11–24, the `Ĩ`-construction, and Algorithm 3
   are modelled faithfully. Lines 6–10 (sampling `Q` and calling `rQuantile`) are abstracted into
   the outputs `ẽ_k`, with the accuracy guarantee of Theorem 4.5 as the only assumption. The
   sample-size precondition of Theorem 4.5 holds here: `|E| = |Q| = a ≥ n_rq`, because no item is
   large. The hypothesis `hl` only asks that the list sorted in Line 1 of Algorithm 3 consists of
   items of `Ĩ`. `rQuantile` could in principle output `±∞`, the extra points of its domain. Such
   outputs are not accurate, since `Pr[eff ≥ +∞] = 0 < 1 − π − τ` and `Pr[eff ≤ −∞] = 0 < π − τ`,
   so modelling outputs as reals loses nothing.
   *Why not excused (R2–R4).* The instance is not degenerate (any `N ≥ 900`; a natural
   instance whose optimum, any `⌊N/2⌋` items, is obvious), and nothing in the paper assumes distinct
   efficiencies; Section 4.2 explicitly treats profits and weights as arbitrary. Ties are not an
   exotic corner: the synthetic items of `Ĩ` have efficiency exactly `ẽ_{k+1}` by construction,
   and two consecutive quantiles `ẽ_k = ẽ_{k+1}` coincide whenever one efficiency value carries
   profit mass above about `q`. Nor is there a local fix (R3): replacing `>` by `≥` in Line 3 of
   Algorithm 3 gives `k = t ≥ 3`, `e_small = 1`, and `LCA-KP` then answers "yes" to every item
   (weight `1 > K = 1/2`, infeasible). A repair needs consistent tie-breaking (e.g. quantiles of
   `(efficiency, index)` pairs) and, by the atom remark in item 2, different EPS tolerances, so
   Lemma 4.4 of [IKY12] would have to be re-checked.
   *Verdict rule.* This is R5: Theorem 4.1 names the paper's specific algorithm ("Algorithm 2
   (`LCA−KP`) is a `(t(n), ε)`-LCA …"), and Theorem 1.4 calls it the main theorem. So the label
   is 🚨. Borderline aspect: Theorem 1.4 and the abstract are existential ("there exists an
   LCA …"). A repair is plausible, for example breaking efficiency ties consistently by item index
   and adjusting the EPS tolerances (see item 2). It is neither given in the paper nor checked
   here, so the existential claim is at best unestablished.
2. **Lemma 4.6 is false** (`Sec4.no_eps_uniform`). On the same instance, with `ε + ε² ≤ 1`, no
   sequence of length `t ≥ 1` is an EPS (Definition 4.3). `A_0(I)` must have profit `≥ ε`, so it
   is nonempty and hence contains everything (all efficiencies are equal). Its profit is then
   `1 ≥ ε + ε²`, contradicting the upper bound. And `A_1(I)` must also be nonempty. The algorithm
   always produces `t' ≥ t − 1 ≥ 1`, so the probability in Lemma 4.6 is `0`.
   *Where the proof breaks.* From `Pr[p/w ≤ ẽ_k] ≥ 1 − kq − τ` it derives `Pr[p/w > ẽ_k] < kq + τ`,
   which is fine. It then uses this as `Pr[p/w ≥ ẽ_k] ≤ q + τ` ("combining these inequalities"),
   which ignores the atom at `ẽ_k`. With equal efficiencies the atom is everything. Even with
   distinct efficiencies, a single small item of profit `ε²` sitting at a quantile adds up to
   `ε²/c` to an interval. That breaks the claimed bound `ε + 7ε²/10 < ε + ε²`, so the constants
   of Definition 4.3 would have to change. This second point is a remark, not formalized.
3. **Proof of Theorem 3.4 (Lemma 3.5) is not valid; theorem true.** Proof repair under R1, since
   Lemma 3.5 is vacuously true. Lemma 3.5 claims that for every query `k` with `w_k = 3/4`, the
   answer is "yes" with probability `≥ 9/10`. Its proof argues that a "no" on the default view
   costs conditional error `1/3 − 1/10 > 1/5`. But the error bound `1/5` is an average over the
   whole distribution, hence over `k`. So it does not force "yes" for each `k`, and the later
   union bound has no justification. The hypotheses of Lemma 3.5 (deterministic, `q < n/11`,
   success `≥ 4/5`) are unsatisfiable for `n ≥ 2` by our Theorem 3.4, so the lemma is vacuously
   true but not proved. Replacement (`LCA.count_le`, `LCA.yao_bound`): for each seed, let `b_k`
   be the default answer and `P_k` the default probe set, with `y = #{b_k = yes}/n`. The algorithm
   fails on `(i, j, light)` if `b_i = no` and `j ∉ P_i`, and on `(i, j, heavy)` if `b_i = b_j`,
   `j ∉ P_i` and `i ∉ P_j`. The number of good instances out of `2n(n−1)` is at most
   `2n(n−1) − (7n² − 10n − 1)/8 + 3nq`. With global success `4/5` this gives `q ≥ n/11` for every
   `n ≥ 2`, the paper's constant. With per-query failure `1/5` it gives `q ≥ n/40 − 1/5`.
4. **Proofs of Theorems 3.2 and 3.3 leave the paper's model; theorems true.** Proof repair.
   Definition 2.2 assumes the total profit is normalised to `1`. The reduction instance `I(x)` has
   total profit `|x| + 1/2` (resp. `|x| + β`). An LCA that is correct only on normalised instances
   may behave arbitrarily on `I(x)`, and normalising `I(x)` on the fly needs `|x|`, that is, all of
   `x`. The paper's reduction is formalized for LCAs that are correct on all well-formed instances
   (`theorem_3_2`, `theorem_3_3`). For LCAs that are correct only on normalised instances we prove
   the theorems directly (`theorem_3_2_normalized`, `theorem_3_3_normalized`). The base instance
   gives every ordinary item profit `c` and the special item profit `γc`. Needle instance `m`
   moves the profit of block `[mb, mb + b)` onto the block's first item, which keeps the total at
   `1`. The bound is `⌊n/b⌋ (1 − 2δ)` with `b = ⌊1/α²⌋ + 1`, so `⌊n/2⌋/3` for optimal solutions.
   Any normalised family must change at least two coordinates per instance (one coordinate alone
   cannot change while the sum stays fixed), so the single-bit reduction from `OR` cannot be kept.
   Whether one reads the normalisation as part of the LCA's promise is a modelling question.
   Both versions are proved, so the statements hold either way.
5. **Theorem 3.4 statement: "`(t(n), 4/5)`-LCA".** Typo (R3). By Definition 2.2 the second
   parameter is the failure probability, but the proof assumes success probability `4/5`, and we
   formalize that. The literal statement (success `≥ 1/5`) cannot follow from the paper's hard
   distribution. The 1-query algorithm "answer yes on weights `0` and `1/4`; on weight `3/4`
   answer a random hash bit of the index" succeeds with probability `1/2` on every instance of the
   distribution. This remark is not formalized. Whether the literal statement is true is open
   here.
6. **Proof of Theorem 3.4: `(i, j)` uniform in `[n]²`.** This allows `i = j`, where the weight
   assignment is ill-defined. Proof repair (minor): we use ordered pairs of distinct indices,
   uniform, with `j`'s weight uniform in `{1/4, 3/4}`.

## Typos and imprecisions (no effect on the formal results)

* Theorem 2.7 states the sample complexity of `rMedian` as `Ω̃(·)`; it should be `Õ(·)`.
* The approximation guarantee of the positive result is stated three ways: `(1/2 + ε)` in
  Theorem 1.4, a "(2 + ε)-approximate" LCA in the technical overview, and `(1/2, 6ε)` in
  Theorem 4.1.
* Theorem 3.4's proof uses non-integer weights `3/4, 1/4` with `K = 1`, while Definition 2.2
  requires integer weights, and profits `0`, while Definition 2.2 normalises total profit to `1`.
  We use weights `3, 1, 0`, limit `4`, and profits `1/n`, which is equivalent.
* The "τ-approximate p-quantile" used in Theorem 4.5 is never defined. We use the definition its
  proof derives: `Pr[X ≤ v] ≥ p − τ` and `Pr[X ≥ v] ≥ 1 − p − τ`.
* Algorithm 3, Line 3 does not say what happens when no `k` satisfies `ẽ_k > p_j/w_j`, or when
  `j = 0`. We set `k = 0`. In the counterexample the branch `k ≥ 3` is impossible under any
  reading.

## Modelling choices

* **Instances.** Profits are reals and weights natural numbers (Definition 2.2: integer weights).
  `WellFormed` means non-negative profits and every weight `≤ K`. `Normalized` adds total profit
  `1`. Section 4 uses normalised real weights (`RInstance`), as the paper does there.
* **LCA.** A `PMF` over seeds; for each weight limit `K`, seed and query, a query tree over the
  item oracle `Fin n → ℝ × ℕ`. `K` and `n` are given to the LCA for free. This only strengthens
  the lower bounds, since every hard family has a fixed `K`. Statelessness, parallelizability and
  query-order obliviousness (Definitions 2.2–2.4) hold by construction. Time `t(n)` is modelled
  as query complexity, the worst case over all oracles (footnote 1 of the paper). Space is
  ignored, as in the paper.
* **Correctness.** Definition 2.2 is ambiguous. `LCA.Correct` (per query) asks for a
  seed-dependent solution `C r` such that for every query `i`, with probability `≥ 1 − δ`, `C r`
  is valid and the answer to `i` agrees with it. `LCA.CorrectStrong` (global) asks that the set
  of "yes" answers is valid with probability `≥ 1 − δ`. Global implies per-query
  (`CorrectStrong.correct`). Theorems 3.2 and 3.3 assume only per-query correctness, the weakest
  hypothesis, and so cover both readings. Theorem 3.4 is proved in both readings, with constants
  `n/11` (global, as in the paper's proof) and `n/40 − 1/5` (per query).
* **Theorems 3.2/3.3 sizes.** We state them for `n + 1` items, so `OR_n` is used where the paper
  writes `OR_{n−1}` on `n` items. Bound: `n/3`. Theorem 3.3 holds for every `α > 0`; the paper
  states `α ∈ (0, 1]`.
* **Ω(n).** The paper's asymptotic `t(n) = Ω(n)` is formalized as explicit linear bounds for every
  `n`.
* **Lemma 3.1.** Proved for randomized query algorithms with error `δ` on every input:
  `n (1 − 2δ) ≤ q` (`Cslib.QueryTree.or_lower_bound`). The paper cites it as standard.
* **Yao's principle.** Only the easy direction (averaging) is needed and proved
  (`sum_mul_probReal_le`).
* **Section 4 randomness.** One `PMF` over executions. The run for query `i` has data
  `(R ω i, e ω i, l ω i)`. The only hypothesis is the per-run accuracy probability `≥ 1 − η`,
  supplied by Theorem 4.5 in the paper. No independence assumptions are needed.

## Not formalized

* Theorem 2.7 ([ILPS22]) and Theorem 4.5 (reproducible median and quantile, sample complexity).
* Lemmas 4.2 and 4.4 ([IKY12]); Lemmas 4.7 and 4.8 (feasibility and approximation of
  MAPPING-GREEDY's output given an EPS); Lemma 4.9 apart from its refutation; Lemma 4.10 (sample
  complexity). Informal remark, not checked: in Lemma 4.7, the case `C = {(p_{j+1}, w_{j+1})}`
  assumes `j ≥ 1`. When the first sorted item of `Ĩ` is a synthetic small item heavier than `K`,
  `j = 0` and item `j + 1` has no index in `I`. This seems harmless, since then `OPT(I) < 3ε`.
