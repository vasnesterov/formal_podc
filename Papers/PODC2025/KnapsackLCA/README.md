# Local Computation Algorithms for Knapsack — PODC 2025

Clément L. Canonne, Yun Li, Seeun William Umboh. *Local Computation Algorithms for Knapsack:
impossibility results, and how to avoid them* (Brief Announcement). PODC 2025. DOI
[10.1145/3732772.3733515](https://doi.org/10.1145/3732772.3733515). Formalized version: arXiv
[2504.01543](https://arxiv.org/abs/2504.01543) v1 (full version); numbering follows it.

**Verdict: 🚨 Headline claim false.** The main positive result, Theorem 4.1 ("Algorithm 2
`LCA-KP` is an LCA giving access to a `(1/2, 6ε)`-approximate solution"), is false: on a
Knapsack instance whose items all have the same efficiency, `LCA-KP` answers "no" to every query,
with probability close to 1. Lemma 4.6, on which it rests, is false on the same instance. The
impossibility results (Lemma 3.1, Theorems 3.2–3.4) are true. Their proofs need repairs: the
reductions of 3.2/3.3 break the paper's own normalisation of the profits, and Lemma 3.5 in the
proof of 3.4 is not justified.

## Mistakes in the paper

* **Theorem 4.1 is false (headline), and so is Lemma 4.6.** Take `N` identical items with
  normalised profit and weight `1/N`. In integer form: weights `1`, weight limit `N/2`. Take
  `ε = 1/m` with `m ≥ 30` and `N ≥ m²`. All items are small with efficiency `1`, so the
  efficiency distribution that `rQuantile` samples is a point mass at `1`.
  - *Lemma 4.6.* Every set `A_k(I)` of Definition 4.3 is either empty or contains every item. So no
    equally partitioning sequence of length `t ≥ 1` exists, and the probability in Lemma 4.6 is
    `0`, not `≥ 1 − 13ε/36`. The proof of Lemma 4.6 turns `Pr[p/w > ẽ_k] ≤ kq + τ` into
    `Pr[p/w ≥ ẽ_k] ≤ kq + τ`, which ignores the mass of items with efficiency exactly `ẽ_k`.
    Nothing in the paper assumes distinct efficiencies.
  - *Theorem 4.1.* Suppose all quantiles are accurate, which by Theorem 4.5 happens with
    probability `≥ 1 − tβ ≥ 1 − ε/36`. Then every `1 − kq` lies in `(τ, 1 − τ)`, and every
    `ẽ_k = 1`. So every item of `Ĩ` is a copy of `(ε², ε²)` with efficiency `1`. CONVERT-GREEDY
    finds no index `k` with `ẽ_k > p_j/w_j = 1`, sets `e_small = −1`, and `LCA-KP` answers "no"
    to every query. This holds for any sample and any tie-breaking in the sort. The empty set is
    not a `(1/2, 6ε)`-approximation, since `OPT ≈ 1/2`. Even in the weakest, per-query reading of
    correctness, no seed-dependent `(1/2, 6ε)`-approximate solution agrees with each answer with
    probability `≥ 1 − ε`. Reading `>` as `≥` in Line 3 of Algorithm 3 does not help: `LCA-KP`
    then answers "yes" to every item, which is infeasible. The paper never assumes distinct
    efficiencies, and ties are built into the design: the synthetic items of `Ĩ` have efficiency
    exactly `ẽ_{k+1}`. (`Sec4.theorem_4_1_false`, `Sec4.answerKP_uniform`, `Sec4.no_eps_uniform`)
* **Theorems 3.2 and 3.3: the reduction leaves the paper's model; statements true.**
  Definition 2.2 normalises the total profit of an instance to `1`. The instance `I(x)` used in
  the reductions from `OR_{n−1}` has total profit `|x| + β`. Normalising it requires knowing
  `|x|`, so the reduction only applies to LCAs that are correct on unnormalised instances. We
  formalize the paper's reductions in that setting (`theorem_3_2`, `theorem_3_3`, bound `n/3` on
  `n + 1` items). We also prove the theorems for LCAs required to be correct only on normalised
  instances, with a different hard family and a direct argument. The first item of a block of
  `b = ⌊1/α²⌋ + 1` items takes the profit of the whole block. This gives the bound
  `⌊n/b⌋/3`, still `Ω(n)` for fixed `α`. (`theorem_3_2_normalized`, `theorem_3_3_normalized`)
* **Theorem 3.4: Lemma 3.5 is not justified, but the theorem is true with the paper's constant.**
  Lemma 3.5 claims that for each query `k` the default answer must be "yes". The argument is
  that answering "no" costs error `1/3 − 1/10 > 1/5`. But that error is conditional on the query
  being `k`, while the `1/5` bound is an average over all `k`. An algorithm may answer "no" on a
  constant fraction of the `k` and still meet the average bound. The lemma's hypotheses are in
  fact unsatisfiable (they contradict Theorem 3.4), so the lemma is vacuously true, but its proof
  does not show this. We replace it with a joint count. Let `y` be the fraction of default "yes"
  answers. The algorithm fails on a `½(1 − y) + ½(y² + (1 − y)²) − O(q/n) ≥ 7/16 − O(q/n)`
  fraction of the hard distribution. This gives `t(n) ≥ n/11` for every `n ≥ 2` with success
  probability `4/5`, the paper's constant, and `t(n) ≥ n/40 − 1/5` under the per-query reading.
  (`theorem_3_4`, `theorem_3_4_perQuery`, `LCA.count_le`)
* **Small slips.**
  - Theorem 3.4 says "`(t(n), 4/5)`-LCA", which is failure probability `4/5` by Definition 2.2.
    The proof uses success probability `4/5`, and we formalize that version. The literal version
    cannot follow from the paper's distribution: a 1-query algorithm that answers "yes" on a
    weight-`3/4` item with a random hash bit succeeds with probability `1/2 > 1/5` on it.
  - The proof of Theorem 3.4 draws `(i, j)` uniformly from `[n]²`, so `i = j` is possible, and
    then the weights are ill-defined. We use distinct pairs. Its weights `3/4, 1/4` are not
    integers, as Definition 2.2 requires. We scale them to `3, 1` with weight limit `4`.
  - Theorem 2.7 states the sample complexity with `Ω̃`; it should be `Õ`.
  - The approximation guarantee is stated inconsistently: `(1/2 + ε)` in Theorem 1.4, `(2 + ε)` in
    the technical overview, `(1/2, 6ε)` in Theorem 4.1.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Knapsack instance on `n` items (`Instance`): real profits, natural-number weights, weight limit
  `K`. `WellFormed` means non-negative profits and weights `≤ K`. `Normalized` additionally
  requires total profit `1`, as in Definition 2.2.
* Randomized LCA (`LCA`): a `PMF` over random seeds. For each weight limit, seed and query there
  is an adaptive query tree over the item oracle `i ↦ (p_i, w_i)` that outputs yes/no. Since the
  answer is a function of (instance, seed, query), the LCA is stateless, parallelizable and
  query-order oblivious by construction (Definitions 2.2–2.4). Complexity is the worst-case number
  of item queries per answer (`QueryBound`, the paper's `t(n)` as query complexity).
* Correctness is formalized in two readings. Per-query (`Correct`): there is a seed-dependent
  solution `C r` such that each single answer agrees with it and `C r` is valid with probability
  `≥ 1 − δ`. Global (`CorrectStrong`): the set of "yes" items is valid with probability `≥ 1 − δ`.
  Global implies per-query. Theorems 3.2 and 3.3 and the refutation of 4.1 use the weaker
  per-query reading, so they hold in both. Theorem 3.4 is proved in both readings.
* Lower bounds quantify over all randomized LCAs with arbitrary seed spaces. The easy direction
  of Yao's principle is an averaging lemma (`sum_mul_probReal_le`).
* Section 4: `LCA-KP` (Algorithm 2 with Algorithm 3) is modelled as a function of one run's random
  data: the sample `R`, the `rQuantile` outputs `ẽ_k`, and the sorting order of `Ĩ`. The only
  property of `rQuantile` used is the accuracy guarantee of Theorem 4.5. The probabilistic
  statement takes as hypothesis that each run is accurate with probability `≥ 1 − ε/36`, which is
  what Theorem 4.5 with `β = ε²/36` and `t ≤ 1/ε` calls gives.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (`R(OR_n) ≥ n/3`) | `lemma_3_1` (general: `Cslib.QueryTree.or_lower_bound`) | `Impossibility.lean` |
| Theorem 3.2 (paper's reduction, unnormalised) | `theorem_3_2` | `Impossibility.lean` |
| Theorem 3.3 (paper's reduction, unnormalised) | `theorem_3_3` | `Impossibility.lean` |
| Theorem 3.2, normalised instances | `theorem_3_2_normalized` | `Impossibility.lean` |
| Theorem 3.3, normalised instances | `theorem_3_3_normalized` | `Impossibility.lean` |
| Theorem 3.4 (success `4/5` ⇒ `t(n) ≥ n/11`) | `theorem_3_4` | `MaximalFeasible.lean` |
| Theorem 3.4, per-query reading | `theorem_3_4_perQuery` | `MaximalFeasible.lean` |
| Lemma 4.6 is false | `Sec4.no_eps_uniform` | `WeightedSampling.lean` |
| `LCA-KP` answers "no" everywhere | `Sec4.answerKP_uniform` | `WeightedSampling.lean` |
| Theorem 4.1 is false | `Sec4.theorem_4_1_false` (general: `Sec4.lcaKP_not_correct`) | `WeightedSampling.lean` |

**Not formalized.** Theorems 2.7 and 4.5 (reproducible median and quantile), Lemmas 4.2 and 4.4
(from [IKY12]), Lemmas 4.7, 4.8 and 4.10, and the Chernoff step of Lemma 4.6. None of them is
needed for the counterexample.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `exists_lca_optimal` and `exists_lca_maximalFeasible` give LCAs
satisfying the hypotheses of the lower bounds with `q = n`, so the bounds are tight up to
constants. `Sec4.accurate_one` shows that accurate quantile outputs exist for the
counterexample instance. The query model (`Cslib.QueryTree`: adaptive query trees, simulation,
the needle lemma, the `OR_n` bound, `PMF` probability helpers) is staged in
`Podc/Computability/QueryComplexity/QueryTree.lean` (CSLib candidate).
