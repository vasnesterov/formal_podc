# Simple and Local Independent Set Approximation — PODC 2018

Ravi B. Boppana, Magnús M. Halldórsson, Dror Rawitz. *Brief Announcement: Simple and Local Independent Set
Approximation.* PODC 2018. DOI [10.1145/3212734.3212793](https://doi.org/10.1145/3212734.3212793).
Formalized version: arXiv [1803.00786](https://arxiv.org/abs/1803.00786) v1 (full version; numbering follows it).

**Verdict: ❌ False claim.** The headline results hold: Boppana's algorithm / the Caro–Wei bound
achieves a tight `(Δ+1)/2` ratio (Theorem 1), and no 1-round randomized algorithm does better
(Theorem 4, after a repair of its proof). Theorems 3, 6 and 7 and Lemmas 2–4 also hold. **Theorem 2**
(ratio `(d̄+2)/1.657` in terms of the average degree) is false as stated: the proof gives the constant
`4(√2−1) = 1.65685…` and rounds it the wrong way. The paper's own extremal family refutes `1.657`, while
`4(√2−1)` is correct. There are also small statement slips: Theorem 1 at `Δ = 0`, Lemma 5 lacks `Y > 0`,
and Theorem 6 has `min_{x ≤ 1}`.

## Mistakes in the paper

* **Theorem 2 is false (wrong rounding of the constant).** It claims `α(G) ≤ (d̄+2)/1.657 · CaroWei(G)`
  for every graph. The proof ends with `(d̄+2)/(4(√2−1)) ≤ (d̄+2)/1.657`, but `4(√2−1) = 1.65685… < 1.657`,
  so the inequality goes the wrong way. Because the bound is asymptotically tight on bipartite graphs with
  regular sides and `τ ≈ 1/√2`, the rounded constant really fails. Example: `K_{24000,10000}` has
  `α = 24000` but `(d̄+2)/1.657·CaroWei ≈ 23999.2`. The smallest complete bipartite counterexample is
  `K_{13721,5683}`. We prove the statement with `4(√2−1)` in place of `1.657` (`theorem2_false`,
  `theorem2_corrected`). This is a borderline call between ❌ and ⚠️; see differencies.md.
* **Theorem 4's proof compares graphs that nodes can tell apart.** The proof says no 1-round algorithm
  can distinguish `K_{Δ+1}` from a `Δ`-regular bipartite graph. In the paper's model, however, nodes know
  `n`, and the two graphs have different sizes. The view also contains the port number at the neighbour's
  end, which the proof ignores. The theorem is true. Our repair uses `2k` copies of `K_{Δ+1}` versus `k`
  copies of `K_{Δ+1,Δ+1}` minus a perfect matching, on the same nodes, with matching port numbers at both
  ends of every edge. For each node `v`, a permutation fixing `v` maps its view in one graph to its view in
  the other, so averaging over labelings gives every node the same join probability in both graphs
  (`theorem4`, `theorem4_ratio`).
* **Lemma 5 lacks `Y > 0`.** As stated (`a > b > 0`, `Z − Y ≥ X > 0`) it is false: `a=2, b=1, X=1,
  Y=−100, Z=−50` gives a smaller value at `t = 0` than at `t = 1`. In its only use `Y = w(opt) > 0`, and
  with that hypothesis we prove it (`lemma5_false`, `lemma5`).
* **Theorem 1 at `Δ = 0`.** A ratio `(0+1)/2 < 1` is impossible on edgeless graphs. The theorem holds for
  every `Δ ≥ 1` (`theorem1_false_zero`, `theorem1`).
* **Typos and slips.**
  - Theorem 6: the minimum should be over `0 ≤ x ≤ 1`. Over `x ≤ 1` the expression takes negative
    values (`theorem6_min_unbounded`).
  - "For `Δ = 2`, … `ρ ∼ 1.657`" should be `≈ 1.686 = 1/0.593` (`rho_two_gt`).
  - The arXiv abstract says Boppana's algorithm is "only a `Δ`-approximation" on weighted graphs. The
    correct ratio is `Δ+1`, as §3 and the PODC abstract state; it exceeds `Δ` on `K_{Δ,Δ}` with weights
    `1, Q > Δ` (`boppana_weighted_not_Delta`).
  - §3 writes `E[w(B)] = Σ_{v∈B} …`, which should be `Σ_{v∈V}`.
  - Lemma 5 is applied with `t = W/X`, which is undefined when `V′ = ∅`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finite simple graphs (Mathlib `SimpleGraph`, `indepNum`). "`B` has performance ratio `ρ` for `Δ`"
  (`HasPerformanceRatio`) means `α(G) ≥ B(G) ≥ α(G)/ρ` for all finite `G` with `Δ(G) = Δ`.
  `HasTightPerformanceRatio` adds that no smaller ratio holds.
* Boppana's algorithm: a uniformly random ordering `σ : V ≃ Fin n`; the output is the set of vertices
  preceding all their neighbours. We prove its expected size is exactly `CaroWei(G)`.
* Theorem 4: synchronous message passing in CSLib's port-numbering model, one round. Nodes have unique
  labels from `Fin N` (any `N ≥ n`) and private i.i.d. random strings from an arbitrary distribution on a
  finite set. Messages and local computation are unbounded, and `n`, `Δ`, `N` are known. The algorithm
  must output an independent set with probability 1, but only on simple `Δ`-regular graphs with
  `n = 2k(Δ+1)` nodes. This is a weaker hypothesis than the paper's, so the theorem is stronger. Not
  covered: randomness with infinitely many outcomes (e.g. exact uniform reals).
* Weighted section: positive real weights. In `Max`, node `v` draws `x_v ∈ [0,1]` uniformly (product
  Lebesgue measure) and joins iff `x_v^{1/w_v}` beats all its neighbours. Lemma 2 is proved
  measure-theoretically.

**Main results in Lean.** (namespace `Podc.LocalISApproximation`)

| Paper | Lean | File |
|---|---|---|
| eq. (1)–(2): `E|Boppana| = CaroWei`, `α ≥ CaroWei` | `expected_card_boppana`, `caroWei_le_indepNum` | `Boppana.lean` |
| Theorem 1 (with tightness, `Δ ≥ 1`) | `theorem1`, `caroWei_ge_of_degree_le`, `regular_bipartite`, `boppana_ratio` | `Theorem1.lean` |
| Theorem 1 fails at `Δ = 0` | `theorem1_false_zero` | `Theorem1.lean` |
| Lemma 1 / `Turán ≤ CaroWei` | `turan_le_caroWei` (Mathlib `sq_sum_div_le_sum_sq_div`) | `Theorem3.lean` |
| Theorem 2 false; corrected | `theorem2_false`, `theorem2_corrected`, `four_mul_sqrt_two_sub_one_lt` | `Theorem2.lean` |
| Theorem 3 (with tightness) | `theorem3`, `indepNum_le_turan`, `tight_of_params`, `exampleGraph` | `Theorem3.lean` |
| Theorem 4 | `theorem4`, `theorem4_ratio`; non-vacuity `boppanaAlg_correct` | `Theorem4.lean` |
| Lemma 2, eq. (7) | `lemma2`, `expected_weight_max`, `maxSet_isIndepSet` | `Lemma2.lean` |
| Lemmas 3, 4, 5 | `lemma3`, `lemma4`, `lemma5`, `lemma5_false` | `Weighted.lean` |
| Theorem 6 | `theorem6` (`theorem6_upper`, `theorem6_tight`), `theorem6_min_unbounded` | `Theorem67.lean`, `Weighted.lean` |
| Theorem 7 | `theorem7`; `ρ(2)`: `rho_two_gt` | `Theorem67.lean` |
| §3 unchanged Boppana | `boppana_weighted`, `boppana_weighted_ratio`, `boppana_weighted_not_Delta` | `Weighted.lean` |

**Not formalized.** Theorem 5 (needs Alon's high-girth graphs), the claim inside Theorem 2's proof that
(6) is tight, the random-reals form (3) of Boppana's algorithm, and the streaming, online and Selkow/Sakai
remarks.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The model of Theorem 4 comes from CSLib `Cslib.Computability.Distributed.PortNumbering`.
Its hypothesis is satisfiable: `boppanaAlg` (random ranks with label tie-breaking) is a correct
algorithm.
CSLib candidates: the `DecidableRel` instance for `completeBipartiteGraph` and its degree lemmas
(`Theorem1.lean`), and `card_le_two_mul_indepNum`. Also `caroWei_le_indepNum` (Caro–Wei) and
`turan_le_indepNum` (Turán), neither of which is in Mathlib.
