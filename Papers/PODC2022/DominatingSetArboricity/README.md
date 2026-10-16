# Distributed Dominating Set in Bounded Arboricity Graphs — PODC 2022

Michal Dory, Mohsen Ghaffari, Saeed Ilchi. *Near-Optimal Distributed Dominating Set in Bounded
Arboricity Graphs.* PODC 2022. DOI [10.1145/3519270.3538437](https://doi.org/10.1145/3519270.3538437).
Formalized version: arXiv [2206.05174](https://arxiv.org/abs/2206.05174) v1 (full version with the
appendix); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main results hold:
- the deterministic `(2α+1)(1+ε)`-approximation for weighted MDS (Theorem 1.1; Theorem 3.1 for unit weights);
- the randomized `α + O(α/t)` approximation (Theorem 1.2);
- the general-graph bound of Theorem 1.3;
- the combinatorial reduction behind the lower bound (Theorem 1.4).

No stated result is false. Four places in the proofs need repair:
- Theorem 1.3's arithmetic fails for large `k`; a different algorithm covers that regime.
- The algorithm in the proof of Observation A.1 fails on `K₂`.
- Lemma 4.6 is under-specified at `λ = 1`.
- Lemma 4.7's bound for adaptive processes is not justified.

## Mistakes in the paper

* **Theorem 1.3's arithmetic fails for large `k`.** The proof uses Lemma 4.6 with `γ = Δ^{1/k}`, which yields the
  factor `γ(γ+1)⌈log_γ(Δ+1)⌉`. This is `≤ Δ^{1/k}(Δ^{1/k}+1)(k+1)` only if `(Δ+1)^k ≤ Δ^{k+1}`, and `γ > 1`
  needs `Δ ≥ 2`. For `Δ = k = 2`, `⌈log_{√2} 3⌉ = 4`, so the proof gives about 13.7 instead of the claimed 10.2.
  *Severity:* proof gap, statement true. In the uncovered regime the claimed factor is at least `Δ + 1`, and the
  trivial one-round algorithm "every node picks a lightest node of `N⁺_v`" achieves `Δ + 1`. (`logb_gap`,
  `claimed_factor_ge`, `trivial_approx`; combined statement `theorem_1_3_full`)
* **Observation A.1: the algorithm in the proof fails on `K₂`.** The observation claims that *some*
  single-round 3-approximation exists on graphs of arboricity 1, and this is true. But the algorithm of the
  proof, "take all non-leaf nodes" (also stated in the introduction for trees), outputs nothing on a single
  edge `K₂`, since both nodes are leaves. If "non-leaf" means "degree ≥ 2", isolated vertices are missed too.
  *Severity:* proof gap, statement true. *Fix:* also output the larger-ID endpoint of every `K₂` component;
  this is still one round. The paper's parent/grandparent charging then gives the factor 3. It needs only an
  orientation of out-degree ≤ 1, so pseudoforests are covered too. (`obsA1_proof_alg_fails_K2`,
  `observation_A_1_fixed`)
* **Lemma 4.6 is under-specified at `λ = 1`.** The lemma says "for `λ > 0`". Its input is "the output of
  Lemma 4.1", which forces `λ < 1`, but this is not stated. Taken literally with `λ = 1`, there are
  `⌈log_γ λ⁻¹⌉ = 0` phases, so `S'` is empty. Example: a single vertex with `w = x = 1` and `S = ∅`. We assume
  `λ < 1`, which every application satisfies. The lemma also writes `E[w_{S'}] = …` where `≤ …` is meant.
  (`lemma_4_6_false_lam_one`, `lemma_4_6_dominating`)
* **Lemma 4.7: missing justification for adaptivity.** The proof bounds `E[c_v]` via "the sequence
  `d_1 ≥ … ≥ d_r` that maximizes `E[c_v]`". But the `d_i` are random and depend on earlier coin flips, and the
  proof does not explain why a bound for every fixed sequence bounds the expectation. A standard argument closes
  the gap, since the coins are fresh in every iteration. We prove Lemmas 4.7 and 4.8 together by backward
  induction with the potential `γ ∑_{v undominated} x_v (p_i d_v + γ)`, using `(1-p)^d (1+pd) ≤ 1`.
  (`lemma_4_6_expect`)
* **Minor slips:**
  - Lemma 4.1 and Theorem 1.1 need `α ≥ 1`. For `α = 0` the parameter `λ = 1/((2α+1)(1+ε))` violates
    `λ < 1/((α+1)(1+ε))`; arboricity-0 graphs are edgeless and trivial.
  - The round bound `O(log(Δ/α)/ε)` should be `O(1 + log(Δ/α)/ε)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Graphs are finite simple graphs `SimpleGraph V` with nonnegative real weights. "Arboricity `≤ α`" is
  `G.ArboricityLE α`: the edges are covered by `α` forests. The algorithmic theorems assume the weaker
  hypothesis `G.OutOrientation α`, an orientation with out-degree `≤ α`, as allowed by footnote 2 of the
  paper. Observation 3.5 (`ArboricityLE.hasOutDegLE`) connects the two. The orientation is used only in the
  analysis.
* *Deterministic algorithm (Theorem 1.1).* The model is synchronous LOCAL with unique identifiers: CSLib's
  `Cslib.LocallyIterative`, where a node's new state is a function of the round number, its own state, and
  the set of its neighbours' states, which include their IDs. Nodes know `Δ`, `α`, `ε`, as in the paper. We
  prove that the run outputs exactly the set `detDS` of the centralized description after `2r + 2` rounds,
  and we bound `r`. CONGEST message sizes are not formalized; each message holds `O(1)` numbers (see
  `Distributed.lean`).
* *Randomized algorithm (Lemma 4.6, Theorems 1.2, 1.3).* This is a centralized round-by-round description in
  which nodes flip independent Bernoulli(`p_k`) coins in each step. The expectation is the exact finite
  expectation over all coin vectors, computed by backward recursion. Domination is proved for every coin
  outcome.
* *Lower bound (Theorem 1.4).* The KMW lower bound for fractional vertex cover is external and not formalized.
  We formalize the combinatorial reduction: the construction, arboricity `≤ 2`, the degrees, both directions of
  the approximation transfer, and the locality of the simulation.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (weak duality) | `sum_le_wt_of_isPacking` | `Basic.lean` |
| Observation 3.5 | `SimpleGraph.ArboricityLE.hasOutDegLE` | `Cslib/Foundations/Combinatorics/SimpleGraph/Arboricity.lean` |
| Lemma 4.1 (and Lemma 3.2 for `w ≡ 1`) | `lemma_4_1`, `numIter_le`, `charging` | `PartialDS.lean` |
| Theorem 1.1 (approximation) | `theorem_1_1`, `theorem_1_1_arboricity`, `numIter_detLam_le` | `Deterministic.lean` |
| Theorem 3.1 / Claim 3.3 | `theorem_3_1` | `Deterministic.lean` |
| Theorem 1.1 (distributed, round count) | `distributed_theorem_1_1`, `run_out_eq_detDS` | `Distributed.lean` |
| Lemma 4.6 (domination) | `lemma_4_6_dominating` | `Randomized.lean` |
| Lemmas 4.6–4.8 (expected weight) | `lemma_4_6_expect` | `Randomized.lean` |
| Lemma 4.6 at `λ = 1` (counterexample) | `lemma_4_6_false_lam_one` | `Lemma46Counterexample.lean` |
| Theorem 1.2 | `theorem_1_2_full` (combined, needs `α ≥ 2`); parts: `theorem_1_2` (explicit), `theorem_1_2_arith`, `theorem_1_2_rounds_arith` | `Main.lean`, `Randomized.lean`, `Theorem12Asymptotic.lean` |
| Theorem 1.3 | `theorem_1_3_full` (combined); parts: `theorem_1_3`, `theorem_1_3_param`, `claimed_factor_ge`, `trivial_approx`; gap: `logb_gap` | `Main.lean`, `Randomized.lean`, `Theorem13Gap.lean` |
| Theorem 1.4 (reduction) | `lbGraph_arboricityLE_two`, `lbGraph_degree_le`, `exists_dominating_lbGraph`, `fracCover_of_dominating`, `edist_host_le`, `reduction` | `LowerBound.lean` |
| Observation A.1 | `observation_A_1_fixed`; proof's algorithm fails: `obsA1_proof_alg_fails_K2` | `Forest.lean` |

The asymptotic form of Theorem 1.2 assumes `α ≥ 2`: for `α = 1` the condition `t ≤ α/log α` is undefined,
and the extension cost grows like `log t`. The explicit bound `theorem_1_2` holds for all `α ≥ 1`.

**Not formalized.**
* The KMW lower bound itself, and the transformation of an `R`-round algorithm on `H` into one on `G`. Only
  the fact that the simulation map does not increase distances is proved.
* Remarks 4.4 and 4.5 (unknown `Δ` or `α`).
* CONGEST bit complexity.
* A locally-iterative implementation of the randomized algorithm.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity:
- every graph has an orientation with out-degree `≤ Δ` (`trivialOrientation`), and forests are covered via
  Observation 3.5;
- the hypotheses of Lemma 4.6 are met by the output of Lemma 4.1 (`theorem_1_2`) and by the trivial packing
  (`theorem_1_3`);
- the lower-bound graph satisfies everything that is claimed of it.

CSLib candidates:
- the finite product-coin expectation toolkit in `Randomized.lean` (`coinProb`, `expect`, `Ec`,
  `expect_le_of_super`);
- dominating sets, packings and weak duality (`Basic.lean`).

The distributed model comes from CSLib `Cslib/Computability/Distributed/Local/LocallyIterative.lean`.
Arboricity, orientations, Observation 3.5 and rank-based acyclicity are in CSLib,
`Cslib/Foundations/Combinatorics/SimpleGraph/Arboricity.lean`.
