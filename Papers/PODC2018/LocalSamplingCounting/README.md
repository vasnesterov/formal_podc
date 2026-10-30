# On Local Distributed Sampling and Counting — PODC 2018

Weiming Feng, Yitong Yin. *On Local Distributed Sampling and Counting.* PODC 2018. DOI
[10.1145/3212734.3212757](https://doi.org/10.1145/3212734.3212757). Formalized version: arXiv
[1802.06686](https://arxiv.org/abs/1802.06686) v1; numbering follows it.

**Verdict: ❌ False claim.** Corollary 5.2 is false as stated. It is a by-product, not a headline
result. Strong spatial mixing (SSM) with exponential decay in total variation does **not** imply
SSM in multiplicative error. The hardcore model is a counterexample, and it is the paper's own
main application. The probabilistic and locality cores of the main results do hold: Theorem 3.2
(sampling from inference), Theorem 3.4, the boosting Lemma 4.1, the correctness of the local JVV
sampler (Claims 4.5–4.7, Lemma 4.8), and both directions of Theorem 5.1. We had to repair a few
proof steps and fix one typo in the JVV algorithm along the way.

## Mistakes in the paper

* **Corollary 5.2 (TV-SSM ⇒ multiplicative SSM) is false.** The multiplicative error (2) is
  `err = max_x |ln μ(x) − ln μ̂(x)|`, and the only convention is `ln 0 − ln 0 = 0`. In the hardcore
  model, let `u` be a neighbour of `v`. Pin `u` to *occupied* (`σ`) and to *unoccupied* (`τ`). Then
  `μ^σ_v(occupied) = 0` while `μ^τ_v(occupied) > 0`, so `err(μ^σ_v, μ^τ_v) = ∞`. No rate
  `δ_n(1) = poly(n)·α` can bound it. The class of hardcore models on perfect matchings (every even
  `n`) meets every hypothesis of the corollary. Its members are locally admissible, their constraints have
  diameter 1, and they have TV-SSM with `δ_n(d) = 2·(1/2)^d`. Yet they have no multiplicative SSM,
  whatever the rate (`corollary_5_2_false`). On any graph with an edge the hardcore model has no
  multiplicative SSM (`hardcore_err_infinite`, `hardcore_not_mssm`). The counterexample keeps `v` free
  and changes only a neighbour, so it does not rely on the trivial case `v ∈ D`, where `err = ∞` for
  every distribution. The paper itself says the hardcore model has SSM with
  exponential decay in the uniqueness regime, so Corollary 5.2 would contradict this. Large weights
  break it with soft constraints alone too, so the true statement can only bound `err` once
  `poly(n)·α^d` is small. There is a second problem. The paper's route (Theorem 5.1 ⇐, then Lemma 4.1,
  then Theorem 5.1 ⇒ for `err`) gives locality `2t + ℓ`. It therefore proves decay only at rate `√α`,
  not `α`. We believe the same `α` can be recovered at large distances by a direct pinning
  argument, but we did not formalize this. The easy direction (multiplicative ⇒ TV, same rate)
  holds, because `d_TV ≤ err` (`ssm_of_mssm`).
* **Local JVV sampler: acceptance and rejection are swapped (typo, ⚠️).** §4.2.1 lets node `vᵢ` set
  `F'_{vᵢ} = 1` with probability `q_{vᵢ}` and fail when `F'_{vᵢ} = 1`. Lemma 4.8 says the
  algorithm "fails with probability at most `∑ E[F'_{vᵢ}] = 1 − O(1/n)`". Since
  `q_{vᵢ} ≥ e^{−5/n²}`, this algorithm would fail almost surely. The proof uses
  `Pr[success | Y = σ] = ∏ q_{vᵢ}(σ)`, so the intended reading is: accept with probability
  `q_{vᵢ}`, and fail with probability `O(1/n)`. We formalize this version (`lemma_4_8_success`,
  `lemma_4_8`).
* **Lemma 4.1, proof of the Claim: a wrong inequality (proof repaired).** The paper writes
  `μ_{Λᵢ∪{v}}(τᵢᶜ) = μ_{Λᵢ₋₁∪{v}}(τᵢ₋₁ᶜ)·μ^{τᵢ₋₁ᶜ}_{vᵢ}(cᵢ) ≥ μ^{τᵢ₋₁ᶜ}_{vᵢ}(cᵢ)`. The first factor
  is a probability, so the inequality goes the other way. Only positivity is needed, and positivity
  follows from the induction hypothesis together with (4) and (5). The bound (3) is correct
  (`lemma_4_1_core`, `lemma_4_1`).
* **Theorem 5.1 (⇒): `min` should be `inf`, with `inf ∅ = ∞`.** The rate
  `δ_n(t) = 2 min{δ | t(n, δ) ≤ t − 1}` need not be attained. For small `t` the set is empty. We
  prove the statement with the infimum, using `[0, ∞]`-valued rates (`theorem_5_1_forward`).
* Small slips:
  * In the Claim of Lemma 4.1, "`dist_G(v, v_{i−1}) > t`" and "at node `v_{i−1}`" should read `vᵢ`.
  * In the proof of (3), "`m = |Λ| ≤ n`" should read `m = |Γ|`.
  * In Claim 4.6, `Γ` uses `B_t(v)` for `B_t(vᵢ)`, and the pinnings `τ₁, τ₂` are implicitly
    combined with `τ`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A joint distribution over `Σ^V` (`V`, `Σ` finite) is a nonnegative weight `w : (V → Σ) → ℝ`.
  A partial configuration `τ ∈ Σ^Λ` is a pinning `τ : V → Option Σ`. Conditional marginals `μ^τ_v`
  (`marg`), conditional distributions `μ^τ` (`cond`), TV distance (`tv`) and multiplicative error
  (`MultClose`) are all finite sums. Gibbs distributions are products of factors with finite scopes
  (`Factor`, `gibbsW`). Locality (Definition 2.4) is `GibbsLocal G F ℓ`, i.e. every scope has
  diameter `≤ ℓ` in `G`. Local admissibility (Definition 2.5) is `LocallyAdmissible`.
* **LOCAL model, per instance.** The instance `(G, x)` is fixed. An inference algorithm is a
  function from pinnings to answers at each node. It is `r`-local (`IsLocalAlg`) if its answer at
  `v` depends only on the pinning within distance `r` of `v`; the rest of `(G, x)` is fixed and
  known. Randomness is removed as in Proposition 3.3. Where we *assume* an algorithm
  (Theorem 5.1 ⇒, Lemma 4.1), this hypothesis is weaker than true LOCAL locality, so the results are
  stronger. Where we *build* an algorithm (Theorem 5.1 ⇐, Lemma 4.1), it is local in the pinning, and
  its output is given by an explicit formula that uses only the factors inside the ball
  (`marg_eq_local`, Proposition 2.1).
* **Sampling.** The SLOCAL samplers are modelled through their output distributions, for an
  arbitrary scan order. `seqProb A l τ σ` is the probability that the sequential sampler outputs
  `σ` (product formula (10)). The JVV rejection step (§4.2.3) is modelled abstractly: we take
  `μ̂` with multiplicative error `δ` (Claim 4.5), the ground state, the feasible path
  `σ₀, …, σₙ = σ` (Claim 4.6), and the acceptance probabilities (9).
* SLOCAL→LOCAL simulation via network decomposition (Lemmas 3.1, 4.4, cited from Ghaffari–Kuhn–Maus)
  is not formalized. Round counts are therefore formalized only as localities.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 3.2 (sampler TV error `≤ δ` with per-step error `δ/n`) | `theorem_3_2`, `theorem_3_2_tv` | `Sampler.lean` |
| Chain rule (exact marginals ⇒ exact sampling) | `seqProb_marg` | `Sampler.lean` |
| Thm 3.4 (inequality chain) | `theorem_3_4_tv` | `Sampler.lean` |
| Prop 2.1 (spatial Markov property, local formula) | `marg_eq_local` | `Gibbs.lean` |
| Lemma 4.1, eq. (3) and Claim (probabilistic core) | `lemma_4_1_core` | `Boosting.lean` |
| Lemma 4.1 (boosting lemma, `(2t+ℓ)`-local algorithm) | `lemma_4_1`, `boostAlg_isLocal` | `BoostingLocal.lean` |
| Claim 4.5 | `claim_4_5` | `Sampler.lean` |
| Claim 4.6 (core step) | `claim_4_6_core` | `JVV.lean` |
| Claim 4.7 (bounds `e^{−5/n²} ≤ q ≤ 1`) | `claim_4_7_bounds` | `JVV.lean` |
| Lemma 4.8 (success prob., exact output) | `lemma_4_8_success`, `lemma_4_8_joint`, `lemma_4_8` | `JVV.lean` |
| Thm 5.1 (⇒) | `theorem_5_1_forward`, `theorem_5_1_forward_pointwise` | `SSM.lean` |
| Thm 5.1 (⇐) | `theorem_5_1_converse`, `ssmAlg_isLocal` | `SSM.lean` |
| Cor 5.2 (⇐ direction, true) | `ssm_of_mssm`, `tv_le_of_multClose` | `SSM.lean` |
| Cor 5.2 (⇒ direction) **false** | `corollary_5_2_false`, `hardcore_err_infinite`, `hardcore_not_mssm` | `Counterexample.lean` |

**Not formalized.**
* Lemmas 3.1 and 4.4 (cited) and Proposition 3.3 (derandomization). We do have the convexity it
  uses, `tv_mix_le`.
* The composition into Theorem 4.2 / Proposition 4.3, including the locality `3t + ℓ` of `q_{vᵢ}`
  (eqs. (11), (12)).
* Corollary 5.3 and the applications. They are round-count bookkeeping on top of the formalized
  statements plus the cited SSM results.
* A repaired Corollary 5.2 with the same rate `α`.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: the hardcore model on perfect matchings meets all hypotheses of
Theorem 5.1 (⇐) (`matching_inference`), and it is locally admissible (`hardcore_locallyAdmissible`)
and local (`hardcore_gibbsLocal`). Everything is self-contained on top of Mathlib (no CSLib
modules are used). CSLib candidates (marked `-- CSLib candidate`) are the finite
distributions/pinnings/TV API (`Basic.lean`), the sequential-sampler coupling bound (`Sampler.lean`)
and Gibbs factors with the spatial Markov property (`Gibbs.lean`).
