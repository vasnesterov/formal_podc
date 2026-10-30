# Game Dynamics in the Population Protocol Model — PODC 2024

Dan Alistarh, Krishnendu Chatterjee, Mehrdad Karrabi, John Lazarsfeld. *Game Dynamics and Equilibrium
Computation in the Population Protocol Model.* PODC 2024. DOI
[10.1145/3662158.3662768](https://doi.org/10.1145/3662158.3662768). Formalized version: arXiv
[2307.07297](https://arxiv.org/abs/2307.07297) v3 (May 2024); numbering follows it.

**Verdict: ❌ False claim.** The upper bound on the mixing time of the `(k, a, b, m)`-Ehrenfest
process (Theorem 2.5) is false as stated: it ignores the laziness of the chain, and fails when
`a + b` is small. The explicit bounds of Lemmas A.5, A.8 and Proposition A.7 behind it are false too. The stationary distribution results are correct: Theorem 2.4, Propositions A.1
and A.3, the stationary part of Theorem 2.7 and Proposition 2.8. The `Ω(km)` mixing lower bound also
holds. The headline Theorem 2.7 survives, because its parameters satisfy `a + b = γ`, `m = γn`. Its
formula for `p_j` is exact only if the responder is drawn independently of the initiator (possibly
the initiator itself). Under the standard distinct-pair scheduler it is off by `O(1/n)`.

## Mistakes in the paper

* **Theorem 2.5 (upper bound) is false when `a + b` is small.** The theorem fixes any `a, b > 0` with
  `a + b ≤ 1` and claims `t_mix = O(k² m log m)` for `a = b`, and `O(min{k/|a−b|, k²} m log m)` for
  `a ≠ b`. But from `x = (m, 0, …, 0)` the chain stays put with probability `1 − a`. So `t_mix` grows
  like `1/a` as `a → 0`, while the claimed bound does not depend on `a` once `k, m` are fixed.
  Concretely, take `k = m = 2` and `a = b = ε`. Then `P(x, x) = 1 − ε` and `π(x) = 1/4`, so
  `d(t) ≥ (1 − ε)^t − 1/4`, and `d(t) ≤ 1/4` forces `t ≥ 1/(2ε)`. The same happens for `a = 2b = 2ε`,
  where `min{k/|a−b|, k²} = k²`. The error is in Proposition A.7. For `a = b`, the process
  `Z_t² − t` is not a martingale (the right one is `Z_t² − 2at`), so `E[τ_absorb] = k²/(2a)`, not
  `k²`. The claim "the right-hand side of (26) is at most `k²`" fails in the same way: it tends to
  `k²/(a+b)` as `a − b → 0`. Every `k²` term needs a factor `1/(a+b)`; the `k/|a−b|` branch is
  correct. In the application (Theorem 2.7), `a + b = γ` and `m = γn`, so `(k²/γ)·m log m ≤ k² n log n`
  and Theorem 2.7's bound is not affected. If one reads the `O` of Theorem 2.5 as allowing constants that
  depend on `a, b`, the theorem itself survives, but the explicit `|a − b|` shows that the bound is meant
  uniformly in `a, b`. In any case the constant-free numbered statements behind it are false. Proposition
  A.7 claims `E[τ_absorb] ≤ k²` for `a = b`, but the truth is `k²/(2a)`. Lemma A.5 claims `E[τ_coal] ≤ k²`; for
  `k = 2`, `z = 1`, `w = 2` the walks coalesce at the first non-null step, so `E[τ_coal] = 1/(a+b)`.
  Lemma A.8 claims `Pr[τ_couple > 2Φ log(4m)] ≤ 1/4`, hence `d(2Φ log(4m)) ≤ 1/4`. Take the fixed values
  `k = m = 2`, `a = 1/100`, `b = 1/200`. Then `Φ = 8` and `2Φ log₂ 8 = 48`, but `d(t) > 1/4` for all
  `t ≤ 48`. (`theorem_2_5_upper_false`, `theorem_2_5_upper_false_ne`, `lemma_A_8_false`)
* **Theorem 2.7: the formula `p_j ∝ (1/β − 1)^{j−1}` depends on the sampling convention.**
  Section 2.2.1 says the initiator, at level `j`, meets a non-AD agent with probability
  `(z_j/n)(1 − β)`. That is exact only if the responder is drawn uniformly from all `n` agents,
  independently of the initiator (a GTFT agent may "meet itself"). With the standard
  population-protocol scheduler (an ordered pair of *distinct* agents, as in the paper's
  references), the count process is still exactly an Ehrenfest process. But its parameters are
  `a' = γ(n−1−βn)/(n−1)` and `b' = γβn/(n−1)`. So the stationary law is multinomial with ratio
  `λ' = (n−1−βn)/(βn) = (1/β − 1) − 1/(βn)`, not `1/β − 1`. Example: one AD and two GTFT agents,
  `k = 2`. The paper's law gives `π(2,0) = 1/9`; the true stationary law gives `1/4`. We count this as
  an implied-assumption issue (the paper's own computation fixes the convention); the formula is
  exactly right in that model. (`distinct_counterexample`; positive result: `theorem_2_7_stationary`)
* **Proposition A.9: "`D ≥ km`" is off by one urn.** The graph diameter is `(k−1)m`: each ball
  moves at most `k − 1` urns. For example, `k = m = 2` gives the path `(2,0) – (1,1) – (0,2)` with
  `D = 2 < 4`. The conclusion `t_mix = Ω(km)` holds: we prove `t_mix ≥ (k−1)m/2` for all `a, b`.
  (`theorem_2_5_lower`)
* **Proof gaps with true statements.** (i) Theorem 2.4 calls the multinomial "the unique stationary
  distribution", but detailed balance gives only stationarity. Uniqueness needs irreducibility,
  which is argued only for `k = 2, 3` ("easy to see"); we prove it for all `k`
  (`ehrenfest_isIrreducible`). (ii) Theorem 2.7 also claims a lower bound `t_mix ≥ Ω(kn)`, but
  Theorem 2.5 gives only `Ω(km) = Ω(kγn)`. This is `Ω(kn)` only for constant `γ` (not formalized).
* **Typos and slips.** Definition 2.3 writes `P : Δ_k^m → Δ_k^m` for a matrix on `Δ_k^m × Δ_k^m`.
  In A.3, the index runs over "`j = 0, …, k − 1`" (it should be `j ∈ [k−1]`), and an "inequality"
  should be "equality". Remark A.2 says `Δ_k^m` for `Δ_2^m`. In Proposition A.6, `Z` is initialized
  both to `z` and to `0`. Lemma A.8 needs `log = log₂`. Contribution (ii) in §1.2 says
  `O(kn log n)` for `β ≠ 1/2`, hiding the factor `1/|1 − 2β|` of Theorem 2.7.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finite discrete-time Markov chains are row-stochastic real matrices, as in CSLib's
  `Cslib.Probability.Markov`. A stationary distribution is a probability vector with `π P = π`.
  Mixing is `d(t) ≤ 1/4` (`IsMixedAt`, total variation, maximum over starting states). We state
  "`t_mix ≤ T`" as "some `t ≤ T` has `d(t) ≤ 1/4`", so we never need `sInf`.
* The `(k, a, b, m)`-Ehrenfest process is defined on `Δ_k^m` as an *urn chain*. With probability
  `r(i,j)·x_i/m`, one ball moves from urn `i` to urn `j`. The rates are `a` for `j → j+1` and `b`
  for `j+1 → j`. Lemmas `ehrenfest_apply_up/down/self/other` check entrywise that this is exactly
  Definition 2.3. Urn `j` of the paper is index `j − 1 ∈ Fin k`.
* The `k`-IGT dynamics (Definition 2.1) is a one-way CSLib population protocol (`igt k`) on states
  AC / AD / GTFT(level). Agent kinds are fixed by `τ : A → Kind` (an `(α, β, γ)` population with
  `n = |A|`). There are two random schedulers: `replKernel` draws the initiator and the responder
  independently and uniformly, which is the model behind (5). `distinctKernel` draws an ordered
  pair of distinct agents, the standard PP scheduler (CSLib's `uniformKernel`). Exactly one
  interaction happens per step.
* The count vector `z^t` is `counts`. "`{z^t}` is the Ehrenfest process" is proved as exact
  lumpability. For every start configuration `C`, every `t` and every `y`, `P[z^t = y]` equals the
  `t`-step Ehrenfest probability from `z(C)` to `y`.
* Our Theorems 2.4/2.7 and Propositions A.1/A.3 hold for all `k ≥ 1` and `m ≥ 0`. The paper needs
  `k, m ≥ 2`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.3 (entries of `P`) | `ehrenfest`, `ehrenfest_apply_up/down/self/other`, `ehrenfest_mem` | `Ehrenfest.lean` |
| Thm 2.4 (stationary law, existence) | `ehrenfest_isStationary`, `ehrenfest_detailedBalance` | `Ehrenfest.lean` |
| Thm 2.4 (uniqueness + identification) | `theorem_2_4`, `ehrenfest_stationary_unique` | `Ehrenfest.lean` |
| Irreducibility (A.1/A.2 "easy to see") | `ehrenfest_isIrreducible` | `Ehrenfest.lean` |
| PMF of A.3 | `multinomialPMF_ehrParam` | `SmallK.lean` |
| Prop. A.1 / Remark A.2 (`k = 2`) | `proposition_A_1` | `SmallK.lean` |
| Prop. A.3 / Remark A.4 (`k = 3`) | `proposition_A_3` | `SmallK.lean` |
| Def. 2.1 (`k`-IGT) | `igt`, `step`, `counts` | `IGT.lean` |
| §2.2.1: `{z^t}` is an Ehrenfest process | `schedKernel_lump`, `replKernel_counts` | `IGT.lean` |
| Thm 2.7, stationary part | `theorem_2_7_stationary` | `IGT.lean` |
| Thm 2.7 under distinct-pair sampling | `distinctKernel_counts`, `distinct_counterexample` | `IGT.lean` |
| Mean of the multinomial (`E[π_j] = m p_j`) | `sum_mul_multinomialPMF` | `Generosity.lean` |
| Prop. 2.8 | `proposition_2_8` | `Generosity.lean` |
| Thm 2.5, lower bound (Prop. A.9) | `theorem_2_5_lower` (`t_mix ≥ (k−1)m/2`) | `Mixing.lean` |
| Thm 2.5, upper bound — false | `theorem_2_5_upper_false` (`a = b`), `theorem_2_5_upper_false_ne` (`a ≠ b`) | `Mixing.lean` |
| Lemma A.8 (`d(2Φ log(4m)) ≤ 1/4`) — false | `lemma_A_8_false` | `Mixing.lean` |

**Not formalized.** The corrected Theorem 2.5 upper bound (coupling, Lemmas A.5, A.8); the
mixing-time bounds and the convergence claim of Theorem 2.7; Proposition 2.2 and Theorem 2.9
(game payoffs, ε-approximate distributional equilibrium); Appendices B–D.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the hypotheses of `theorem_2_7_stationary` hold for the 3-agent
population `τ₀` (an `example` in `IGT.lean`), and `ehrenfest_isStationary` gives the stationary
distribution that `theorem_2_4` and `proposition_2_8` assume. The PP model is CSLib's
`Cslib.PopulationProtocol.Protocol`. Markov-chain lumping is `Cslib.Probability.Markov`. New
shared infrastructure (CSLib candidates) is in `Podc/Probability/Markov/Stationary.lean`
(stationarity, detailed balance, uniqueness for irreducible chains) and
`Podc/Probability/Markov/Mixing.lean` (total variation, `d(t) ≤ 1/4`, diameter lower bound).
