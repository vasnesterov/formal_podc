# Fault-Tolerance in Distributed Optimization: The Case of Redundancy — PODC 2020

Nirupam Gupta, Nitin H. Vaidya. *Fault-Tolerance in Distributed Optimization: The Case of
Redundancy.* PODC 2020. DOI [10.1145/3382734.3405748](https://doi.org/10.1145/3382734.3405748).
Formalized version: the proceedings version (there is no arXiv version). Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** Theorem 2 (linear convergence of gradient descent with the CGC
filter under 2f-redundancy) is fully proved; its part (i) `ρ ≥ 0` fails only in the degenerate case
`W* = ℝ^d`. Theorem 1 ("2f-redundancy is necessary") is under-specified. Read literally it is
vacuous. Read as what its proof shows (indistinguishability), it is true and tight, provided exactly
`f` agents are faulty and `n > 2f`; we prove this repaired form in both directions.

## Mistakes in the paper

* **Theorem 1 is under-specified.** Definition 2 does not say on which inputs the algorithm must be
  correct. There are three readings.
  - *(a) Literal: vacuous.* The proof turns the faulty agents' functions into honest functions of a
    second execution, so it asks for correctness on all executions. In that model no deterministic
    algorithm is f-resilient once `f ≥ 1`, so "f-resilient ⇒ 2f-redundant" holds trivially. Even a
    2f-redundant execution is confused there. Example: `n = 3`, `f = 1`, received `x², x², (x−2)²`;
    honest agents {0, 1} (minimum 0) vs. {1, 2} (minimum 1). The partner `x², (x−2)²` has no common
    minimum point. (`theorem1`, `no_resilient_allExecs`, `redundant_execution_confusable`)
  - *(b) Sharp: false, but not claimed by the paper.* "An algorithm that is f-resilient on all
    2f-redundant inputs cannot also be f-resilient on a non-redundant input." Counterexample in the
    paper's sensing setting: `n = 3`, `f = 1`, honest costs `x²` and `y²` on `ℝ²`. More generally,
    any execution whose honest costs share a minimum point can be added to the 2f-redundant class.
    The paper never states this reading, so it is not an error of the paper. It does show that
    2f-redundancy is not a maximal solvable class. (`sharp_necessity_false`,
    `exists_resilient_redundant_insert`)
  - *(c) Indistinguishability: true and proved.* This is what Part II actually shows. Let `f ≥ 1`,
    `2f < n`, exactly `f` agents faulty, and suppose the honest costs share a minimum point. Then the
    execution is not 2f-redundant iff the faulty agents can send convex differentiable functions such
    that another execution yields the same received vector, has honest costs with a common minimum
    point, and has a solution set disjoint from the true one. Then no deterministic algorithm is
    correct on both. The (⇒) direction is the paper's construction with `C_B = ‖x − ŵ‖²`. For (⇐),
    the two honest sets share `≥ n − 2f` agents, and the partner's common minimum point solves that
    subset, hence by 2f-redundancy the true execution. (`theorem1_indistinguishable`)
* **Part II assumes exactly `f` faulty agents** ("Then `|H| = n − f`"). With fewer faults reading
  (c) is false. Take `n = 3`, `f = 1`, no faulty agent, costs `x², y², x² + y²` on `ℝ²`. The
  execution is not 2f-redundant, yet every execution producing the same received vector has the
  origin as a solution. Classification: false statement under reading (c); the repair is "exactly
  `f` faulty agents". (`theorem1_indistinguishable_false_fewer_faults`)
* **Theorem 1 needs `n > 2f`**, which is used in the proof but not stated. For `n = f = 1` the
  statement is false. Definition 1 then includes the empty subset, so a single honest agent with cost
  `x²` violates 2f-redundancy, while "output a minimum point of the received function" is
  f-resilient. False only in a degenerate case. (`theorem1_false_n_eq_one`)
* **Theorem 2 (i), `ρ ∈ [0, 1)`, fails when `W* = ℝ^d`** (e.g. all honest costs constant). Appendix B
  derives `λ ≤ μ` from a point outside `W*`. Without one, `λ` is unconstrained: `n = 3`, `f = 1`,
  `μ = 1`, `λ = 30`, `η = 29/3 < η̄ = 58/3` give `ρ = −840`. Part (ii) is trivially true there. False
  only in a degenerate case. (`theorem2_rho_nonneg_false`; (i) under `W* ≠ ℝ^d`:
  `theorem2_rho_nonneg`)
* **Smaller gaps.**
  - Existence of minimum points is assumed tacitly. Definition 2 and the projection in Assumption 4
    need `W* ≠ ∅`.
  - The step (29) ⇒ (30) ("every honest gradient vanishes on `W*`") needs `f ≥ 1`. For `f = 0` it
    fails, but Theorem 2 still holds via the Lipschitz bound on the aggregate gradient.
  - "2f-redundancy implies `n > 2f`" (Appendix B) does not follow from Definition 1.
  - The hypothesis `α > 0` of Theorem 2 is implied by `0 < η < η̄`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Theorem 1 model.* This is the paper's "best case for the server". There are `n` agents and at most
  `f` Byzantine ones. The server gets one cost function per agent and applies a deterministic map
  `alg`. Honest agents send their own convex differentiable cost; faulty agents send arbitrary convex
  differentiable functions. f-resilience is relative to an explicit class `K` of executions (honest
  set + honest costs). `AllExecs` contains all executions with `≤ f` faults whose honest aggregate
  has a minimum point; `RedExecs` is its 2f-redundant part. `Protocol.resilient_toAlg` transfers
  the impossibility to every deterministic interactive protocol in which a Byzantine agent can mimic
  an honest one.
* *Theorem 2 model.* The system is synchronous and server-based. In each iteration honest agents send
  `∇Q_i(w^t)`, and faulty agents send arbitrary vectors (adaptive adversary; a missing gradient is one
  such choice). The CGC filter scales the `f` largest vectors down to the `(n−f)`-th smallest norm
  (defined as an order statistic, independent of tie-breaking), and `w^{t+1} = w^t − η Σ ĝ_j`. The
  paper's termination rule is the case "threshold = 0", in which the update is the identity.
* *Space.* Costs live on a real inner product space, which includes `ℝ^d`. The space is complete for
  Theorem 2. Lemma 1 and the sufficiency results hold for arbitrary functions on any type.
* `[w]_{W*}` is any nearest-point map onto `W*` (unique), and it exists whenever `W* ≠ ∅`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (for any functions, `S` may be empty) | `lemma1` | `Basic.lean` |
| Definitions 1, 2 | `TwoFRedundant`, `Resilient` | `Basic.lean` |
| Theorem 1, Part I of the proof | `partI` | `Convex.lean` |
| Theorem 1, repaired (indistinguishability, both directions) | `theorem1_indistinguishable` | `Necessity.lean` |
| — needs exactly `f` faulty agents | `theorem1_indistinguishable_false_fewer_faults` | `Necessity.lean` |
| Theorem 1 (literal, assuming `2f < n`; vacuous) | `theorem1` | `Necessity.lean` |
| — no algorithm is f-resilient on all executions (`f ≥ 1`) | `no_resilient_allExecs` | `Necessity.lean` |
| — redundant executions are confused as well | `redundant_execution_confusable` | `Necessity.lean` |
| — sharp reading (not claimed by the paper) is false | `sharp_necessity_false`, `not_sharp_theorem1` | `Necessity.lean` |
| — fails without `n > 2f` | `theorem1_false_n_eq_one` | `Necessity.lean` |
| "Best case for the server" reduction | `Protocol.resilient_toAlg` | `Necessity.lean` |
| Sufficiency (existence of an exact algorithm on 2f-redundant inputs) | `exists_resilient_redundant` | `Basic.lean` |
| 2f-redundancy is not a maximal solvable class | `exists_resilient_redundant_insert` | `Basic.lean` |
| Theorem 2 (ii) and `ρ < 1` | `Assumptions.theorem2` | `CGC.lean` |
| Theorem 2 (i) `ρ ≥ 0` (needs `W* ≠ ℝ^d`) | `Assumptions.theorem2_rho_nonneg` | `CGC.lean` |
| Theorem 2 (i) false if `W* = ℝ^d` | `theorem2_rho_nonneg_false` | `Examples.lean` |
| Convergence `dist(w^t, W*) → 0` | `Assumptions.theorem2_tendsto` | `CGC.lean` |
| Stopping rule of Step S2 is correct | `Assumptions.mem_Wstar_of_threshold_eq_zero` | `CGC.lean` |
| Appendix B, `λ ≤ μ` | `Assumptions.lam_le_μ` | `CGC.lean` |
| Appendix C, (42) and (56) | `Assumptions.key_estimates`, `Assumptions.step` | `CGC.lean` |

**Not formalized.**
* The peer-to-peer reduction via Byzantine broadcast (an informal remark).
* Section 5 (partial asynchrony; the paper gives no proof).
* The applications in Section 1.2.
* The `O(n(d + log n))` complexity of the filter.

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity of Theorem 2: `example_assumptions` instantiates all hypotheses with one
Byzantine agent (`n = 4`, `f = 1`, costs `x²/2`, `α = 1/12`, `ρ = 15/16`). `exists_proj` shows that
the projection field can always be filled. The counterexamples are explicit instances on `ℝ` and
`ℝ × ℝ`. The model is self-contained (Mathlib, plus the shared quorum arithmetic
`Cslib/Foundations/Data/Finset/Quorum.lean`). CSLib's Byzantine message-passing models were
not needed, because the paper argues in a one-shot model. Unlike `PODC2013/ByzantineVectorConsensus`
(inputs are points, validity is a convex-hull condition), the inputs here are cost functions, so no code
is shared. CSLib candidates:
* `mem_argmin_iff_of_hasFDerivAt`;
* the order statistic `threshold` with `threshold_spec`.

The first-order condition (`ConvexOn.add_fderiv_le` / `ConvexOn.add_inner_le`) and finite sums of
convex functions (`ConvexOn.fun_sum`, used by `convexOn_agg`) are shared code in CSLib,
`Cslib/Foundations/Analysis/Convex/FirstOrder.lean`.
