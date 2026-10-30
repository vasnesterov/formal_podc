# Approximate Byzantine Fault-Tolerance in Distributed Optimization — PODC 2021

Shuo Liu, Nirupam Gupta, Nitin H. Vaidya. *Approximate Byzantine Fault-Tolerance in Distributed
Optimization.* PODC 2021. DOI [10.1145/3465084.3467902](https://doi.org/10.1145/3465084.3467902).
Formalized version: arXiv [2101.09337](https://arxiv.org/abs/2101.09337) v5 (full version);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf). Formalized: Section 3 (Lemma 1,
Theorems 1 and 2).

**Verdict: ⚠️ Minor statement issues.** Theorem 2 ("`(2f, ε)`-redundancy ⇒ `(f, 2ε)`-resilience")
holds as stated. Its algorithm misses a case, which is easy to repair. Theorem 1 ("`(f, ε)`-resilience
⇒ `(2f, ε)`-redundancy") does not say on which inputs the algorithm must work. Read for the given cost
functions, it is false. Read for all inputs, it is vacuous. Read for the class of
`(2f, ε')`-redundant inputs, it is true, and we prove it for all `n > 2f ≥ 2`. But the paper's proof
does not cover that reading. Lemma 1 is true, except in the degenerate case `f ≥ n`.

## Mistakes in the paper

* **Theorem 1 is under-specified.** Definition 2 is a property of an algorithm in the executions
  with given cost functions. The theorem talks about "the agents' cost functions". We formalize three
  readings.
  - *(a) Per profile (literal): false.* Take `n = 3`, `f = 1`, `d = 1` and costs `(x − a)²`, `(x + a)²`,
    `2a|x|` with `a > 0`. They are convex and every aggregate has a unique minimum point, as in the
    proof's own scenario. Every pair of agents has `arg min = {0}`, so the algorithm "always output
    0" is `(1, 0)`-resilient, i.e. exactly fault-tolerant. But `arg min Q₀ = {a}` is at distance `a`
    from `arg min (Q₀ + Q₁) = {0}`, so the costs are not `(2, ε)`-redundant for any `ε < a`. Since `a`
    is arbitrary, no constant factor helps either. For a fixed profile, an `(f, ε)`-resilient
    algorithm exists iff some point is within `ε` of every `(n − f)`-`arg min`. Redundancy plays no
    role there. (`theorem_1_false_per_profile`, `exists_isResilient_iff`)
  - *(b) All inputs: vacuous.* The proof turns the faulty agents' fabricated functions into the true
    costs of a second execution. So it needs the algorithm to be correct on all profiles. On that
    class no deterministic algorithm is `(f, ε)`-resilient once `1 ≤ f < n`, whatever the
    redundancy, even with quadratic costs `‖x − cᵢ‖²`. The theorem then holds only because its
    hypothesis is never met. (`theorem_1_uniform`, `no_uniform_resilience`)
  - *(c) Redundant inputs: true, proof repaired.* The meaningful version is: if `ε < ε'`, no
    deterministic algorithm is `(f, ε)`-resilient on all profiles satisfying Assumption 1 and
    `(2f, ε')`-redundancy. Equivalently, resilience `ε` on that class forces `ε' ≤ ε`. With Theorem 2,
    the best resilience on the class lies in `[ε', 2ε']`. The paper's proof does not establish this:
    its second profile (the reflected faulty functions) is not shown to be `(2f, ε')`-redundant. We
    prove it for all `n > 2f ≥ 2` and every `ℝ^d`, `d ≥ 1`, with one profile supported on the three
    points `−v, 0, v`, `‖v‖ = ε'`. The `f` agents of group 2 pull towards `v`, the `f` agents of group
    3 towards `−v`, and the rest prefer `0`. A set has `v` (resp. `−v`) as a minimum point only if it
    contains group 2 and not group 3 (resp. the converse). So nested sets always have their `arg min`s
    together in `{0, v}` or in `{0, −v}`, and the redundancy is `ε'`. The `n − f` agents outside group
    3 have `arg min {v}`, those outside group 2 have `{−v}`, at distance `2ε' > 2ε`. These costs are
    discontinuous, which Section 3 allows. (`theorem_1_corrected`, `theorem_1_class`,
    `resilience_window`)
* **The Theorem 2 algorithm misses a case.** Step 2 picks `x_T ∈ arg min ∑_{i∈T} Qᵢ` for *every*
  set `T` of `n − f` received functions. It also takes distances to `arg min ∑_{i∈T̂} Qᵢ`. If `T`
  contains faulty agents, these sets may be empty, and then Step 2
  is undefined. For example, a faulty agent can send minus the other agents' aggregate plus a
  non-zero linear function, so that the aggregate is linear and has no minimum. Repair: pick an
  arbitrary point, and let the distance to `∅` be `+∞`. The proof then goes through unchanged, since it uses `x_T ∈ arg min` only for a fully non-faulty `T`. This is a
  proof-level gap; the statement is true. (`algorithm`, `theorem_2`)
* **Lemma 1 fails for `f ≥ n`.** For `f = n` the only set of `n − f` non-faulty agents is `∅`, whose
  `arg min` is all of `ℝ^d`. So every algorithm is `(n, 0)`-resilient. For `f > n` the condition is
  empty. False only in a degenerate case. For `n/2 ≤ f < n` the lemma holds in the reading of its
  proof (no algorithm works for all profiles). Read per profile, it is false (e.g. all costs equal),
  just like Theorem 1. In the uniform reading, `f ≥ 1` already suffices. (`lemma_1`,
  `lemma_1_false_of_le`, `no_uniform_resilience`)
* **Smaller points.**
  - Theorem 2 needs neither the closedness in Assumption 1 nor redundancy outside the current
    non-faulty set. An `inf`/triangle-inequality argument replaces the nearest points `z` and `x*`.
    Only `arg min ≠ ∅` and the redundancy inequality for sets of non-faulty agents are used
    (`theorem_2_strong`). It also holds for `f = 0`, which the proof excludes.
  - Theorem 1's proof writes `n − 2f ≤ |Ŝ| < n − f`, while Definition 3 has `|Ŝ| = n − 2f`. This is
    harmless.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* This is the paper's "best case for the server" (Section 3). There are `n` agents, each with a cost
  `Qᵢ : E → ℝ`. The server receives one function per agent and applies a deterministic map
  `alg : (Fin n → E → ℝ) → E`. Non-faulty agents send their true cost. A set `B` of at most `f`
  Byzantine agents may send arbitrary functions. There is no synchrony or randomness issue in this
  one-shot model.
* `IsResilient f ε alg Q` (Definition 2) quantifies over all faulty sets `|B| ≤ f`, all behaviours
  of `B`, and all sets `S` of `n − f` non-faulty agents. Resilience on a class of inputs is
  `∀ Q ∈ class, IsResilient …`.
* The impossibility results only use executions in which the faulty agents send their true costs.
  So they also hold if faulty agents are restricted to "admissible" functions.
* Distances are `Metric.infEDist` and `Metric.hausdorffEDist`, valued in `ℝ≥0∞`. On non-empty sets
  they are the paper's `dist`. The distance to `∅` is `∞`. Definition 3's cardinalities are stated
  additively (`|S| + f = n`, `|Ŝ| + 2f = n`).
* Spaces: Theorem 2 is proved in any (pseudo-e)metric space. Lemma 1 is proved in real inner product
  spaces. Theorem 1 (c) is proved in real normed spaces `≠ 0`. All of these include `ℝ^d`, `d ≥ 1`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 2, 3, Assumption 1 | `IsResilient`, `IsRedundant`, `Assumption1` | `Basic.lean` |
| Lemma 1 (`n/2 ≤ f < n`) | `lemma_1` | `Quadratic.lean` |
| — false for `f ≥ n` | `lemma_1_false_of_le` | `Quadratic.lean` |
| — holds for every `1 ≤ f < n` (uniform reading) | `no_uniform_resilience` | `Quadratic.lean` |
| Theorem 1, per-profile reading: false | `theorem_1_false_per_profile` | `PerProfile.lean` |
| — per-profile characterization | `exists_isResilient_iff` | `Basic.lean` |
| Theorem 1, uniform reading (vacuous) | `theorem_1_uniform` | `Quadratic.lean` |
| Theorem 1, class reading (corrected) | `theorem_1_corrected`, `theorem_1_class` | `Tightness.lean` |
| Theorem 2 | `theorem_2` | `Sufficiency.lean` |
| — honest-only hypotheses, no closedness | `theorem_2_strong` | `Sufficiency.lean` |
| Theorems 1 + 2: window `[ε', 2ε']` | `resilience_window` | `Main.lean` |

**Not formalized.** Appendix B ((f, 0)-resilience ⇔ exact fault tolerance). The remark "2f-redundancy
⇔ (2f, 0)-redundancy". Sections 4–5 (DGD with CGE/CWTM gradient filters, Theorems 3–6) and the
experiments. The peer-to-peer simulation remark.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `resilience_window` shows that the class of Theorem 2's hypotheses is
non-empty for every `ε'`. The counterexample profiles satisfy Assumption 1 (with unique minima in
`PerProfile.lean` and `Quadratic.lean`). The model is self-contained (Mathlib only). It follows the
style of the companion formalization `Papers/PODC2020/RedundantOptimization` (Gupta–Vaidya, exact
case), which found the same under-specification of the necessity theorem. No CSLib candidates.
