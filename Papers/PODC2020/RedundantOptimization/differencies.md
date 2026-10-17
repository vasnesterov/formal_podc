# Differences between the formalization and the paper

Paper: N. Gupta, N. H. Vaidya, *Fault-Tolerance in Distributed Optimization: The Case of Redundancy*,
PODC 2020, DOI 10.1145/3382734.3405748 (proceedings version; no arXiv version).

## Issues in the paper

1. **Theorem 1 is under-specified.** *Classification: under-specified statement.* Definition 2
   (f-resilience) does not say which inputs (honest sets and honest cost functions) the algorithm
   must handle. We formalize three readings.
   - *(a) Literal (all executions): true but vacuous.* In Part II the faulty agents' functions
     `C_j` become honest cost functions of another execution (`T₂ = Ŝ ∪ B`). So the proof asks for
     correctness on all executions with `≤ f` faulty agents and arbitrary convex differentiable
     honest costs. We call this class `AllExecs`; it adds the implicit requirement of a minimum point
     (item 4). Under this reading the statement holds (`theorem1`). But for `f ≥ 1` and `d ≥ 1` no
     algorithm is f-resilient on this class (`no_resilient_allExecs`), so it holds vacuously. In this
     class even 2f-redundant executions are confused. With `n = 3`, `f = 1`, received
     `x², x², (x−2)²`, honest agents `{0,1}` (minimum 0) cannot be told apart from `{1,2}` (minimum
     1) (`redundant_execution_confusable`). That partner's costs have no common minimum point, unlike
     the partners built in the paper's proof.
   - *(b) Sharp: false, but not claimed by the paper.* "An algorithm that is f-resilient on all
     2f-redundant executions cannot be f-resilient on a non-redundant one" is false
     (`sharp_necessity_false`, `not_sharp_theorem1`). Counterexample: `n = 3`, `f = 1`, state space
     `ℝ²`, honest costs `x²` and `y²`. In general, any execution whose honest costs share a minimum
     point can be added (`exists_resilient_redundant_insert`). So 2f-redundancy is sufficient
     (`exists_resilient_redundant`, Theorem 2) but not a maximal solvable class. The paper does not
     claim this reading.
   - *(c) Indistinguishability: true, tight, proved* (`theorem1_indistinguishable`). Assume `f ≥ 1`,
     `2f < n`, exactly `f` faulty agents (`|H| + f = n`), and honest costs with a common minimum
     point. Then `e` is not 2f-redundant iff there are a received vector `C` consistent with `e` and
     an execution `e'` such that:
     - `e'` has `≤ f` faulty agents and is consistent with `C`;
     - the honest costs of `e'` share a minimum point;
     - the solution set of `e'` is disjoint from that of `e`.

     (⇒) is the paper's construction: `ŵ ∈ ⋂_{Ŝ} arg min Q_i \ W*` via Lemma 1, and
     `C_B = ‖x − ŵ‖²`. (⇐): `S = H ∩ H'` has `|S| ≥ n − 2f`, and a common minimum point of `e'`
     minimizes `Σ_S Q_i`, hence lies in `W*` by 2f-redundancy. This reading is our repaired
     Theorem 1.
2. **Part II of the proof assumes `|H| = n - f`.** *False statement under reading (c); the repair is
   "exactly `f` faulty agents".* "Then `|H| = |{1,…,n} \ B| = n − f`" silently fixes the number of
   faulty agents to `f`. Counterexample: `n = 3`, `f = 1`, no faulty agent, `H = {0,1,2}` with
   `x², y², x² + y²` on `ℝ²`. The honest costs share the minimum point `0` and violate 2f-redundancy.
   Yet every execution producing the same received vector has `0` as a solution
   (`theorem1_indistinguishable_false_fewer_faults`, via `not_disjoint_of_univ`).
3. **Theorem 1 needs `n > 2f`, which it does not state.** *False only in a degenerate case.* Part II
   uses `n > 2f` ("Recall that … `n > 2f`"). Without it the statement fails for `n = f = 1`. Then
   "output a minimum point of the only received function" is f-resilient on all executions, but the
   execution whose only (honest) agent has cost `x²` is not 2f-redundant: its empty subset has
   `|∅| ≥ n - 2f`, and `arg min 0 = ℝ ≠ {0}` (`theorem1_false_n_eq_one`). `theorem1` assumes
   `2f < n`.
4. **Existence of minimum points is implicit.** *Under-specified definitions.* Definition 2 can only
   be met if `arg min ∑_{i∈H} Q_i ≠ ∅`. Otherwise no algorithm is resilient even with `f = 0`
   (e.g. a linear cost). Assumption 4 uses the projection onto `W*`, which needs `W* ≠ ∅`. The paper
   only says "closed and convex". We require a minimum point in `AllExecs` / `RedExecs`, and
   Theorem 2's `Assumptions` contain a projection map with values in `W*`.
5. **Theorem 2 (i) (`ρ ∈ [0,1)`) is false when `W* = ℝ^d`.** *False only in a degenerate case.*
   Appendix B derives `λ ≤ μ` from (31) and (32), which needs a point `w ∉ W*`. If all honest costs
   are constant, Assumptions 2–4 hold for every `λ > 0`. With `n = 3`, `f = 1`, `μ = 1`, `λ = 30`,
   `η = 29/3 ∈ (0, η̄ = 58/3)` we get `ρ = 1 − 9α² = −840 < 0` (`theorem2_rho_nonneg_false`). Part (ii)
   is trivially true there. With a point off `W*`, (i) holds (`theorem2_rho_nonneg`).
6. **(30) needs `f ≥ 1`.** *Proof gap, statement true.* "From (29) it is easy to obtain
   `∇Q_i(w*) = 0` for all `i ∈ H`" uses a subset of `H` of size `|H| − 1 ≥ n − 2f`. For `f = 0` this is
   false (e.g. `(x−1)²` and `(x+1)²`), and so is (41). Theorem 2 still holds for `f = 0` (plain
   gradient descent): `key_estimates` treats `f = 0` separately, using the Lipschitz bound of the
   aggregate gradient.
7. **Minor.**
   - Appendix B: "if 2f-redundancy property holds true then `n > 2f`" does not follow from
     Definition 1. We assume `2f < n` explicitly in Theorem 2.
   - Theorem 2 assumes `α > 0` and `η ∈ (0, η̄)`. The former follows from the latter, since
     `η̄ = 6α/(nμ)`, so `theorem2` omits it. Part (ii) only needs `η ≥ 0` in each step (`step`).
   - Lemma 1 assumes `S ≠ ∅`; this is not needed, and no convexity or differentiability is needed
     either (`lemma1` holds for arbitrary real functions on any type).

## Modelling choices

- **Theorem 1 model.** This is the paper's "best case for the server" (Section 3.1). The server
  receives one cost function per agent and applies a deterministic map `alg`. Honest agents send
  their own function; faulty agents send arbitrary *admissible* (convex differentiable) functions,
  as in the paper. `Protocol.resilient_toAlg` shows that any deterministic protocol in which a
  Byzantine agent can behave like an honest agent with any cost function induces such a map. So
  the impossibility (`no_resilient_allExecs`) applies to all such protocols, including iterative
  server-based ones. f-resilience is defined relative to an explicit class `K` of executions
  (`Resilient Adm K alg`). `AllExecs` is the class of all executions with `≤ f` faulty agents and a
  minimum point. `RedExecs` is its 2f-redundant part.
- **Space.** The paper uses `ℝ^d`. Lemma 1, sufficiency and the "not maximal" results hold for any
  type and any real functions. Part I (`partI`) holds on any real normed space. The impossibility
  and Theorem 2 are stated on real inner product spaces (complete for Theorem 2, so that
  `HasGradientAt` is available), which include `EuclideanSpace ℝ (Fin d)`. The concrete
  counterexamples live on `ℝ` and `ℝ × ℝ`.
- **`n − 2f`** is truncated subtraction. This agrees with the paper's `|S| ≥ n − 2f` as cardinalities
  are `≥ 0`.
- **Gradients** are data `G i : E → E` with `HasGradientAt (Q i) (G i w) w` (Assumption 2).
  Assumption 3 is `‖G i w − G i w'‖ ≤ μ‖w − w'‖` for honest `i`. Assumption 4 is stated with the
  average honest gradient, as in the paper.
- **Projection.** `[w]_{W*}` is any nearest-point map onto `W*` (a field of `Assumptions`). It is
  unique in an inner product space. `exists_proj` shows it exists whenever `W* ≠ ∅` (`W*` is closed
  and convex).
- **CGC filter.** The threshold `‖g_{i_{n−f}}‖` is defined as an order statistic (`threshold`), and
  the filter as `min 1 (threshold / ‖g_j‖) • g_j`. This coincides with (16) for every tie-breaking in
  the sort: vectors not among the `f` largest have norm `≤` threshold, so their factor is 1.
- **Termination.** "If `‖g_{i_{n−f}}‖ = 0`, terminate and output `w^t`" is modelled by the same update.
  When the threshold is `0`, all filtered vectors are `0`, so `w^{t+1} = w^t`. Correctness of the
  stopping rule is `mem_Wstar_of_threshold_eq_zero`.
- **Adversary.** In each iteration the faulty agents' vectors are arbitrary (`IsRun` quantifies over
  any per-round choice). This includes adaptive adversaries and the "missing gradient = 0" rule.
- **Part I** (`partI`) is proved, like the paper, only from sets of exactly `n − f` agents (the
  paper's `S₁`, `S₂` swap argument), with `1 ≤ f < n`.

## Not formalized

- The peer-to-peer architecture, which the paper reduces to the server model via Byzantine broadcast
  when `f < n/3`. This is an informal remark in the paper.
- Section 5 (partial asynchrony with diminishing step sizes): the paper gives no proof here and
  refers to a technical report.
- Section 1.2 (sensing, learning, SGD variants) and the complexity `O(n(d + log n))` of the CGC
  filter.
- Part III of the proof of Theorem 1 as written. Part II is formalized as the repaired
  `theorem1_indistinguishable` (item 1(c)), and Part I as `partI`. The literal statement follows
  directly from `no_resilient_allExecs`.
