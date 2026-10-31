# Differences between the formalization and the paper

Paper: V. Dani, A. Gupta, T. P. Hayes, S. Pettie, *Wake Up and Join Me! An Energy-Efficient
Algorithm for Maximal Matching in Radio Networks*, PODC 2021 (brief announcement); full version
arXiv:2104.09096v2 (numbering follows it).

## Errors in the paper

1. **Theorem 6.5, "maximum load at most `k`", is false; the true bound is `k + 1`.**
   Algorithm 4 makes `k + 1` calls of the maximal matching subroutine (line 1 and `k` loop
   iterations). In each call a vertex gets at most one new partner, so at most one new vertex
   points to it: the load is at most `k + 1` (`theorem_6_5_load`). This is attained: on `c`
   disjoint copies of `P₃` with `k = 1`, the first call matches each centre with one leaf, and the
   second (cross-graph) call necessarily matches the other leaf with the centre, which is
   re-assigned to it; the first leaf still points to the centre, so the load is `2 > k`
   (`theorem_6_5_load_false`; `exists_run` shows such executions exist). This happens in every
   execution in which both calls return maximal matchings, an event of probability
   `1 − O(1/n²)` by the paper's own Theorem 1.1 (`n = 3c`); so the claimed event has probability
   `O(1/n²)`, not `1 − O(k/n²)`. Rule: R3 does not excuse it (the fix changes the constant `k`,
   which is itself the claim, and the paper's proof never discusses the load); Theorem 6.5 is a
   secondary result ("We also consider …", R5), so ❌. Borderline call (reviewer): one could read `k` vs `k + 1` as an off-by-one with evident
   intent, but the paper nowhere states or argues `k + 1` (its proof is silent on the load), and an
   off-by-one in a stated bound is a changed constant under R3 (same call as the off-by-one bound of
   Theorem 2.6 in PODC 2018 SparseColoringLB). The counterexample is within the paper's own model:
   line 4 makes the subroutine a maximal matching of the assigned–unassigned cross graph, so on `P₃`
   the second call must match the remaining leaf with the centre; the load `|f⁻¹(v)|` is Definition
   6.4's. Also for `k = 0` the claim fails on any graph with an edge (load `1`). The abstract's claim (load within a
   polylog factor of optimal) survives with `k + 1`.

2. **Proof of Theorem 6.5: false intermediate claim (statement unaffected).** The proof says that
   after `k` iterations "at most `(1 − 1/(2L+2))^k (1−ε) n` nodes from `S ∪ R` will remain
   unassigned". The maximal matchings of the cross graph may keep picking unassigned vertices
   outside `S ∪ R`, so vertices of `S ∪ R` can stay unassigned: on the star `K_{1,9}` with the
   partial NAF `1 ↦ 0, 2 ↦ 0, 0 ↦ 1` (`L = 2`, `|S ∪ R| = 3`), a successful run of 7 iterations
   leaves `2 ∈ S` unassigned although `(5/6)^7 · 3 < 1` (`proof_6_5_step_false`). Repair: count
   *all* assigned vertices. Each call assigns at least `|S \ A| / (2L+2)` new vertices (pigeonhole
   over the `L + 1` cover matchings + "maximal ≥ half of any matching" in the cross graph), so
   `|S| − |A_j| ≤ |S| (1 − 1/(2L+2))^(j+1)`, which gives the stated coverage
   (`theorem_6_5_coverage`, `theorem_6_5_coverage_exp`, `theorem_6_5_full_coverage`). R1: claim
   inside a proof → 🛠️.

3. **Proof of Theorem 6.3: the normalisation procedure is not well-founded as described.**
   "Repeated application of this rule [redirect `f(f(v))` to a load-zero `v`] to all leaves in turn
   eventually leads to a NAF whose components are directed cycles or stars with one bidirected
   edge." Applied to a leaf `x₂` of a star with bidirected edge `r ↔ x₁`, the rule sets
   `f(r) = x₂` and makes `x₁` a leaf; applying it "to all leaves in turn" cycles forever, and the
   final shape it describes contains leaves. Also "double stars" (a 2-cycle with leaves at both
   ends) are not stars. The theorem is true. Repair (`Theorem63.lean`): apply the move only at a
   vertex `v` whose image is not on a 2-cycle and whose load is `< L`; it strictly decreases
   `|{v : f(f(f v)) ≠ f v}|` (`card_bad_move_lt`). When no move applies and `L ≥ 2`, a counting
   argument shows `f ∘ f ∘ f = f` (`bad_eq_empty`): every component is a 2-cycle with leaves. Odd
   cycles thus disappear for `L ≥ 2` (they are turned into stars of load `≤ 2`) instead of being
   covered by two matchings as in the paper. The `L` matchings are then built by labelling the
   in-neighbours of each vertex injectively (`exists_cover_of_tidy`). R1: proof gap → 🛠️.

4. **Theorem 1.1 is literally false for `Δ = 1`.** The energy bound `2C (log n)(log Δ)` is `0`
   for `Δ = 1` (allowed: `Δ` is "any upper bound on the maximum degree"), but a node can only be
   matched in a round in which it sends or listens. On any graph with an edge the event of
   Theorem 1.1 is empty for every execution (`theorem_1_1_delta_one`), so its probability is
   `0 < 1 − 1/n²`. Rule R2 (degenerate parameter corner; with the usual convention
   `log Δ ≥ 1` it disappears) → ⚠️. The energy part of Theorem 1.1 is checked only in this
   corner; its maximality part is Lemma 5.4, which we prove.

## Minor imprecisions and typos

* Proof of Lemma 5.4: "Let `t` be the first bad round; that is, `t` is minimal such that
  `Δ(t) ≥ 1/(2r(t))`" — should be `Δ(t − 1)` (Definition 5.3). Our `exists_first_bad` uses
  `Δ(t−1)`.
* Proof of Lemma 5.6: the chain of inequalities passes from `d(v, t − 1)` to `d(v, t)` inside a
  conditional expectation given `M(t − 1)` (`d(v, t)` is not `M(t−1)`-measurable). The intended
  argument (case split on `d(v, t−1) ≥ 1/(3r(t))`, since `d(v,t) ≤ d(v,t−1)`) is what we
  formalize (`lemma_5_6`).
* Proof of Theorem 1.1: `3 ∑_{t=1}^T r(t) = r(T) + 3 ∑_{t=1}^{T−1} r(t)` should be `3 r(T) + …`
  (not formalized).
* `T = C Δ log n` is used as a number of rounds but need not be an integer. We take any natural
  `T ≥ 1` (and `T ≥ 1000 Δ ln n` in `lemma_5_4_whp`).

## Modelling choices and differences

* **Graphs / NAFs.** `V` is a finite type, `G : SimpleGraph V`. A NAF is `f : V → V` with
  `G.Adj v (f v)` (Definition 6.1); `load f = max_v |f⁻¹(v)|`; `minNAFLoad G` and
  `matchingCoverNumber G` are `sInf` of the sets of achievable values (Definitions 6.1, 6.2), with
  matchings = Mathlib `Subgraph.IsMatching`. Theorem 6.3 is stated for graphs without isolated
  vertices (`hG`): otherwise there is no NAF and no matching cover, and both minima are undefined
  in the paper (in Lean both are `0` by the `sInf ∅ = 0` convention). We also prove the
  junk-free threshold form `exists_naf_iff_exists_cover` (`k ≥ 2`).
* **Partial NAFs** (Definition 6.4) are `f : V → Option V`; coverage `|S|/|V|` is stated as a
  bound on `|S|` (`#(domain f)`).
* **Algorithm 4** is modelled with the maximal matching subroutine as a black box: an execution
  is a sequence of partner functions `m 0, …, m k` with `m 0` a maximal matching of `G` and
  `m (j+1)` a maximal matching of the cross graph (assigned–unassigned edges of `G`), the effect of
  "only unassigned nodes recruit, only assigned nodes accept" (as in the paper's proof). The
  probabilistic wrapper "with probability `1 − O(k/n²)`" (all calls succeed, by Theorem 1.1) is
  not formalized; all our statements hold for every execution in which all calls succeed. The
  energy claim `O(k log² n)` is not formalized.
* `log` in Theorem 6.5 is taken to be the natural logarithm (`Real.log`); with `log₂` the
  hypothesis `k ≥ (2L+2) log n` is stronger, so the statement is covered. `n` may be any upper
  bound on `|V|`.
* **Radio model** (`Radio.lean`): synchronous rounds of three timesteps, no collision detection, a
  listener receives iff exactly one neighbour sends; IDs are the vertices (the paper assumes unique
  IDs, generated w.h.p.). Messages per timestep are typed (ID, pair, pair) as in Algorithms 2–3.
  Algorithm 1's per-round coin `x ∈ [0, 1]` is replaced by a role in
  `{recruit, accept, sleep}` with probabilities `r/2, r/2, 1 − r`; matched nodes draw a role that
  the protocol ignores (they sleep), which does not change the law of the execution.
* **Lemma 5.1** is proved for every sequence of role choices (stronger than "with probability one").
* **Lemma 5.2 / 5.6** are proved for one round, conditioned on the state `M(t−1)` (fixed partner
  variables), with the product law over role vectors as an explicit finite sum (`prob`). In Lemma
  5.2, `Δ` is any common upper bound on `d(v, t−1)` and `d(w, t−1)` (the paper uses the maximum
  residual degree `Δ(t−1)`, which is such a bound). In Lemma 5.6, goodness of round `t` is a
  hypothesis (`Z ≡ 0` otherwise, as the paper notes).
* **Lemma 5.4** (`Lemma54.lean`). The probability space is explicit: executions are paths
  `ω : Fin T → V → Role` with the product weight of the per-round role laws (`Chain.lean`;
  `pathProb`). We prove `P(M(T) maximal) ≥ 1 − T |V| exp(−((T/(3Δ)) ln(3/2) − 1/2)/(6e))`
  (`lemma_5_4`) and, for `T ≥ 1000 Δ ln n`, `≥ 1 − 2T|V|/n⁶` (`lemma_5_4_whp`); the paper states
  `≥ P(A) ≥ 1 − o(1/n²)` with per-event bound `n^{−(4+ε)}`. We bound `P(M(T) maximal)` directly
  (the failure event is contained in the union of the events `E_{v,t}`), which is the part of
  Lemma 5.4 used later; `P(A)` has the same bound by the same argument (not stated separately).
  The paper's Riemann sum / integral `∫ r = (T/(3Δ)) ln(r(t)/r(t*))` is replaced by the exact
  telescoping inequality `r(t) ≥ (T/(3Δ)) ln(r(t)/r(t−1))` (`sum_rate_ge`), which gives the same
  bound `∑_{t'∈I} r(t') ≥ (T/(3Δ)) ln(3/2) − 1/2`. `ln(3/2) ≥ 1/3` is used in the `whp` form
  (exponent `6` instead of the paper's `4 + ε` per event after the union bound — the paper's
  exponent is better; ours suffices for `o(1/n²)`). `Δ` is a natural number `≥ 1` bounding all
  degrees; rates after round `T` are frozen at `r(T)` (they are never used).
* **Theorem 1.1** is not formalized beyond Lemma 5.4 (maximality) and the `Δ = 1` corner: the
  w.h.p. energy bound (Chernoff) and the running time are not formalized.
* **Not formalized:** Propositions 2.3–2.4 (cited/random-graph facts), the energy claim of
  Theorem 6.5, the `O(n³)` remark after Theorem 6.3.
* **Proposition 2.2** is proved in vertex form (`#N.covered ≤ 2 #M.covered`, a matching with `e`
  edges covers `2e` vertices).
