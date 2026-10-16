# Differences between the formalization and the paper

Paper: S. Brandt, Y. Maus, J. Uitto, *A Sharp Threshold Phenomenon for the Distributed Complexity of
the Lovász Local Lemma*, PODC 2019, DOI 10.1145/3293611.3331636. Formalized version: arXiv
1908.06270v2; numbering follows it.

The main results hold: Theorems 1.1 and 1.3, Lemmas 3.2, 3.7, 3.9, Lemma 3.5 with the intended
parentheses, and Lemma 3.6. One reduction in the proof of Theorem 1.3 is not valid as written,
and Lemma 3.5 is false as printed (a typo). Each item is classified as false statement / false only
in a degenerate case / proof gap with true statement / under-specified definition / typo / modelling
choice.

## Errors and gaps

1. **Section 3, "w.l.o.g. all variables have rank exactly 3" (proof gap; the statement is true).**
   The paper turns a rank-2 variable on `{u, v}` into a rank-3 one by adding a "virtual third bad
   event" whose probability does not change. The proof of Lemma 3.2 then needs the edges `{u, w}`
   and `{v, w}` of the dependency graph, with bookkeeping values on them.
   * If `w` is a new node, these edges raise the degrees of `u` and `v`. The final bound
     `p · ∏ φ ≤ p · 2^{deg}` then uses more than `d` factors `≤ 2`.
   * If `w` is an existing node, it need not be adjacent to `u` and `v`.
   * Rank-1 variables (one event) would need two virtual events. They are not mentioned.

   *Repair.* For a hyperedge `T` of size `≤ 2`, the representable set is a half-space: `s_t ≤ 1`
   for `|T| = 1`, and `s_u + s_v ≤ 2` for `|T| = 2`. Linearity of expectation gives the fixing step
   directly. This is the weighted Section-2 argument that §3.1 states informally. We prove one
   *fixing property* for all hyperedges of size `≤ 3` (`fixingProperty_of_card_le_three`), and
   Lemma 3.2 for every variable of rank `≤ 3` (`variable_fixing_lemma`), with no virtual events.

2. **Lemma 3.5 as printed (typo; the printed statement is false).** The statement reads
   `f(a,b) := 4 + 1/2 · ab − 2a − 2b − √(ab(4−a)(4−b))`, without the parentheses of Lemma 3.6.
   With this reading, `(0, 1, 3)` is representable (`a₁ = a₂ = 0`, `b₁ = c₂ = 2`, `b₃ = 1/2`,
   `c₃ = 3/2`), but `3 > f(0,1) = 2` (`lemma_3_5_as_printed_false`). With the parentheses of
   Lemma 3.6 the lemma is true (`srep_eq_f`). We also prove the symmetric form
   `S_rep = {(a,b,c) ≥ 0 | a + b + c + √(abc) ≤ 4}` (`representable_iff`). The paper does not state
   it. It follows from the identity `f(a,b) = ((√((4−a)(4−b)) − √(ab))/2)²` (`f_eq_zmax_sq`).

3. **Theorem 1.1, proof (proof gap in degenerate cases).**
   * "All other random variables do not change the probability of `E_v`" ignores variables that
     affect only `E_v` (rank 1). These can increase `Pr[E_v]` unless their value is chosen well.
     Such variables do not lie on an edge, so the merging step does not remove them. (They can be
     merged into an incident edge variable when `v` has a neighbour.)
   * The claim `Inc(u,y) + Inc(v,y) ≤ 2` divides by `Pr[E_u | θ]`, which may be `0`. Section 3.3
     fixes this with the convention `Inc = 0`.

   Both are handled: rank-1 hyperedges by the fixing property, and the convention of §3.3 in
   `Inc` (`exists_inc_add_inc_le_two` is the claim of the proof, for an unfixed variable and any
   two events).

4. **Lemma 3.9, proof (proof gap in a degenerate case).** The proof asserts
   `Σ pᵢ · Inc(x, yᵢ) = Pr[E_x]/Pr[E_x] = 1`. When `Pr[E_x | fixed] = 0`, the convention
   `Inc = 0` gives `0`, so `Σ pᵢ sᵢ` is only *dominated* by `(a, b, c)`. One then needs `S_rep` to be
   downward closed. This is true (`Representable.mono`) but not stated. Our version of the
   averaging step takes a dominated average (`exists_hval_le_four`, used in
   `fixingProperty_of_card_le_three`).

5. **Typos and imprecise remarks.**
   * Proof of Lemma 3.5, case `a = b = 0`: "`a₁ = a₂ = b₂ = b₃ = 0`" should read `b₁` for `b₂`.
   * Applications: "For the parameters to work out, the degree of the dependency graph must be at
     least 7" (3 orientations of a rank-3 hypergraph; no node may be a sink in two of them). We
     could not reproduce the 7. Take a `k`-regular linear 3-uniform hypergraph (dependency degree
     `d = 2k`). Then `Pr[E_v] = 3·9^{−k} − 2·27^{−k}`. The criterion fails for `k = 1`
     (`(7/27)·4 = 28/27`) but already holds for `k = 2`, `d = 4` (`(25/729)·16 = 400/729`). The
     relevant requirement is a lower bound on the minimum hyperdegree (`p` is the maximum over
     nodes) together with `d` bounded in terms of it. Not formalized; checked by exact arithmetic.
   * We checked the appendix's Hessian formulas for Lemma 3.6 numerically (finite differences).
     `∂²f/∂a²`, `∂²f/∂a∂b` and the determinant formula `(16 − ((2−a)(2−b) − √(ab(4−a)(4−b)))²)/(4ab(4−a)(4−b))`
     agree. We do not use them (item 8).

## Statements: modelling choices

6. **LLL instances** (modelling choice). There are finitely many independent variables `X_i` with
   finite ranges and arbitrary distributions (`Instance.prob`, nonnegative, summing to 1), and
   finitely many events `E_v`, each given as a predicate on full assignments that depends only on
   the variables `vbl v` (`bad_local`). The dependency graph joins two events that share a variable
   (`dep`, `depGraph`). `d` is any bound on `#dep v`, and `p` any bound on `Pr[E_v]`. This is the
   paper's variable setting. The paper writes `p < 2^{-d}`, i.e. `p · 2^d < 1`. We do not assume
   `p ≥ 0`; it follows from `Pr[E_v] ≥ 0` when there is an event.

7. **Conditional probabilities** (exact). `Pr[E_v | X_i = x_i, i fixed]` is `condProb σ v`, the
   probability under the product distribution in which fixed variables are point masses. Since
   the variables are independent, this equals the conditional probability given the fixed values.
   We use only the law of total probability (`sum_condProb_fix`), independence
   (`condProb_fix_of_not_mem`), locality (`condProb_congr`) and the value at full assignments
   (`condProb_total`). Variables are fixed only to values of positive probability, as in the paper
   ("positive probabilities `p₁, …, p_k`").

8. **Proof of Lemmas 3.6 and 3.7 replaced** (different proof, same statements). The paper proves
   Lemma 3.7 from Lemma 3.5 and the convexity of `f` (Lemma 3.6, via the Hessian and Sylvester's
   criterion), in a three-case argument. We prove the stronger *tangent-plane inequality*
   (`hval_le_of_tangent`). For `m > 0`, every `s ≥ 0` below the tangent plane of
   `h(a,b,c) = a + b + c + √(abc)` at `m` has `h(s) ≤ h(m)`. The proof is two weighted AM–GM
   inequalities (`two_sqrt_le`). This gives the averaging step directly (`exists_hval_le_four`),
   then Lemma 3.7 (`srep_incurved`). Lemma 3.6 follows from Lemma 3.7 and Lemma 3.5: a function
   whose strict epigraph is convex is convex (`f_convexOn`).

9. **Lemma 3.9** (generalised). Proved for an arbitrary incurved set `S ⊆ ℝ³` and any finite
   positive distribution, in contrapositive form ("an average in `S` has a point in `S`")
   (`lemma_3_9`). The paper's prefix-average argument is replaced by induction on the support.

10. **Lemma 3.2** (generalised). It is stated for any variable whose hyperedge `T` has the fixing
    property (`exists_step`), and proved for `|T| ≤ 3` (`variable_fixing_lemma`). The new values
    `ψ` differ from `φ` only on edges inside the hyperedge, exactly as in the paper's "moreover"
    clause (the frame condition of `Step`).

11. **The process** (modelling choice). The "sequential and local deterministic process" is a
    transition relation `Step p j s s'`. A step fixes an unfixed `X_j` to a value of positive
    probability, changes the bookkeeping only inside the hyperedge of `X_j`, and re-establishes
    `P*` at the events of `X_j`. `process_correct`, `theorem_1_1` and `theorem_1_3` say:
    * in every reachable state, **every** unfixed variable has a step, so an adaptive adversary may
      choose the order;
    * every reachable state with all variables fixed avoids all bad events;
    * a good assignment exists.

    A deterministic process is obtained by picking one step by a fixed choice function. Locality
    is formal: a step stays valid from any state that agrees on the variables of its events and on
    their bookkeeping rows (`Step.transport`).

12. **Theorem 1.1 uses the Section-3 bookkeeping** (stronger statement). The paper merges all
    variables of an edge into one and then multiplies `Pr[E_v]` by at most 2 per incident edge. We
    allow any number of variables per pair of events and keep the values `φ` of §3, with the linear
    fixing step for hyperedges of size `≤ 2`. The paper's own claim (`Inc(u,y) + Inc(v,y) ≤ 2` for
    some `y`) is `exists_inc_add_inc_le_two`.

13. **General rank** (extra). `process_correct` holds for any rank, given the fixing property of
    every hyperedge. Conjecture 1.5 thus reduces to this property for larger cliques, which is
    the paper's remark that "all other parts generalize". The property is not proved for size
    `≥ 4`. The follow-up paper of Brandt, Grunau and Rozhoň (PODC 2020) proves the conjecture.

## Corollaries 1.2 and 1.4

14. **Only the correctness of the parallel schedule is formalized** (scope). The corollaries
    combine three ingredients:
    * (a) a colouring computed by cited algorithms ([PR01] for an `O(d)` edge colouring in
      `O(d + log* n)` rounds, [FHK16] for an `O(d²)` 2-hop colouring in `Õ(d) + log* n` rounds);
    * (b) a LOCAL implementation of one phase in `O(1)` rounds;
    * (c) the fact that the parallel phases are a valid execution of the sequential process.

    We formalize (c). A parallel phase is a list of groups with pairwise disjoint regions. Each
    group runs a sequential run from the common start state, and the merged result is reached by
    the concatenated sequential run (`phase_run`). Every execution of a valid schedule succeeds,
    and an execution always exists (`valid_schedule_correct`). For the colour-class schedules:
    * Corollary 1.2 uses a colouring of the variables in which variables sharing an event differ,
      i.e. an edge colouring after merging (`corollary_1_2_core`);
    * Corollary 1.4 uses a 2-hop colouring of the dependency graph and an owner event for each
      variable (`corollary_1_4_core`).

    Both have exactly `K` phases. (a) and (b) are not formalized, so the round bounds are not
    formal theorems.

15. **Corollary 1.4, owners** (under-specified in the paper). "Every node of a color class fixes …
    all of its variables that are not fixed yet" assigns each variable to the first of its events in
    colour order. We allow any owner function with `owner j ∈ evs j`. The paper's rule (the event of
    smallest colour) is one such function. Variables that affect no event get an arbitrary owner.

## Lower bounds and sharpness

16. **Lower bounds** (cited, not formalized). The `Ω(log n)` deterministic and `Ω(log log n)`
    randomized lower bounds for `p ≥ 2^{-d}` come from [CKP16] and [BFH+16] via sinkless orientation.
    We formalize the reduction at instance level. Sinkless orientation on a `Δ`-regular graph is an
    LLL instance of rank 2 and dependency degree `Δ` with `Pr[E_v] · 2^Δ = 1`
    (`sinkless_at_threshold`). Its good assignments are exactly the sinkless orientations
    (`sinklessInstance_good_iff`). A port-numbering version of the round-elimination lower bound
    for sinkless orientation is in `Papers/PODC2019/AutomaticSpeedup` (`sinklessOrientation_lower_bound`).
    It is not connected to this development.

17. **Strictness of the criterion** (extra). With `p · 2^d = 1` a good assignment need not exist:
    one fair bit with the events `X = 0` and `X = 1` has `d = 1`, `p = 1/2` (`sharp_no_good_assignment`).
    For `d ≥ 4` this cannot happen, because `2^{-d} < 1/(e(d+1))` and the classical LLL applies.
    The threshold in the paper is about *distributed complexity*, not existence.
