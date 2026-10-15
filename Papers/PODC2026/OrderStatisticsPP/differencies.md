# Differences between the formalization and the paper

Paper: D'Archivio, AlMahmoud, Natale, Mallmann-Trenn, *Order Statistics in Population Protocols via
Simple Dynamics*, PODC 2026 (proceedings numbering; full version HAL hal-05548829 numbers Section 4
as Section 3).

## A. Modelling choices (faithful, but made explicit)

1. **Opinions** range over a finite linear order `α` instead of `ℝ`. All dynamics only compare and
   copy opinions, so a real initial configuration evolves inside its finite value set; the
   matrix formulation needs a finite state space.
2. **Fixation probability** is formalized as `lim_{t→∞} P[X_t = (x, …, x)]` (finite Markov chain
   `T`, `(T^t) c s`); since consensus configurations are absorbing this equals the probability of
   eventually being in consensus on `x` forever. No trajectory measure is built. Existence of the
   limit is proved, not assumed.
3. **Ties.** The paper proves its laws for distinct initial opinions and says the general case
   "trivially follows by summing". We prove the general statement (sum of `π_k` over the ranks of
   `x`, `#{u | c u < x} < k ≤ #{u | c u ≤ x}`) and derive the distinct-opinion statements.
4. **Weighted model (Sec. 4.2)**: weights `w ≥ 0` with `W = ∑ w > 0` (needed for the
   activation probabilities `w/W` to make sense), self-loops allowed, `p ∈ (0, 1)`. "Connected" is
   connectivity of the undirected support graph `{u, v}` with `w u v > 0` or `w v u > 0`
   (`supportGraph`); for circulations this coincides with strong connectivity.
5. **Clique sampling**: "sample `u, v` u.a.r." = independent uniform `u, v`, `v = u` allowed (as in
   Lemma 4.1's `1/n²`).
6. **Biased-Median sampling (ambiguity).** Sec. 4.5 says `u` "samples uniformly at random an
   unordered pair of agents `(v, s)` (`v` and `s` may be equal)". Lemma 4.8's counts
   `2(n-j)+1`, `2j-1` (out of `n²`) require two *independent* uniform samples (ordered pairs); we
   formalize that reading. Under the literal reading (uniform among the `n(n+1)/2` multisets) the
   law is different: for `n = 3`, `p = 1/2` (Median) the fixation law is `(2/7, 3/7, 2/7)` instead
   of `(1/4, 1/2, 1/4)` (exact computation, script not kept in the repo; not formalized).
7. Self-Excluding Median and 3-Majority: three independent uniform samples (Lemma 4.9's count
   out of `n³`), possibly including the activated agent. 2-Choices (Cor. 3): `u` samples two
   independent uniform agents (possibly itself) and adopts their opinion if they agree. Binary
   opinions are `Bool` with `false < true` (`0`/`1`).
8. **Theorem 2 range**: requires `p ∈ (0, 1/2]` (so `p/(1-p) ≤ 1` is a probability). The abstract's
   "binomial protocol … `K - 1 ~ Bin(n-1, 1-p)`" therefore only covers `1 - p ≥ 1/2`; stated with
   this hypothesis.
9. **Converse of Proposition 6.** The hypothesis is read as "the geometric law holds from every
   configuration with pairwise distinct opinions"; values range over a linear order with at least
   `n` elements (otherwise there are no such configurations).

## B. Errors / gaps in the paper

10. **Proposition 6 (⇐), proof gap.** After "relabel at every round the nodes so that node `i`
    holds `X^t_(i)`", the matrices `P^(t)` depend on the (random) configuration at time `t`.
    Equation (6), `P[X^t_(i) = X^0_(j)] = (∏_s P^(s))_{j,i}`, has a random right-hand side and is
    not justified by "similarly to Lemmas 4.3 and 4.4" (the expectation of a product of dependent
    random matrices is not the product of expectations); Lemma 4.7 is about a deterministic
    sequence. **The statement is true**: we prove it with the harmonic function
    `c ↦ ∑_{k ≤ #{u : c u ≤ y}} π_k` (a bounded martingale), whose harmonicity only needs that
    `π` is stationary for every possible `P^(t)`, i.e. equal in/out flows across every cut
    (Lemma 4.6) — `copyOrMaxW_fixation`.
11. **Proposition 6 (⇒), invalid proof.** The proof claims that geometric fixation probabilities
    imply "there exists `N` such that for all `t ≥ N`, `P[X^t_(i) = X^0_(j)] = π_j`" — a limit
    need not be attained at a finite time (already for the clique with `n = 2`,
    `P[X^t_(1) = x_(1)] = π_1 + (1-π_1) r^t ≠ π_1` for every `t`), and again treats `P^(N)` as
    deterministic. **The statement is true**: `copyOrMaxW_geomFix_iff`. New proof: (i) threshold
    projection `y ≤ ·` turns Copy-or-Max into binary Copy-or-Max (lumping), so the binary fixation
    probabilities are determined by the hypothesis; (ii) the binary fixation probability is
    harmonic, and harmonicity at the configuration with a single `0` at agent `v` forces
    in-flow(v) = out-flow(v); (iii) if the support graph were disconnected, a configuration with
    distinct opinions could never reach consensus.
12. **(Minor) D vs D⁻¹ slip in the proof of Proposition 6, Item iv).** Lemma 4.7 itself is fine:
    its item iv) is an existential hypothesis ("there exists a non-singular `D` …"), satisfied by
    `D = diag(1/√π_k)`. Only the instantiation in the proof of Proposition 6 is wrong: with
    `D = diag(√π_k)`, `D⁻¹ P^(t)ᵀ D` is not symmetric (detailed balance `π_a K_ab = π_b K_ba` makes
    `D Pᵀ D⁻¹` symmetric instead). Trivially fixable. Lean check for `n = 2`, `p = 1/2`
    (`Counterexample.prop6_itemIv_sqrt_slip`, which also checks the corrected choice). Lemma 4.7
    is not formalized (our proofs do not need it).
13. **Definition 4.2 is under-specified (Theorem 7).** Definition 4.2 only constrains
    configurations with pairwise distinct values, but from the first opinion change on every configuration has ties, so the
    proof of Theorem 7 ("we can follow the proof of Lemmas 3.3 and 3.4") needs the rank structure
    on tied configurations too. The paper's own gloss ("`P[S_ij]` is a function of the ranks `i` and `j`
    only") shows the intended class, which is our fix below. Clarification — under the literal
    reading of Definition 4.2 Theorem 7 would fail:
    `Counterexample.tieMax` equals Copy-or-Max (`p = 1/2`) on every configuration with distinct
    opinions (`tieMax_eq_copyOrMax`; so it is Order-Based with Lemma 4.1's `q_j(i)` and satisfies
    Theorem 7's positivity hypotheses) and runs the Max dynamics on tied configurations; it
    converges to consensus a.s., but from `(0, 1, 2)` it fixes on `2` with probability `7/9`
    (`tieMax_fixation`) instead of `π_3 = 4/7` (`tieMax_not_geometric`).
    **Fix (intended reading)**: require the rank-event structure on all configurations, formalized in threshold form
    (`OrderBased`: for every lower set `D` holding `m` agents, `P[an agent outside D adopts a value
    in D] = f_{m+1}`, `P[an agent in D adopts a value outside D] = h_m`; this is implied by the
    rank-event condition with ties broken arbitrarily, and is all the proof needs). Then Theorem 7 holds (`orderBased_fixation`); no laziness /
    aperiodicity assumption is needed. Copy-or-Max, Biased-Median and Self-Excluding Median
    satisfy this definition with exactly the paper's `f_k, h_k` (`Instances.lean`).
14. **Theorem 1, convergence time "O(log n) parallel rounds w.h.p."** (proof only in the full
    version, Theorem 9): not formalized. The proof is a sketch with gaps: the holding times `W_s`
    (geometric, unbounded, state-dependent) are "upper-bounded by i.i.d. `Z_s`" with a bounded,
    state-independent distribution — no such pointwise or stochastic domination holds; the
    "spread time evenly over ranks" step is heuristic; the restart rule "if [the new top count] is
    larger, consensus is only faster" is asserted without a monotonicity argument. The bound also
    implicitly needs `p` to be a constant (for `p → 1` the dynamics approaches the voter model,
    which needs `Θ(n)` parallel rounds). The statement is plausible but unverified here.
15. Fact 4.1 (examples of Order-Based dynamics) is stated without proof and not formalized; note that
    as written ("adopts `Y_j` with probability depending only on `j`") it covers neither Copy-or-Max
    nor Biased-Median (their adoption probabilities depend on the position of the agent's own
    value). Full-version Fact 3.2 (median on the cycle) is informal; Corollary 10 (Top-k) is an
    application with its own concentration analysis — both not formalized.

## C. Minor issues

16. Lemma 4.2, footnote 3: the boundary convention should be `X_(k) = 0` for `k = 0` or
    `k = n + 1` (not `k = n`); irrelevant since `f_1 = h_n = 0`. Our Lemma 4.2 (`orderStat_step`)
    is the stronger distributional form and holds for all configurations (ties included), as the
    paper claims.
17. Lemma 4.4 is proved in the paper for distinct initial values only; `orderStat_ancestry` gives
    the version with ties (`P[X^t_(i) = x] = ∑_j (Pᵗ)_{j,i} 1[X^0_(j) = x]`), for every Order-Based
    dynamics. The order statistic is formalized by the predicate `IsOrderStat` (unique, by
    `isOrderStat_existsUnique`); Lemma 4.3 is formalized for an arbitrary real valuation of the
    opinions (`orderStat_expectation`).
18. Lemma 4.5: we formalize detailed balance (`lemma45_detailed_balance`) and the diagonal bound
    `g_k ≥ (n²+1)/(2n²)` (`lemma45_diag_bound`, valid for every `p ≤ 1`); irreducibility,
    aperiodicity and uniqueness (Perron–Frobenius) are not needed by our proof and not formalized.
19. Full version only: Lemma 3.9 and the proof of Theorem 8 divide by `n³`; the correct
    normalisation is `n⁴` (as in the proceedings). Ratios, hence the law, are unaffected.
20. Theorem 8's law is formalized literally with `Real.Gamma` (`sxLaw`); its normalisation
    (`sum_sxLaw`) is proved via the rising-factorial Chu–Vandermonde identity; Corollary 4's
    Beta-Binomial pmf is `betaBinomial N a b x = C(N,x) B(x+a, N-x+b)/B(a,b)` with
    `B(a,b) = Γ(a)Γ(b)/Γ(a+b)`.
21. Proof route: instead of the paper's rank-ancestry + Perron–Frobenius argument (Lemmas
    4.3–4.5, 4.7) the fixation laws are proved with harmonic functions of threshold counts and a
    finite-chain absorption lemma; the rank-ancestry lemmas are verified separately
    (`RankAncestry.lean`). The paper's final step "as there exists a sequence of events with
    non-zero probability leading to consensus, the probability … is `π_k`" is made rigorous by
    `Cslib.Probability.Markov.tendsto_sum_compl_of_absorbing`.
