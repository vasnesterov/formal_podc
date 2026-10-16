# Differences between the formalization and the paper

Paper: Dory, Ghaffari, Ilchi, *Near-Optimal Distributed Dominating Set in Bounded Arboricity Graphs*,
PODC 2022 (arXiv:2206.05174v1). Each item is classified as one of: **false statement**, **false only in a
degenerate case**, **proof gap (statement true)**, **under-specified definition**, **typo**, or
**modelling choice**.

## Errors and gaps in the paper

1. **Theorem 1.3 (factor `Δ^{1/k}(Δ^{1/k}+1)(k+1)` in `O(k²)` rounds): proof gap, statement true.** The proof
   uses Lemma 4.6 with `γ = Δ^{1/k}` and `λ = 1/(Δ+1)`, which gives the factor `γ(γ+1)⌈log_γ(Δ+1)⌉`. But
   `⌈log_γ(Δ+1)⌉ = ⌈k log_Δ(Δ+1)⌉ ≤ k+1` only when `(Δ+1)^k ≤ Δ^{k+1}`, and `γ > 1` needs `Δ ≥ 2`. For
   `Δ = k = 2`: `⌈log_{√2} 3⌉ = 4 > 3` (`logb_gap`), so the proof gives `≈ 13.7` instead of the claimed `≈ 10.2`.
   The statement is still true. In the uncovered regime `(Δ+1)^k > Δ^{k+1}` (which forces `k ≥ Δ`), the claimed
   factor is at least `Δ+1` (`claimed_factor_ge`). There the trivial one-round algorithm, where every node picks
   a minimum-weight node of `N⁺_v`, is a `(Δ+1)`-approximation (`trivial_approx`). Combined statement:
   `theorem_1_3_full`.

2. **Observation A.1: proof gap, statement true.** The observation claims that some single-round
   3-approximation exists on graphs of arboricity 1; this is true. But the algorithm of the proof (and of
   the introduction's sentence about trees), "take all non-leaf nodes", fails on a forest with a `K₂`
   component: both endpoints are leaves, so they are not dominated (`obsA1_proof_alg_fails_K2`). If "non-leaf"
   means "degree ≥ 2", isolated vertices are missed too. Fix: also take the larger-ID endpoint of every `K₂`
   component, and every isolated vertex. This is still one round, and the paper's parent/grandparent charging
   then gives the factor 3 (`observation_A_1_fixed`). The charging only needs an orientation with out-degree
   ≤ 1, so the result also holds for pseudoforests.

3. **Lemma 4.6 for `λ = 1`: under-specified hypothesis.** The lemma says "for `λ > 0`" and takes "the output of
   Lemma 4.1", which forces `λ < 1`, but `λ < 1` is never stated. Read literally with `λ = 1`, the number of
   phases `t = ⌈log_γ λ⁻¹⌉` is 0, so `S' = ∅` and `S ∪ S'` need not dominate. Example: a single vertex with
   `w = 1`, `x = 1`, `S = ∅` (`lemma_4_6_false_lam_one`). We assume `λ < 1` (`lemma_4_6_dominating`). Also, the
   lemma states `E[w_{S'}] = γ(γ+1)⌈log_γ λ⁻¹⌉·OPT`; this should be `≤` (**typo**).

4. **Lemma 4.7 (`E[c_v] ≤ γ+1`): missing justification, statement true.** The proof takes "the sequence
   `d_1 ≥ … ≥ d_r` that maximizes `E[c_v]`" and bounds `E[c_v]` by `∑ β_i e^{-β̄_i}` for a fixed sequence. The
   `d_i` are random and depend on earlier iterations, and the proof does not say why the fixed-sequence bound
   applies. Since the coins are fresh in every iteration, a standard argument closes the gap. We prove the
   lemma, combined with Lemma 4.8, by a potential-function / backward-induction argument. The potential is
   `Φ_i = γ ∑_{v undominated} x_v (p_i d_v + γ)`, and the step uses `(1-p)^d (1+pd) ≤ 1`.

5. **Theorem 1.1 / Lemma 4.1 for `α = 0`: false only in a degenerate case (of the proof).** Lemma 4.1 needs
   `λ < 1/((α+1)(1+ε))`. Theorem 1.1 uses `λ = 1/((2α+1)(1+ε))`, which violates this when `α = 0`, and bound (a)
   then has a zero denominator. Graphs of arboricity 0 are edgeless, so the theorem itself is trivial there. We
   assume `α ≥ 1`.

6. **Round complexity `O(log(Δ/α)/ε)`: imprecise.** The bound is `0` when `Δ ≤ α`, but at least one iteration
   (and `O(1)` rounds) is always needed. We prove `r ≤ 1 + 2 log(max 1 ((Δ+1)/(2α+1)))/ε` iterations and
   `2r + 2` rounds in total (`numIter_detLam_le`, `distributed_theorem_1_1`). For the general Lemma 4.1 we prove
   `r ≤ 1 + 2 log(max 1 (λ(Δ+1)))/ε` (`numIter_le`).

7. **Minor slip (notation):**
   - Section 3 reuses the symbol `λ` for `α/((2α+1)(1+ε))`, which differs from the `λ` of Section 4.

## Modelling choices and scope

8. **Arboricity vs. orientations (modelling choice).** As footnote 2 of the paper allows, the main theorems take
   an orientation with out-degree `≤ α` (`G.OutOrientation α`). The arboricity versions follow from
   Observation 3.5, which is proved (`ArboricityLE.hasOutDegLE`, `theorem_1_1_arboricity`, `theorem_3_1`). Our
   orientations may orient an edge both ways; this only makes the hypothesis stronger.

9. **Weights (modelling choice).** Weights are arbitrary nonnegative reals, not positive integers bounded by
   `n^c`. `OPT` is expressed as "for every dominating set `D`".

10. **Unweighted Section 3 (modelling choice).** The procedure of Section 3 equals that of Section 4.1 with
    `w ≡ 1`: `r+1` iterations in Section 3 correspond to `r' = r+1` in Section 4.1, and `τ ≡ 1`. Theorem 3.1 /
    Claim 3.3 are therefore obtained as `theorem_3_1` from the weighted theorem. Lemmas 3.2 and 3.4 are not
    stated separately: they are the unit-weight cases of `lemma_4_1` and of the feasibility invariant `Inv.feas`.

11. **Distributed model (modelling choice).** The deterministic algorithm is implemented in CSLib's synchronous
    locally-iterative model (`Cslib.LocallyIterative`). There, a node's new state is a function of the round
    number, its own state, and the *set* of its neighbours' states. States contain node identifiers, so this
    is the LOCAL model with IDs. Global knowledge: `Δ` (instantiated with the true maximum degree), `ε`, and the
    iteration count `r` (a function of `Δ, α, ε`), as the paper assumes. CONGEST message sizes are not
    formalized. Each message is the sender's state: an ID, a weight, `τ`, an ID, `x = τ(1+ε)^j/(Δ+1)` with
    `j < r` (invariant `Inv`), and three bits. The minimum-weight dominator `tauNode` is an arbitrary one, chosen
    with `Classical.epsilon`. Real-number arithmetic is exact.

12. **Randomized algorithm (modelling choice).** Lemma 4.6's algorithm is described centrally, round by round.
    Its randomness is modelled as independent per-node Bernoulli(`p_k`) coins in every step. The expectation is
    the finite backward recursion `expect`, which equals the expectation under the product measure. Γ is
    recomputed in every iteration as `{u ∉ S∪S' : X_u ≥ w_u/γ}`. The paper instead shrinks Γ by removing nodes
    whose `X_u` drops; the two agree because `X_u` only decreases (and sampled nodes have `X_u = 0`). A node
    whose sampling probability is `≥ 1` is sampled regardless of its coin. The packing values are multiplied by
    `γ` at the last iteration of each phase instead of at the start of the next phase, which is equivalent. No
    locally-iterative implementation of the randomized algorithm is given; the `O(1)` rounds per iteration are
    evident from the description.

13. **Theorem 1.2 (scope).** Combined statement: `theorem_1_2_full` (`Main.lean`). It is formalized in an explicit form for every `t ≥ 1` and `γ > 1`
    (`theorem_1_2`). With `ε = 1/(4t)` and `λ = ε/(α+1)`, the expected weight is at most
    `(α(1+1/t) + γ(γ+1)⌈log_γ(4t(α+1))⌉)·OPT`. The asymptotic part covers `γ = max(2, α^{1/(2t)})`, `α ≥ 2`
    and `t ln α ≤ α`, i.e. `t ≤ α/ln α`:
    - the extension cost is at most `416 α/t` (`theorem_1_2_arith`);
    - the number of iterations of Lemma 4.6 is at most `50 t (ln(Δ+1) + 1)` (`theorem_1_2_rounds_arith`);
    - the iterations of Lemma 4.1 are bounded by `numIter_le`.

    The constants are explicit but not optimized. Lemma 4.1 and Lemma 4.6 are combined at the level of
    the centralized description, not as a single distributed run.

14. **Theorem 1.4 (scope).** The KMW lower bound for fractional vertex cover (KMW16) is an external result and is
    not formalized. We formalize the combinatorial reduction:
    - the construction of `H` and its arboricity bound (we prove `≤ 2`, which is what the lower bound needs);
    - the degree bound `max K (max (Δ+1) 2)`;
    - `OPT_MDS(H) ≤ K·OPT_VC(G) + n`;
    - the conversion of any dominating set of `H` into a fractional vertex cover of `G` with `∑ y ≤ |S|/K`;
    - the locality of the simulation: the host map `H → G` does not increase distances.

    The simulation itself is formalized only as this distance property, not as a transformation of algorithms.
    The paper uses two properties of the KMW graph: it is bipartite (so `OPT_VC = OPT_FVC`) and it has `m ≥ n`.
    We use instead the general facts `OPT_VC ≤ 2·OPT_FVC` (rounding) and `n ≤ (Δ+1)·OPT_FVC`, the latter for
    graphs without isolated vertices. This gives the factor `2c(1+1/Δ)` instead of `c(1+1/Δ)` (`reduction`). The
    paper's footnote 3 mentions this alternative, and the change is immaterial for constant or polylogarithmic
    `c`.

15. **Not formalized:** Remarks 4.4 and 4.5 (unknown `Δ` or `α`, which use the Barenboim–Elkin orientation
    algorithm). The NP-hardness results cited from [BU17] are only quoted in the paper.
