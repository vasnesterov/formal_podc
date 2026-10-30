# Differences between the formalization and the paper

Paper: W. Feng, Y. Yin, *On Local Distributed Sampling and Counting*, PODC 2018 (arXiv:1802.06686v1).
Rules R1–R6 refer to the project's verdict scale.

## Errors in the paper (statement level)

1. **Corollary 5.2 is false as stated (❌, R1/R5: a corollary, not a headline).**
   *Claim.* A class of locally admissible, local Gibbs distributions has SSM with exponential decay
   at rate `α` in TV distance iff it has SSM with exponential decay at rate `α` in multiplicative
   error. Here `err(μ, μ̂) = max_x |ln μ(x) − ln μ̂(x)|`, eq. (2), with only `ln 0 − ln 0 = 0` as a
   convention, and exponential decay means `δ_n(t) = poly(n)·α^t` for all `t` (Definition 5.1).
   *Counterexample.* Take the hardcore model with fugacity 1 on the perfect matching with `m ≥ 1`
   edges (`matchingGraph m`, `n = 2m`). Every member is locally admissible
   (`hardcore_locallyAdmissible`) and has constraints of diameter `≤ 1` (`hardcore_gibbsLocal`).
   The class has TV-SSM with `δ_n(d) = 2·(1/2)^d` (`matching_ssm`). But pin a neighbour `u` of `v`
   to 1 (`σ`) and to 0 (`τ`). Then `D = {u}` is at distance 1, `μ^σ_v(1) = 0` and
   `μ^τ_v(1) > 0`, so `err = ∞`. Hence there is no multiplicative SSM with any real-valued rate
   (`hardcore_err_infinite`, `hardcore_not_mssm`, which hold for any graph with an edge; `corollary_5_2_false`).
   *Why not ⚠️.* The counterexample satisfies every hypothesis of the paper and is not degenerate:
   the class covers every even `n`, and the hardcore model is the paper's flagship application. The
   repair is not local. Restricting to distances `> ℓ` is not enough, because soft constraints with
   weights like `e^{e^n}` give finite but super-polynomial `err` at distance 1. The true statement
   must only constrain `err` where `poly(n)·α^d` is small, i.e. at distances `≳ log n`. That changes
   the definition of exponential decay the corollary is about.
   *Second problem (proof gap).* Even at large distances, the paper's proof (Theorem 5.1 ⇐, then the
   boosting Lemma 4.1 with locality `2t + ℓ`, then Theorem 5.1 ⇒ for `err`) yields
   `err ≤ poly(n)·(√α)^d`, not `poly(n)·α^d`. A direct pinning argument, with the pinned shell
   placed close to `D` and lower bounds on the marginals obtained from SSM, should recover rate
   `α` at large distances. This is not formalized, and we make no claim about it.
   *Distance 0.* Read literally, multiplicative SSM fails for *every* distribution with `|Σ| ≥ 2` already
   at `dist(v, D) = 0`: if `v ∈ D`, then `μ^σ_v`, `μ^τ_v` are point masses at different values and `err = ∞`.
   Our `MSSM` inherits this (at `d = 0` the pinnings may differ at `v`), so `¬ MSSM` on its own would be a
   weak statement. The counterexample does not use this case: `hardcore_err_infinite` has `v` free in both
   pinnings, which differ only at a neighbour `u`. So it also refutes the natural readings "`v ∉ Λ`" and
   "`dist(v, D) ≥ 1`".
   *Borderline (R6).* One could read Definition 5.1 for `err` as constraining only distances where
   `poly(n)·α^d` is small, which would make the hardcore counterexample disappear. We do not excuse it under
   R3/R4: the paper never states such a restriction, it says that the known multiplicative SSM results for
   independent sets have exactly this form, and the needed repair changes the notion of exponential decay
   itself (not a local fix). The corollary is listed by the paper under "Minor results", so ❌, not 🚨.
   *True part.* Multiplicative SSM ⇒ TV SSM with the same rate, since `d_TV ≤ err` for probability
   vectors (`tv_le_of_multClose`, `ssm_of_mssm`). This direction needs neither local admissibility
   nor locality.

2. **Algorithm local-JVV and the statement of Lemma 4.8: acceptance and rejection swapped
   (⚠️, R3).** §4.2.1: "`vᵢ` samples `F'_{vᵢ} = 1` with probability `q_{vᵢ}`" and "fails locally
   if `F'_{vᵢ} = 1`". Lemma 4.8: "fails with probability at most `∑ E[F'_{vᵢ}] = 1 − O(1/n)`". As
   written, with `q_{vᵢ} ≥ e^{−5/n²}`, the algorithm fails almost surely. The proof of Lemma 4.8
   uses `Pr[F'_{vᵢ} = 1 | Y = σ] = q_{vᵢ}(σ)` together with `Pr[success | Y = σ] = ∏ q_{vᵢ}(σ)`. The
   intent is therefore recoverable: accept with probability `q_{vᵢ}`, and fail with probability
   `≤ 1 − e^{−5/n} = O(1/n)`. The fix is local. We formalize the intended version.

3. **Theorem 5.1 (⇒): `δ_n(t) = 2 min{δ | t(n, δ) ≤ t − 1}` (⚠️, R3).** The minimum need not be
   attained (`δ` ranges over the open set `δ > 0`), and for `t ≤ t(n, δ)` for all `δ` the set is
   empty, so `δ_n(t)` is undefined although Definition 5.1 requires `δ_n : ℕ → ℝ≥0`. Intended
   reading: infimum, with `inf ∅ = ∞`. We use `[0, ∞]`-valued rates in `SSM` and prove the
   statement with the infimum (`theorem_5_1_forward`).

## Proof gaps and repairs

4. **Lemma 4.1, Claim.** `μ_{Λᵢ∪{v}}(τᵢᶜ) = μ_{Λᵢ₋₁∪{v}}(τᵢ₋₁ᶜ) · μ^{τᵢ₋₁ᶜ}_{vᵢ}(cᵢ) ≥ μ^{τᵢ₋₁ᶜ}_{vᵢ}(cᵢ)`
   is wrong (the first factor is `≤ 1`). Only positivity is needed. The first factor is positive by
   induction, and the second is `≥ 1/q − 3ε/(5nq) > 0` by (4) and (5). Our proof uses exactly this
   (`pinSeq_spec`). The quantitative bound (3) is correct as stated (`lemma_4_1_core`). The numeric
   step `e^{−ε/n} ≤ 1 − 2ε/(5n − ε)` and `1 + 2ε/(5n − ε) ≤ e^{ε/n}` is checked in `ratio_bound`.
5. **Lemma 4.1: `|p(c) − q(c)| ≤ d_TV(p, q)`** (used for (5)) requires both `p` and `q` to be
   probability vectors. We assume, as the paper's definition of approximate inference does, that
   the TV-approximate algorithm returns probability vectors on feasible instances (`hacc`).
6. **Lemma 4.1, the pinned case `v ∈ Λ`** ("otherwise the inference problem is trivial"): our
   `boostAlg` returns the point mass at `τ(v)`, which is exact (`marg_of_pinned`).
7. **Theorem 3.2, coupling.** "By a coupling argument, it can be verified that `d_TV(μ̂, μ^τ) ≤ δ`."
   We prove the ℓ¹ version by induction on the scan (`sum_abs_seqProb_sub_le`). The proof notes one
   subtlety: after an approximation error the sampler may reach infeasible pinnings, on which the
   inference algorithm has no guarantee. Our statement lets the oracle behave arbitrarily there,
   requiring only nonnegative answers of total mass `≤ 1`.
8. **Claim 4.6.** `Γ = {vⱼ | vⱼ ∉ B_t(v) or j ≤ i − 1}` should read `B_t(vᵢ)`. The pinnings
   `τ₁ = σᵢ₋₁(Γ)` and `τ₂ = Y(Γ)` must be read together with `τ` (feasibility "w.r.t. `μ^τ`"). We
   formalize the core step: equal oracle answers plus multiplicative error give positivity of the
   needed marginal (`claim_4_6_core`). The vertex bookkeeping is not formalized.
9. **Small slips.** In the Claim of Lemma 4.1, "`dist_G(v, v_{i−1}) > t`" and "at node `v_{i−1}`"
   should read `vᵢ`. In the proof of (3), "`m = |Λ| ≤ n`" should be `m = |Γ| ≤ n`. In the
   statement of Lemma 4.1 the round count is `2t + ℓ` with `t = t(n, ε/(5qn))`, which the paper
   writes as `O(t(n, ε/(5qn)))`.

## Modelling choices

10. **Per-instance LOCAL model.** We fix one instance `(G, x)` (graph, Gibbs factors) and model an
    inference algorithm as a map `Pin V S → V → (S → ℝ)`. `IsLocalAlg G r A` requires that the answer
    at `v` depends only on the pinning within distance `r`. True LOCAL locality also restricts the
    dependence on `(G, x)`, so assuming `IsLocalAlg` is weaker (Theorem 5.1 ⇒ and the hypothesis of
    Lemma 4.1 become stronger results). For the constructed algorithms (`ssmAlg`, `boostAlg`) we
    prove `IsLocalAlg`. Their outputs are given by the local formula `marg (gibbsWOn F B) (restrictPin
    τ' B) v`, which uses only the factors inside the ball `B`, and the choices of the extension depend
    only on factors inside `B_{t+2ℓ}(v)`.
11. **Randomness.** Inference algorithms are deterministic (Proposition 3.3, not formalized; its key
    step, convexity of TV distance, is `tv_mix_le`). Samplers are modelled by their exact output
    distributions (`seqProb`). The JVV third pass is modelled by its acceptance probabilities.
    Random bit strings, the SLOCAL model and the network-decomposition simulation (Lemmas 3.1, 4.4,
    cited from Ghaffari–Kuhn–Maus) are not formalized, so round complexities appear only as
    localities.
12. **Weights instead of normalized distributions.** Joint distributions are given by nonnegative
    weights `w` (any `μ`, or a Gibbs weight); `μ^τ` is `cond w τ`. A partial configuration `τ ∈ Σ^Λ`
    is a pinning `V → Option Σ`. Feasibility is `Z w τ > 0`.
13. **SSM (Definition 5.1).** `SSM G w R` says: for feasible `σ, τ` with the same domain that agree
    on all `u` with `dist(v, u) < d`, `d_TV(μ^σ_v, μ^τ_v) ≤ R d`. For non-increasing `R` this is
    the paper's `≤ δ_n(dist(v, D))`. When `D` is unreachable from `v`, the paper's `dist = ∞` case,
    our version requires `≤ R d` for every `d`. Rates take values in `[0, ∞]` (see item 3).
    `MSSM` is the multiplicative variant with real rates, as in the paper.
14. **Theorem 5.1 (⇐) parameters.** We assume `R t ≤ δ`, where `R` is evaluated at the shell radius
    `t`. The paper's `t = min{t' | δ_n(t') ≤ δ}` satisfies this. The algorithm has locality `t + 2ℓ`,
    as in the paper. The extension on the shell is any one passing the local test (14)
    (`Classical.epsilon`); the paper enumerates.
15. **Vertex order in Lemma 4.1.** The paper orders `Γ` by IDs; we use any fixed enumeration
    (`Finset.toList`). The result holds for every order.
16. **Theorem 3.4** is formalized as its inequality chain
    `d_TV(μ̃_v, μ^τ_v) ≤ d_TV(μ̃, μ^τ) ≤ d_TV(μ̂, μ^τ) + Pr[fail]` for the mixture
    `μ̃ = (1 − p) μ̂ + p ν` (`theorem_3_4_tv`). Reconstructing `μ̃_v` at `v` by enumerating random
    bits is not formalized.
17. **Not formalized.** Theorem 4.2 and Proposition 4.3 as compositions. The locality `3t + ℓ` of
    `q_{vᵢ}` (eqs. (11), (12)). Corollary 5.3 and the applications (they rely on cited SSM results).
    A repaired Corollary 5.2.
