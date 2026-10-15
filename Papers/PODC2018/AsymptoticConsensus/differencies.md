# Differences between the formalization and the paper (arXiv v2 of FNS'18)

## Errors in the paper

1. **Theorem 4 (⇐) is false.** The statement is: if some asymptotic consensus algorithm has, for
   all `N' ⊆ N` and all `C₀`, a valency `Y*_{N'}(C₀)` that is a singleton or disconnected, then
   exact consensus is solvable in `N`.
   * Counterexample (`theorem4_false`, `theorem4_mpr_counterexample`). Take `n = 2`,
     `N = {H₀,H₁,H₂}`, values in `ℝ`, and the algorithm `fd` of `FirstDeviation.lean`.
   * `fd` works as follows. The agent that is deaf in the first non-`H₀` round `t` decides
     `x_self` if `t` is odd and `x_other` otherwise. The other agent copies that decision, or decides
     the same value by the same parity rule if it is deaf in round `t+1`. Before any deviation the
     output is `x_0`.
   * `fd` solves asymptotic consensus and every limit is `x₀` or `x₁`. So all valencies are finite,
     hence singletons or disconnected.
   * Exact consensus is not solvable in `N`. We prove this from Theorem 1
     (`not_exactSolvable_N3`): an exact algorithm would yield rate 0.
   * **Root cause.** The proof states "`δ_{N'}(C_t) → 0` by Convergence and Agreement". This holds
     iff the consensus function is continuous. The paper itself notes that it need not be
     (Section 2.1). For `fd` it fails (`fd_not_vanishing`).
   * **Repair.** We add the hypothesis `VanishingValency` (valency diameters vanish along every
     execution of every submodel, i.e. the consensus function is continuous). Then (⇐) holds
     (`theorem4_mpr_repaired`). The equivalence `theorem4_repaired` follows once we assume the cited
     characterization of [12] (`CouloumaHyp`: unsolvable ⇒ some nonempty source-incompatible,
     α-connected submodel). Its (⇒) direction holds as stated (`theorem4_mp`). The algorithm built
     from an exact one also has vanishing valency diameters (`vanishing_toAsym`).
   * Charitable reading: `N'` ranges over **nonempty** submodels, as in our `ValencyProp`. For
     `N' = ∅` the valency is `∅`, which is connected and not a singleton, so the iff would fail in
     the other direction.
   * The refutation also applies to binary consensus. `fd` only ever outputs initial values, so with
     initial values in `{0,1}` all limits are binary. Exact binary consensus is also unsolvable in
     `{H₀,H₁,H₂}` (the classical two-agent lossy-link impossibility). The binary variant is not
     formalized separately.
   * The proof of the repaired (⇐) works in any real normed space. We embed `ℝ` along the segment
     `[0, v]` with a dual vector, so the paper's "WLOG d = 1" is not needed.

2. **Definition 15 is stated imprecisely (typo-level).** It restates Coulouma et al.'s Definition 4.7
   loosely, with `In_S(G) = ⋃_{j∈S} In_j(G)` (a set of nodes). The per-agent meaning
   `AlphaRel K G H := ∀ i ∈ R(K), In_i(G) = In_i(H)` is clearly intended: the remark `D = 2` for
   `{H₀,H₁,H₂}` (`alphaDiam_N3`), the proof of Lemma 20 (via Lemma 6) and the proof of Lemma 24 all
   use it. Under that reading, Lemma 20 and Theorem 5 are correct and proved.
   The formalization also records what goes wrong under the literal reading:
   * `alphaDiamLit_N3`: the α-diameter of `{H₀,H₁,H₂}` becomes 1, since `R(H₀) = {1,2}` and
     `In_{1,2}(G) = {1,2}` for every `G`.
   * `lemma20_literal_false`: for Algorithm 1 from `(0,1)`, `Y*(H₁.C₀) ⊆ [0,1/3]` and
     `Y*(H₂.C₀) ⊆ [2/3,1]` are disjoint.
   * `theorem5_literal_false`: the literal Theorem 5 would claim a rate `≥ 1/2` for Algorithm 1,
     whose rate is `1/3`.

3. **Proof of Theorem 11 is broken** (the statement is fine; we prove it differently).
   * It defines `Ã` by "repeatedly running A … restarting A with the decision values". With a fixed
     `ε` this need not converge, so `Ã` is not an asymptotic consensus algorithm.
   * It assumes `T < log₃(Δ/ε)` where `log_{D+1}` is meant.
   * It writes `δ_N(C₀) ⩽ Δ(y(0)) ⩽ Δ/n` where `δ_N(C₀) ≥ Δ/n` is meant.
   * We prove Theorems 8–11 directly with finite-horizon decision sets (`decSet`), without
     reducing to asymptotic consensus.

## Gaps and imprecisions (fixed)

4. **Lemma 20 uses `R(K) ≠ ∅`.** This is an implicit citation, not a gap. `K` belongs to a model
   in which `A` solves asymptotic consensus, so `K` is rooted by [8, Thm 1]. We prove this necessity
   direction (`Alg.Solves.exists_root`) and use it in Lemmas 20 and 21.
5. **Theorem 3, claim (8) "for every initial snapshot `S₀`".** The reduction uses
   `δ_{P_seq}(S₀) = δ_P(S₀)` "by Lemma 13", but Lemma 13 only provides some `S₀` with
   `δ = Δ` (agents 4…n are never deaf in `P_seq`). For the theorem only one good `S₀` is needed,
   which we use.
6. **Theorem 5 / Lemma 21 hypothesis.** The paper assumes "exact consensus is not solvable" and
   invokes Theorem 19 of [12] to get a source-incompatible β-class. Only source-incompatibility
   of `N` is used. We state `Alg.theorem5` and `Alg.lemma21` with `SourceIncompatible N` and derive
   the paper's form (`theorem5_paper`, `lemma21_paper`) by proving the easy direction of [12]
   (a common root makes exact consensus solvable, by flooding: `exactSolvable_of_common_root`).
   Theorem 19 and Lemma 17 (β-classes) are **not** formalized. They appear only as the hypothesis
   `CouloumaHyp` of the repaired Theorem 4.
7. **Lemma 21 constant.** We prove `δ_N(C₀) ≥ ‖v‖/(n−1)`, better than the paper's `Δ/n`, with a
   chain argument that works in any normed space (no reduction to `d = 1`, no inf/sup).
   Theorem 11 accordingly gets `(n−1)` instead of `n`.
8. **Lemma 5 / finiteness.** Lemma 5 needs `N` finite. That is automatic for finitely many agents
   (`Set.toFinite`). Our engine works with the chain lemma (`exists_ediam_le_mul`), which needs only
   a finite set of moves.
9. **Theorem 2** is proved under the paper's closing remark: three graphs `F_i, F_j, F_l` suffice.
10. **Theorem 6.** Only the network-model statement is formalized (`theorem6`: rate in `N_A` is
    `≥ 1/(⌈n/f⌉+1)`).
    * Not formalized: the asynchronous message-passing model, the claim that round-based algorithms
      realize every `N_A` pattern, and the remark on time versus rounds.
    * The hypotheses are weaker: `n ≥ 2`, `1 ≤ f < n` (the paper has `n ≥ 3`, `f < n/2`).
    * In Lemma 24 our chain runs from `G` to `H` with `H_r` using `H` on the first `rf` agents. The
      paper writes `H₀ = G, H_q = H` with the opposite mixing, which is inconsistent with its own
      definition of `H_r` (it gives `H₀ = H`). This is harmless.
11. **Theorem 10.** We prove `Δ ≤ 2^{⌊T/(n−2)⌋} ε`, which gives exactly `T ≥ (n−2) log₂(Δ/ε)`
    (`theorem10_logb`). Leftover rounds are played as `Ψ₀` before the blocks.
12. **Theorems 8–11.** These assume `0 ≤ Δ` (resp. `Δ, ε > 0` for the log forms). `ε, Δ` are fixed
    parameters of the algorithm, not inputs. Only time-`T` decisions are constrained, which is a
    weaker hypothesis and gives stronger lower bounds.

## Modelling differences

13. **Initial states.** `init i v` may depend on the agent. The paper has a common set of initial
    states, from which our class embeds. `y_i(0) = x_i` is not required. Both choices make the
    class of algorithms larger, so the lower bounds stronger.
14. **Specification.** Convergence, Agreement and Validity are combined into "all outputs converge
    to a common `z ∈ hull(x)`" (equivalent).
15. **Valency.** The valency is history-free: limits of continuations from `C`. It equals the
    paper's `Y*_N(C)` on reachable configurations (`val_eq_paperVal`). Properties and snapshots
    (§6.1) are replaced by block patterns (`BlockPat`), which are shift-invariant at block
    boundaries. Lemmas 9–13 are thus subsumed by the block versions of Lemmas 3, 4, 7, 8.
16. **Diameters and rates** are in `ℝ≥0∞` (`Metric.ediam`, `limsup` of `δ^{1/t}`).
    * The lower bounds are stated as `r ≤ rate`, e.g. `3⁻¹ ≤ A.rate N`.
    * Theorem 3 is stated as `(2^{1/(n−2)})⁻¹ ≤ rate`.
17. **Dimension.** All lower bounds, Algorithm 1 and `fd` work in any (nontrivial) real normed
    space, which covers `ℝ^d`. The midpoint algorithm is only for `ℝ`.
18. **Upper bounds.**
    * Algorithm 1 (`= 1/3` in all rooted 2-agent graphs) and the midpoint algorithm (`= 1/2` in all
      non-split graphs, `n ≥ 3`) are proved.
    * The amortized midpoint algorithm of [9] (`(1/2)^{1/(n−1)}` in rooted models) is **not**
      formalized, so Theorem 3's tightness remains cited.
    * Section 2.2's Theorem 2 (continuity of convex-combination algorithms) is proved for the
      averaging algorithms used here, in valency form (`Averaging.vanishing`).
19. **Numbering.** The paper numbers the cited Theorem 1 ([8]) and the continuity theorem
    (Section 2.2) as Theorems 1–2, clashing with the main Theorems 1–2. Lean names follow the main
    numbering.
20. **Not formalized.**
    * Theorem 7 (MinRelay, asynchronous crashes).
    * The exact-consensus characterization of [12] (Theorem 19), β-classes (Definition 16,
      Lemma 17).
    * The cited sufficiency direction of [8] (every rooted model admits an asymptotic consensus
      algorithm).
