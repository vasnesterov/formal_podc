# Differences between the formalization and the paper

Paper: J. Burman, H.-L. Chen, H.-P. Chen, D. Doty, T. Nowak, E. Severson, C. Xu,
*Time-Optimal Self-Stabilizing Leader Election in Population Protocols*, PODC 2021
(arXiv:1907.06068v5, 29 Nov 2021; numbering follows it).

## Model (Section 2)

1. **Agents are labelled**: a configuration is a function `A → Q` with `Fintype.card A = n`, not a
   multiset. Interactions are ordered pairs of distinct agents.
2. **Randomized transitions** `T : S × S → Dist(S × S)` are modelled by their *support*
   `δ p q ⊆ Q × Q` (`NProtocol`, `Model.lean`). All formalized statements about self-stabilization
   only depend on the support. The model does not require supports to be nonempty; this only
   enlarges the class of protocols covered by the lower bounds (Theorem 2.1), whose proofs never use
   nonemptiness.
3. **"With probability 1"** is formalized as `SelfStabilizes good`: from every configuration some
   *stably correct* configuration (all reachable configurations are correct) is reachable. For a
   finite state space and the uniformly random scheduler this is equivalent to the paper's notion:
   `RandomScheduler.lean` proves, for every row-stochastic kernel whose positive entries are exactly
   the protocol's steps, that `SelfStabilizes` implies that the probability of not being stably
   correct tends to `0` (`tendsto_not_stablyCorrect`, via CSLib's absorption theorem), and that if no
   stably correct configuration is reachable from `C` the probability of being stably correct is `0`
   at all times (`prob_stablyCorrect_eq_zero`). The kernel of a deterministic protocol under the
   uniform scheduler is `uniformKernel` (`uniformKernel_pos_iff`, `uniform_tendsto`). For lower bounds
   (Theorem 2.1) the reachability hypothesis is the *weakest* reading (positive probability), so those
   results are stronger than stated.
4. **SSLE/SSR outputs**: leader election uses an output map `leader : Q → Bool`, ranking an output map
   `rank : Q → Fin n` (correct iff `a ↦ rank (C a)` is a bijection). For `Optimal-Silent-SSR` the rank
   output of a non-settled agent is "no rank" and a configuration is correct (`Ranked`) iff all agents
   are settled with pairwise distinct ranks in `{1, …, n}`.
5. **Silent** configurations: every enabled interaction leaves both states unchanged (for randomized
   transitions: every outcome in the support is the null outcome).
6. Time complexity (parallel time, expectation, w.h.p.) is not modelled. All time bounds of the paper
   are **not formalized** (see the end of this file).

## Theorem 2.1 (cited from Cai–Izumi–Wada [21])

7. The paper only cites the result. We formalize the proof of Cai–Izumi–Wada (SIROCCO 2009 / ToCS 2012,
   "closed-set argument": Lemmas 1–5 and Theorem 1 there). Their proof is stated for one leader state
   and deterministic transitions; ours handles an arbitrary set of leader states (output map) and
   randomized transitions (their Remark 1), and uses only the reachability hypothesis.
   (`NProtocol.card_le_card_states`)
8. We assume `Q` nonempty (if `Q = ∅` there are no configurations and SSLE holds vacuously).
9. "Strongly nonuniform" ("for any `n₁ < n₂` a different set of transitions is used") is formalized as:
   no protocol (same `Q`, `δ` and leader output) solves SSLE on `Fin n₁` and on `Fin n₂`
   (`NProtocol.not_solvesSSLE_two_sizes`). The proof is the paper's sketch (a leaderless
   sub-population of size `n₁` of a stably correct size-`n₂` configuration creates a second leader),
   made precise by `reachable_embed`. No gap.

## Lemmas 2.2, 2.3 and Theorem 2.4 (`Silent-n-state-SSR`)

10. Inequality (1) is formalized literally (`IsBarrier`, sum over `d ∈ {0,…,r}` of `m_{(k−d) mod n}`)
    and shown equivalent to a window count (`isBarrier_iff`).
11. **Lemma 2.2** is proved by a different argument: a rank `k` maximising `∑_a ((k − rank a) mod n)` is
    a barrier (shifting `k` down by `r + 1` would increase this sum by `n·(win − (r+1))`). The paper's
    prefix-sum proof contains index typos (**typo**): it writes `∑_{j=1}^{n−1} m_j(C) = n` (should start at
    `j = 0`) and `S_k − S_{k−r+1}` (should be `S_k − S_{k−r−1}` with `S_{−1} = 0`); with these fixes the
    paper's argument is correct.
12. **Lemma 2.3**: no gap (our proof follows the paper).
13. **Theorem 2.4 (correctness)**: the paper's correctness argument is probabilistic (each stage
    `T_s − T_{s−1}` is finite). We prove stronger deterministic facts: in *every* execution, under any
    scheduler, at most `n(n−1)` interactions change the configuration (`card_changes_le`), every weakly
    fair execution becomes silent in a correctly ranked configuration (`weaklyFair_eventually_ranked`),
    and the protocol solves SSR and SSLE (`leader ↔ rank = 0`) in the reachability sense
    (`solvesSSR`, `solvesSSLE`), hence with probability 1 (item 3).
14. **Typo** in the proof of the lower bound of Theorem 2.4: the initial configuration is given as
    "`m_1(C_0) = 2`, `m_{n−1}(C_0) = 0`, and `m_i(C_0) = 1` for all `i ∈ {1, …, n−2}`", which is
    contradictory for `m_1`; the text before (and the argument) use `m_0(C_0) = 2`.
15. The time bounds of Theorem 2.4 (`Θ(n²)` in expectation and w.p. `1 − exp(−Θ(n))`) are not
    formalized. The upper-bound proof's "stochastically dominated by the fratricide process" step is
    only sketched in the paper (not checked).

## Observation 2.5

16. Formalized as stated, with the uniform transitions replaced by their support (`δ = univ` on active
    pairs). We prove: from every configuration of three agents a silent configuration is reachable in
    at most one interaction, every silent configuration has exactly one leader, so the protocol solves
    (silent) SSLE; and for every map `r : S → Fin 3` the protocol does not solve SSR with output `r`
    (an odd cycle has no proper 2-colouring). No gap.

## Observation 2.6

17. **Deterministic core** formalized (`obs26_null_of_ne`, `obs26_two_leaders`): in `C'` (a silent
    one-leader configuration with the leader state copied to `u`) there are two leaders and every
    interaction other than `{ℓ, u}` is null. For deterministic protocols under the uniform random
    scheduler we also prove the geometric tail: the chain is still at `C'` after `t` interactions with
    probability `≥ (1 − 2/(n(n−1)))^t` (`obs26_stay_prob`), which gives the `Ω(n)` expected time. The
    resulting expectation `≥ C(n,2)` interactions (tail-sum formula) is not written out in Lean.
18. **False only in a degenerate case.** "For any `α > 0`, probability `≥ ½ n^{−3α}` to require
    `≥ α n ln n` convergence time" fails for `n = 2`: `Silent-n-state-SSR` (a silent SSLE protocol) is
    correct after the first interaction from every configuration under every schedule, i.e. its
    convergence time is at most `1/2`, while `α n ln n = 2 ln 2 > 1/2` for `α = 1`
    (`obs26_n2_counterexample`). Likewise "expected time `≥ n/3`" uses `C(n,2)/n ≥ n/3`, false for
    `n = 2`.
19. **Proof gap (statement true for `n ≥ 4`).** The displayed estimate
    `(1 − 3/n²)^{α n² ln n} ≥ ½ e^{−3α ln n}` is false for large `α` at fixed `n` (since
    `n² ln(1 − 3/n²) < −3`; e.g. `n = 10`, `α = 7`), and `1/C(n,2) < 3/n²` needs `n ≥ 4`. The claim itself
    holds for `n ≥ 4` because the true success probability `p = 2/(n(n−1))` satisfies
    `n² ln(1 − p) ≥ −3` there (checked by hand, not in Lean). For `n = 3` the claim fails for large `α`:
    `Silent-n-state-SSR` makes at most `6` changes, each enabled with probability `≥ 1/3` per
    interaction, so its tail decays like `(2/3)^k = e^{−0.405 k}` while the claimed bound at
    `k = 9 α ln 3` interactions is `½ e^{−0.333 k}`; an exact Markov-chain computation shows the bound is
    violated from `α = 10` on (checked numerically, not in Lean).

## Section 3–4: `Propagate-Reset` and `Optimal-Silent-SSR` (Protocols 2–4)

20. **Off-by-one in Protocol 3, line 9 (false as printed).** The recruitment guard
    `2 · i.rank + i.children < n` never allows rank `n` to be assigned (new ranks come only from
    `Reset`, rank 1, and from recruitment, rank `2·rank + children < n`). Hence from every
    configuration without a settled agent of rank `n` — e.g. all agents `Unsettled`, or any
    configuration right after a complete reset — no correctly ranked configuration is ever reachable,
    for every `n ≥ 2` and all parameters (`asWritten_never_ranked`, `asWritten_not_selfStabilizes`).
    So Theorem 4.3 is false for the protocol as printed. Figure 1 (rank 12 assigned for `n = 12`)
    shows the intended guard `2 · i.rank + i.children ≤ n`, used in `Params.fixed = true`. Our
    explicit-state model checker (`tools/oss.py`) confirms: as printed, the stable set is unreachable
    from most configurations already for `n = 2, 3, 4`; with `≤`, it is reachable from every
    configuration for all `n ≤ 4` and all small parameters (`Rmax, Dmax, Emax ≥ 1`).
21. **Under-specified pseudocode (our interpretation, `OptimalSilent.lean`):**
    * Protocol 3's field list gives `resetcount ∈ {1, …, Rmax}`, but dormant agents need
      `resetcount = 0` (Protocol 2); we allow `0`.
    * `Propagate-Reset(a, b)` is written "for Resetting agent `a`" but Protocol 3 calls
      `Propagate-Reset(a, b)` also when only the responder `b` is Resetting; we then call it with the
      agents swapped.
    * The `leader` field of an agent brought into `Resetting` by line 2 of Protocol 2 is not set in
      the pseudocode; following the text of Section 4 ("all agents set themselves to L upon entering
      the Resetting role") it is `L`.
    * "`resetcount` just became 0" is read as "positive at the start of the interaction and 0 now",
      so an agent brought in by line 2 decrements its fresh `delaytimer = Dmax` in the same
      interaction.
    * Line 10 tests `b.role ≠ Resetting` even for `i = b`; we read it as "the other agent is not
      Resetting" (awakening by epidemic).
    * Decrements are truncated at `0`; triggered agents get `delaytimer = Dmax` (irrelevant while
      propagating); the sub-steps of an interaction are applied in the order of the pseudocode
      (lines 1–4, 5–7, 8–12 for `(a, b)` then `(b, a)`, 13–18).
    The off-by-one (item 20) does not depend on any of these choices.
22. **Correctness of the fixed protocol** (`fixed_reachable_ranked`, `fixed_selfStabilizes`): for `n ≥ 2`,
    `Rmax ≥ 2`, `Dmax ≥ 2` (any `Emax`), from every *valid* configuration (fields in their ranges:
    settled ranks in `{1,…,n}`, `children ≤ 2`, `errorcount ≤ Emax`, `resetcount ≤ Rmax`,
    `delaytimer ≤ Dmax`; preserved by `valid_step`) a correctly ranked configuration is reachable, and
    it is silent. The paper's `Rmax = 60 ln n ≥ 41` and `Dmax = Θ(n)` satisfy the extra hypotheses
    (for small `n` the model checker shows they are not even needed). Our proof is a deterministic
    schedule construction (drain/wake Resetting agents, create a triggered pair, sweep every other
    agent into dormant `F` using the pair, elect ranks 1 and 2, recruit the rest in BFS order), not the
    paper's probabilistic epoch argument. Since the state type uses unbounded `ℕ` fields, the
    probability-1 corollary (item 3) applies to the finite valid state space; we did not instantiate
    `RandomScheduler.lean` for it.
23. Theorem 4.3's time bound `O(n)`, Corollary 4.4, Lemmas 3.2, 3.3, Theorem 3.4, Corollary 3.5 and
    Lemmas 4.1, 4.2 are probabilistic and **not formalized**; the state count `O(n)` is not formalized.

## Not formalized

24. Lemmas 2.7–2.11 (epidemic, roll call and bounded epidemic processes), all expected / w.h.p. time
    bounds, Section 5 (`Sublinear-Time-SSR`, `Detect-Name-Collision`, Lemmas 5.1–5.6, Theorem 5.7),
    Section 6 (derandomization), footnote 7 (immobilizing the leader bit), the `Ω(log n)` remark.
