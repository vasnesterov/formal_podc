# Differences between the formalization and the paper

Paper: K. Censor-Hillel, B. Haeupler, D. E. Hershkowitz, G. Zuzic, *Broadcasting in Noisy Radio
Networks*, PODC 2017 (arXiv:1705.07369v1).

## Proof gaps and errors (statements true)

1. **Lemma 15, impossibility half (verdict-relevant, 🛠️).** The paper's argument is internally
   inconsistent:
   - it proves `E[Xᵢ] ≥ (log n)/4` and then uses `E[Xᵢ] ≤ (log n)/4`;
   - "on average `(log n)/16`" does not follow from `(k log n)/4` rounds;
   - Chernoff is applied to `Xᵢ`, which is not a sum of independent indicators;
   - Chernoff is applied to `S = Σ Sᵢ` without independence under an adaptive schedule;
   - the resulting bound `exp(-Ω(E[S]))` is vacuous for `E[S] → 0`, and is then rewritten as
     `exp(-Ω(n^c))`.

   Replaced by the coupling argument `star_prob_delivered_le`. For an adaptive schedule with
   `R < (k - m + 1)·T` rounds, `P(delivered) ≤ C(k, m)·((1 - p^T)^n)^m`. With `m = ⌊k/2⌋ + 1` and
   `n p^T ≥ 2` this is `< 1 - 1/k` (`star_routingRounds_ge`), so `routingRounds k ≥ ⌈k/2⌉·T` with
   `T = ⌊log_{1/p}(n/2)⌋`.
2. **Lemma 15, possibility half.** The domination `Pr(Y ≥ t) ≤ Pr(H ≥ t)` needs the `Yᵢ` to be
   independent. They are defined by a single adaptive run; independence holds only after the
   per-message coupling (`Coupling.lean`, `StarCoupling.lean`), which the paper does not mention. The
   paper's `Pr(Hᵢ ≥ t) = (1/2)^t` should be `(1/2)^{t-1}` for a geometric variable on `{1, 2, …}`
   (harmless). We use our own exponential-moment bound instead of Doerr's Theorem 34
   (`sum_pow_excess_le`, `star_greedy_succeeds`). The greedy schedule uses `k(a + b)` rounds with
   `a = ⌈log_{1/p} n⌉` and `b` a constant with `(2/(1+p))^b ≥ 4`, and fails with probability
   `≤ 2^{-k}`.
3. **Lemma 25: under-specified construction.** "Broadcast `m_{i1}` until it succeeds" assumes the
   schedule observes the sender's coin, which Definition 14 does not provide.
   - Ours: node `u` broadcasts the least sub-message `(i, j)` still unknown to one of its faultless
     receivers in round `t`. A clean round delivers it to all of them, so the set of missing `j`
     shrinks by one per clean round.
   - Only nodes that effectively broadcast in round `t` of the faultless run may transmit in
     meta-round `t`, so extra knowledge gained through fewer collisions never creates new collisions
     (`SenderTransform.act`, `inv_succ`, `delivered_of_good`).
   - The meta-round length is `L = m·a` and the sub-message count `x = m·b` with `b/a < 1 - p`
     rational and `m → ∞` (`frequently_le`). This replaces the paper's `x(1-p)^{-1}(1+η)`.
4. **Lemma 25: typos.** In "sends `k'₀ = k₀x` messages in `(τ-ε)^{-1}(1-p)^{-1}(1+η)` rounds" the
   factor `k'₀` is missing (the later formula `k'₀(τ-ε)^{-1}…` is the intended one).
5. **Lemma 16.** The proof is fine up to constants. We use `⌈(4k + 2n)/(1 - p)⌉` Reed–Solomon packets
   and Chernoff with `λ = 1/2` (`starCoding_succeeds`). The paper's `100k + 100 log n` for `p = 1/2`
   works too; we keep `2n` instead of `2 log n` because it changes nothing as `k → ∞`. The upper bound
   "`Ω(k)` rounds are necessary" is proved information-theoretically (`starCoding_rounds_ge`: `k ≤ 2R`
   when `|A| ≥ 4`). It relies on packets being no larger than messages.

## Modelling choices

6. **Fault parameter.** The paper proves Lemma 15 for `p = 1/2` ("for concreteness"). We prove all
   results for every constant `p ∈ (0, 1)` (Lemma 16 and Lemma 25 also for `p = 0`).
   Borderline call (R4/R6): at `p = 0` (no faults) Lemma 15 is false, since the star then has
   throughput 1. We read "with receiver faults" as `p > 0`, because the paper treats the faultless
   setting separately throughout. So this is not counted as a statement issue.
7. **`Θ(·)` in `n`.** We prove: there are `c₁, c₂ > 0` and `n₀`, depending on `p`, such that for all
   `n ≥ n₀`, `c₁/log n ≤ τ^R(star n) ≤ c₂/log n` (`lemma15`). The constants are `c₁ = log(1/p)/2` and
   `c₂ = 8 log(1/p)`. Similarly `ofReal((1-p)/8) ≤ τ^NC ≤ 2` (`lemma16`), and the gap lies between
   `c log n` and `c' log n` (`theorem17`).
8. **Throughput (Definition 1).** We use `limsup_{k→∞} k / rounds(k)` in `ℝ≥0∞`, where `rounds(k)` is
   an `ℕ∞` infimum (`⊤` if no schedule succeeds, giving ratio 0). The paper's ε-reformulation after
   Definition 1 is not needed.
9. **Success probability.** "Succeeds with probability `≥ 1 - 1/k`" uses the product law of the coins
   of rounds `< R` (`prob`). For coding it is required for every message vector `m`
   (`CodingSucceeds`), which is weaker than "for all `m` simultaneously" and so strengthens the coding
   lower bound on rounds.
10. **Adaptive routing (Definition 14).** A schedule is a function of the round number and the
    knowledge state (all pairs `(u, i)` with `u` knowing `mᵢ`), and outputs an action for every node.
    Broadcasting an unknown message means staying silent; this is the paper's convention for routing
    and equivalent to "broadcast a message they know". The lower bound would also hold for schedules
    that see all past coins (the coupling only needs causality), but it is stated for the paper's class.
11. **Faultless schedules** (Lemma 25, Definition 1 faultless) are static, `round → node → action`,
    run with all coins clean. Lemma 25 is stated for the optimal faultless throughput
    `faultlessThroughput G s`, which is the case used in Theorem 28. `frequently_le` gives the
    per-schedule statement.
12. **Coding model.**
    - Messages and packets are drawn from one finite alphabet `A k`. The paper has `O(log(nk))`-bit
      messages and packets; for Lemma 16 we require finite fields with `|F k| ≥ k²`, and
      `galoisAlphabet` (`GaloisField 2 (2⌊log₂ k⌋+2)`, `O(log k)` bits) shows this is satisfiable
      within the paper's message size.
    - A node's action is a function of its own input (the source knows `m`) and its reception history.
      Decoders are functions of the final history.
    - Reed–Solomon coding is implemented by Lagrange interpolation over `F k`; the paper uses it as a
      black box.
13. **Star.** The source `none` plus `n` leaves `some i`, as in the paper's footnote ("`n` instead of
    `n - 1`").
14. **Shared topology gap (Definition 2).** Theorem 17's corollary is read as "the star with `n` leaves
    witnesses a ratio `≥ c log n`". We do not define the max over all topologies.

## Not formalized

- Lemma 4 (`G_w ≤ G_s`).
- Section 4 (Lemmas 5–13: Decay, FASTBC, Robust FASTBC, RLNC).
- Lemmas 18–24 and Theorem 24 (they need the construction of [19]).
- Lemma 26 (coding transformation). The proof has a gap we did not resolve: coding schedules may
  choose silence based on packet contents, so the `x` parallel copies in a meta-round may disagree on
  whether `u` broadcasts, and the construction "u computes `F = (f_u^r(copy 1), …, f_u^r(copy x))`" is
  then undefined. We did not decide whether the statement holds.
- Theorems 27–28 (they use results of [3]).
- Appendix A (Lemmas 29–33).
