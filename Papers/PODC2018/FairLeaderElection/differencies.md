# Differences between the formalization and the paper

Paper: A. Yifrach, Y. Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018; arXiv:1805.04778v2 (the version formalized; numbering as there).

## Model (Section 2)

1. **Asynchrony.** The unidirectional ring is the shared model `Cslib.UniRing`
   (`Podc/Computability/Distributed/UniRing/Basic.lean`): deterministic processors whose behaviour is
   a function of the received history (cumulative sent list, monotone; optional termination output),
   FIFO links, oblivious schedules `σ : ℕ → Fin n` (a step delivers the next pending message to `σ t`,
   a no-op if there is none), fair = every processor scheduled infinitely often. Every fair
   asynchronous execution is of this form. The paper's remark "all message schedules are equivalent"
   on a unidirectional ring is *proved* (`exists_le_run`, `terminates_iff`, `outcomeUnder_eq`), and
   most statements are about the schedule-free `outcome` (equal to `outcomeUnder σ` for every fair `σ`).
2. **Wake-up.** Every processor runs its initialization (it may send at wake-up), as in the paper's
   pseudocode where every processor has `Init()`. The paper's text says only the origin wakes up
   spontaneously; honest normal processors send nothing at initialization, so this only gives the
   adversaries more power, and it is used by the Cubic Attack (see item 12).
3. **Messages and identities.** Messages are values in `Fin n` (honest processors reduce incoming
   values mod `n` anyway); processors are `Fin n`, the origin is `0` (the paper's processor 1); ids
   are consecutive along the ring (as the paper assumes for `A-LEADuni` in Sections 3–5).
4. **Randomness.** Each honest processor draws its secret `d i` uniformly from `Fin n`; probabilities
   are counted over `Fin n → Fin n`. A protocol is a family of profiles indexed by a finite uniform
   randomness type (`Game.lean`).
5. **Deviations are deterministic** (adversary strategies do not depend on any randomness). All our
   negative results exhibit deterministic deviations, which is enough. The positive results
   (`claim_D_1`, `isUnbiased_aLead_one`, `isResilient_aLead_one`) are proved against deterministic
   deviations only; for unbiasedness this is equivalent to allowing randomized deviations (a
   randomized deviation is a mixture of deterministic ones), for resilience (Def. 2.3, which asks for
   *some* coalition member not to gain) it is in general weaker.
6. **Outcome.** As in the paper, `outcome = v` iff *all* processors (including adversaries) terminate
   with output `v`; otherwise `FAIL`.
7. **Resilience / unbiasedness** (Def. 2.3 and the definition before Lemma 2.4) quantify over fair
   schedules, rational utilities (`u FAIL = 0`, values in `[0,1]`), coalitions of size exactly `k`
   and deviations. FLE: every leader with probability exactly `1/n` under every fair schedule. The paper
   defines an FLE protocol as a *symmetric* protocol; `IsFLE` does not require symmetry (no
   restriction, since strategies may depend on the id, and `A-LEADuni` is a fixed protocol).

## Section 2

8. **Lemma 2.4** is proved as stated, with the implicit side conditions made explicit: the second
   direction needs `k ≥ 1` (a coalition member must exist) and `ε ≥ 0` (`lemma_2_4`).
9. **New observation (used below):** for every FLE protocol, rational utility and deviation, the gain
   is at most `1 − 1/n` (`expU_le_add_one_sub`), so every FLE protocol is `(1 − 1/n)`-`k`-resilient
   for every `k ≥ 1` (`isResilient_one_sub_inv`).

## Section 3 and Appendix A

10. **The origin's pseudocode (Appendix A) is off by one**: `round` starts at 1, so the origin checks
    its `(n−1)`-th incoming message against `d_1` and sums only `n − 1` values; the honest execution
    would then abort whenever `d_1 ≠ d_2` (for `n ≥ 2`). We follow the verbal description of
    Section 3 (the origin sends `d_1`, forwards `n − 1` messages, and validates its `n`-th incoming
    message), i.e. `round` should start at 0. Not formalized as a counterexample (typo-level).
11. **Lemma 3.3 is imprecise as stated.** (a) "The execution succeeds (outcome ≠ FAIL)" must be read
    as "all honest processors terminate with the same valid output": `outcome` also requires the
    adversaries to terminate with that output, which conditions 1–3 do not constrain. (b) "Sends `n`
    messages" means *at least* `n`, and "its last `l_j` messages" means the messages
    `n − l_j + 1, …, n` (honest processors process only their first `n` messages). (c) "Sums of all the
    outgoing messages" means sums of the first `n` messages. (d) The proof's case analysis swaps the
    numbering of conditions 1 and 2. Our `lemma_3_3` states: all honest processors terminate with
    output `v` iff in some reachable configuration (equivalently, `lemma_3_3_run`, at some time of
    any fair run) every exposed adversary has sent `≥ n` messages, the first `n` sum to `v`, and the
    messages `n, n−1, …, n−l+1` are the secrets of its segment. Requires a nonempty coalition (for
    `C = ∅` the honest execution succeeds, `outcome_aLead`).
12. **Lemmas 3.4/3.5** are formalized in list form (`lemma_3_4`, `lemma_3_5`: the histories of the
    segment processors are `seg m e s`) and used in Lemma 3.3 through `segment_hist`/`segment_pump`.
13. **Correctness of `A-LEADuni`** (implicit in the paper) is proved: the honest execution elects
    `∑ d_i` (`outcome_aLead`) and the protocol is FLE (`isFLE_aLead`).

## Section 4 and Appendix C

14. **Lemma 4.1 needs the origin to be honest.** The paper states it for every coalition with
    segments of length `≤ k − 1`, but its attack (all adversaries just forward) never starts if the
    origin is an adversary: nobody sends anything and the outcome is `FAIL`
    (`lemma_4_1_attack_deadlocks`). We prove Lemma 4.1 under the extra hypothesis `0 ∉ C`
    (`lemma_4_1`). We believe a modified attack (the adversarial origin injects one dummy message)
    proves the lemma in general, but this is not formalized. Theorems 4.2 and 4.3 are unaffected
    (the coalition is chosen with the origin honest, as the paper does in Section 4.3).
15. **Theorem 4.2** is proved as stated (`theorem_4_2'` with `√n ≤ k`, `theorem_4_2` with `n ≤ k²`),
    for `k ≤ n`. The "equally spaced" coalition is replaced by any placement with segments of length
    `≤ k − 1`, the origin honest (greedy segment lengths `fillGaps`, positions `place`); for `k = n`
    the coalition is everybody and outputs `w` at once (`outcome_univ`).
16. **Theorem 4.3 (Cubic Attack)** is proved as stated (`theorem_4_3'` with `2∛n ≤ k`,
    `theorem_4_3` with `8n ≤ k³`, `k ≤ n`). Differences in the construction: the segment lengths
    satisfy the paper's relaxed conditions (`l_k ≤ k − 1`, `l_i ≤ l_{i+1} + k − 1`, total `n − k`),
    chosen greedily from the end below the caps `(k − 1)(k + 1 − i)`; all `k` adversaries attack (the
    paper picks a minimal `k ≤ k'` and lets the other `k' − k` adversaries play honestly — not needed).
    Minor slips in the paper: `∑_{i=1}^{k'−1}(k'−1)i` is written `(k'−1)k'(k'+1)/2` instead of
    `(k'−1)²k'/2` (harmless); the proof of Lemma 4.4 starts with "since `l_1 = max_i l_i`", which does
    not follow from the relaxed conditions (our liveness proof does not need it).
17. **Cubic Attack pseudocode (Appendix C):** the `k − 1` zeros are sent only when
    `count == n − k − l_i` after incrementing `count`, which never happens when `n − k − l_i = 0`;
    the attack then deadlocks (e.g. `n = 4, k = 2, l = (2, 0)`). The verbal description ("transfer
    `n − k − l_i` messages, then send `k − 1` zeros") sends them at wake-up, which we do.
18. **Lemmas 4.4 and 4.5** are proved for a general *rushing attack* (forward `F_a` messages, send
    `z_a` zeros, after `n − k` messages send `M`, zeros and the last `l_a` messages) under explicit
    content/budget conditions (`Params`) and liveness conditions (`Live`); both Lemma 4.1's attack
    and the Cubic Attack are instances (`rushing_outcome`, `lemma_4_4_4_5`). The termination proof
    (Lemma 4.4) is a counting argument on the stuck configuration (`reach_finalCfg`), not the
    paper's round-by-round narrative.
19. **Corollary 4.6 is false at the boundary `ε = 1 − 1/n`**: the paper states it for
    `0 ≤ ε ≤ 1 − 1/n`, but by item 9 `A-LEADuni` (like every FLE protocol) is
    `(1 − 1/n)`-`k`-resilient (`corollary_4_6_boundary_false`). Proved for `0 ≤ ε < 1 − 1/n`
    (`corollary_4_6`, `corollary_4_6'`; Theorem 4.3 and Lemma 2.4).
20. **Appendix C (randomly located adversaries, Theorem C.1)** and **Claim B.1** are not formalized.
21. **Conjecture 4.7** is not addressed.

## Section 5 and Appendix D

22. **Theorem 5.1** (`∜n`-resilience) is **not formalized**.
23. **Claim D.1 omits the bound `k < n/2`** (false as stated, with no bound on `k`; the claim is a
    standalone warm-up, not used elsewhere): for `n ≥ 3` the block of all processors but the
    origin forces any outcome by Lemma 4.1 (`claim_D_1_false`). The proof uses that the honest segment
    is longer than the coalition ("length `k > l`" in the text should read `l > k`), and the
    introduction states the result of [4] for `k < n/2`. We prove it for consecutive coalitions with
    `2k + 1 ≤ n` (`claim_D_1`), with any position of the origin (the paper assumes it honest), against
    deterministic deviations. The proof formalizes the information-flow argument by a simulation
    (`reach_tau`): until the coalition has received the secret of the first honest processor, changing
    that secret does not change what the coalition sees. Consequence: `A-LEADuni` is `0`-`1`-unbiased
    and `0`-`1`-resilient for `n ≥ 3` (`isUnbiased_aLead_one`, `isResilient_aLead_one`).

## Sections 6, 8 and Appendices E, G, H

24. `PhaseAsyncLead` (Theorem 6.1, w.h.p. over a random function, Appendix E), Appendices G and H
    are not formalized.

## Section 7 and Appendix F

25. **Model for Section 7** (`TreeModel.lean`): general asynchronous message passing on a finite
    simple graph; a processor is a function of its received history of `(sender, message)` pairs
    (cumulative sends per neighbour, monotone; optional output); FIFO links; oblivious schedules are
    sequences of directed links (no-op if nothing pending), fair = every directed edge infinitely
    often; protocols need not be symmetric; random inputs from finite nonempty sets, uniformly (the
    paper: infinite random strings — a restriction). Deviations may be arbitrary strategies of the
    coalition members (deterministic given their own inputs). Two-party protocols are modelled as the
    unidirectional ring of size 2 (`TreeTwoParty.lean`), where executions are schedule independent.
26. **Definition 7.1 as written is degenerate** (a wording slip: the sentence after it describes the
    intended notion) (`IsKSimTreeLiteral.card_fiber_le_one`: a homomorphism
    into a loopless tree with connected fibres has singleton fibres). We use the intended notion
    `IsKSimTree`: a partition into connected parts of size `≤ k`, every edge inside a part or between
    tree-adjacent parts.
27. **Theorem 7.2 is false at `ε = 1/n` for `n = 2`** (`thm_7_2_boundary_false`: `K₂` is a 1-simulated
    tree, `k2FLE` is FLE, and every FLE protocol is `(1 − 1/n)`-resilient, `isResilient_one_sub`). For
    `n ≥ 3` at `ε = 1/n` the status is open (the method gives gain only `1 − |A|/n`).
28. **The reduction FLE → coin toss has a gap** (Theorem 8.1 and the last step of the proof of
    Theorem 7.2): the parity coin can succeed (all processors output leaders of the same parity) while
    the election fails, so `Pr(coin = 0) ≤ Σ_{i even} Pr(leader = i)` does not follow; the proof also
    assumes `n` even. Replaced by `not_resilient_of_assures`: a coalition of size `≤ k` assuring that
    the leader lies in a proper subset contradicts `ε`-`k`-resilience for every `ε < 1/n`, every `n`.
29. **Lemma F.2** is proved in a generalized form (`lemma_F2`): arbitrary outputs and arbitrary target
    sets `Q₁, Q₂`, finite input sets; the hypothesis "bounded amount of messages" is derived from
    termination with finite inputs (`exists_bdd`). Its hypothesis that every honest execution succeeds
    (implicit in the paper) is explicit.
30. **Lemma F.3 and Corollary F.4 are not formalized; their proofs have gaps.** The "super-node" `b`
    simulating `T ∖ {a}` is not a processor of the model: its behaviour toward `a` depends on the
    interleaving of `a`'s messages with internal events, so executions of `P` are not executions of the
    two-party `P_a`, and neither "`a` assures in `P_a` ⇒ `a` assures in `P`" nor "`b` is a dictator in
    `P_a`" transfers to single processors; moreover, for a super-node, termination under all fair
    schedules does not bound the number of messages (ping-pong until a third processor's message
    arrives), so Lemma F.2's boundedness hypothesis is genuinely missing. Connected fibres simulating
    tree nodes (Corollary F.4) raise the same issue. **Theorem 7.2 is proved only for `n = 2`**
    (`thm_7_2_two`, all `1 ≤ k ≤ 2`, `ε < 1/n`); for `n ≥ 3` it is neither proved nor refuted.
31. The remark of Section 7 that every graph is simulated by a **tree of size 2** with parts of size
    `≤ ⌈n/2⌉` is false (`K₁,₃`); Claim F.5 (a star partition) is correct but not formalized.
32. **Theorem 8.1** is not formalized (see item 28).
