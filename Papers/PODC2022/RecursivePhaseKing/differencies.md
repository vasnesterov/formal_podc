# Differences between the formalization and the paper

Paper: C. Lenzen, S. Sheikholeslami, *A Recursive Early-Stopping Phase King Protocol*, PODC 2022,
DOI 10.1145/3519270.3538425 (proceedings version; no arXiv version exists). Node `i` of the paper
is `i - 1` in Lean (`Fin n`), iterations are 0-based as in the paper's Algorithm 4.

## Errors in the paper

1. **Lemma 3.1 is false for `f = 2` (false statement; off by one iteration).** Lemma 3.1 claims
   that some iteration `j ≤ ⌈log(max{f/2, 1})⌉` of Algorithm 4 has fewer than a third faulty
   electors. For `f = 2` the bound is `0`, but the first elector set `{1, 2, 3, 4}` can contain
   both faulty nodes (2/4 ≥ 1/3). Counterexample: `n = 7` (`t = 2`), faulty nodes `1, 2`
   (`lemma_3_1_false`). The proof's final inequality
   `Σ_{j=0}^{⌈log(f/2)⌉} (2^j + 1) = 2^{⌈log(f/2)⌉+1} − 1 + ⌈log(f/2)⌉ + 1 > f` fails exactly for
   `f = 2` (both sides are 2); the case split "the claim is trivial for `f ≤ 1`" should have been
   `f ≤ 1` vs. `f ≥ 3` plus `f = 2`. A brute-force check over all `n < 3000` and all `f ≤ t`
   confirms that `f = 2` is the only failing case (apart from the degenerate `n ≤ 3`, item 3).
   Corrected bound: `jStar f`, the least `J` with `2^{J+1} + J > f` (`lemma_3_1`); `jStar f` is at
   most the paper's bound for every `f ≠ 2` (`jStar_le_paperJ`) and `jStar 2 = 1` (`jStar_two`).
2. **Corollary 3.2's iteration bound is false for `f = 2` (false statement, same cause).** In a
   spec-level execution with `n = 7`, faulty nodes `1, 2`, in which all subroutine outputs meet
   Definitions 2.2, 2.5, 2.7, a correct node has not terminated after iteration `0`
   (`corollary_3_2_false`, `badTrace`): iteration 0 has a bad elector set, so electors' broadcast
   gives no agreement and the termination check is entitled to answer `term = 0`. With the
   concrete Algorithms 2 and 5 this is realizable (argued, not formalized): with mixed inputs and
   silent faulty nodes nobody is strong; the faulty electors `1, 2` make some receivers see a 2–2
   tie and others a 4–0 majority for the value `c` of the correct electors `3, 4`. Ties are broken
   "arbitrarily", so the opinions may split (also for a fixed rule that breaks ties against `c`),
   and then nobody passes the termination check. Corrected statement
   (`corollary_3_2`): termination by iteration `jStar f`. Theorem 1.1's `O(f + 1)` is unaffected
   (`theorem_1_1_rounds`).
3. **Algorithm 4 for `n ≤ 3` (false only in a degenerate case).** The loop runs for
   `j = 0 … ⌈log(n/6)⌉`, which is negative for `n ≤ 3` (`loopEnd_neg`); the loop body is never
   executed and Algorithm 4 never returns. In particular this happens for `t = 0` under the paper's
   own convention of running the protocol on `3t + 1` nodes (footnote 2). For `n ≥ 4` the loop is
   long enough (`jStar_le_loopEnd`). Fix: run at least iteration 0.

## Imprecisions, under-specified points, typos

4. **Algorithm 4, line 5: `max{ind + 3·2^j, n}` should be `min{…}` (typo).** With `max` the elector
   sets would extend to `n` or beyond. We use `min` (`K4`).
5. **Convention (3) ("terminated nodes are assumed to send `b` in all future rounds") is
   under-specified for subroutines whose messages are not bits** (Algorithms 5, 7 and the
   recursive consensus calls). For Algorithm 1 we implement it literally (receivers record
   termination broadcasts and substitute the recorded value, `eff`, `done`), and verify it. For
   Algorithm 4 (spec level) we let terminated nodes keep taking part in every call with their
   final value; the specifications of the three subroutines then apply to all correct nodes,
   which is what the paper's proof of Theorem 2.9 uses ("this applies even when a subset of the
   nodes in `V_g` already terminated"). For Algorithm 4 this is harmless because every iteration
   has a fixed length. For Algorithm 8 it is not: see the section on Section 4 below.
6. **Convention (4) (arbitrary choice when both values qualify).** Modelled by tie-breaking
   parameters (`pick` in `Alg2Inst`, `tb` in `alg1`, `pick` in `alg5Out`); all results hold for
   every choice, including choices depending on the round, node, state and receptions.
7. **Theorem 2.9: `t := ⌈n/3⌉ − 1` generalized.** We prove it for every `t` with `3t < n` and at most
   `t` faults (the algorithm's thresholds `n − t`, `t + 1` use this `t`); `⌈n/3⌉ − 1` is the largest
   such `t`. The kings of iterations `0 … t` must be distinct (paper: nodes `1 … t + 1`).
8. **Theorem 2.9's round count.** "Runs for at most `6(f+1)` rounds" is proved as: after `6(f + 1)`
   rounds every correct node has decided and halted (sends nothing afterwards); `f = |F|` is the
   actual number of faulty nodes. The message bound `6n²(f+1)` counts messages (pairs
   sender/receiver per round, including messages to oneself) sent by correct nodes; each is one
   bit (`Bool`).
9. **Theorem 1.1 is assembled from hypotheses on the cited Theorem 3.3.** The recursive Phase King
   protocol of [2] is not formalized. Its correctness is the hypothesis `ConsensusOn` of
   `lemma_3_4`, its running time `R k ≤ a k + b` and bit complexity `B k ≤ c k n` (`k ≤ n`) are
   hypotheses of `theorem_1_1_rounds` / `theorem_1_1_bits`. Round and bit counts of Algorithm 4 are
   computed from the fixed per-iteration costs (`roundsUntil`, `bitsUntil`: validator 2 rounds,
   Algorithm 5 `R(|K|) + 1` rounds, termination check 2 rounds, termination broadcast 1 round;
   ≤ 5n² bits for the broadcasts, `B(|K|) + |K| n` for electors' broadcast). Explicit constants:
   `(6 + b + 7a)(f + 1)` rounds and `5 n² (⌊log₂(f+1)⌋ + 1) + 7 (c + 1) n (f + 1)` bits. The paper
   states `O(n t log(f + 2))` bits; for `n ≤ 3` (`t = 0`) that is `0`, which is false literally
   (degenerate; the paper's footnote 2 assumes `n = 3t + 1`); our bound is in terms of `n²`.
   The paper's `Θ(·)` in the proof of Theorem 1.1 should be `O(·)` (no lower bound is shown).
10. **Lemma 3.4** is formalized for its correctness part (validity and electors' agreement from a
    consensus routine that is correct when fewer than a third of `K` is faulty). Its time and bit
    claims are the per-iteration costs of item 9. The proof's claim "strictly more than one half of
    the nodes in `K` are correct" follows from `|V_g ∩ K| > ⌊2|K|/3⌋` (`good_iff`), as used.
11. **Spec-level model for Algorithm 4.** Corollary 3.2 is about arbitrary implementations meeting
    Definitions 2.2, 2.5, 2.7, so we formalize it over `Trace`s: each call's outputs are arbitrary
    subject to its specification. The concrete Algorithm 2 / 3 / 5 instances satisfy these
    specifications (`Alg2Inst.spec`, `lemma_2_6`, `lemma_3_4`), but Algorithm 4 is not compiled into
    one round algorithm (that would need a concrete recursive Phase King protocol of [2]).
12. **Lemma 2.3 is proved in two halves** (`vote_of_all`, `alg2_out_of_all`) so that it also applies
    when some correct senders are terminated nodes substituted by convention (3) (needed in the
    concrete Algorithm 1).

## Section 4 (Algorithm 8, Theorem 1.2)

13. **Lemma 4.2 is false for Algorithm 7 as stated (false statement; formal counterexample).**
    `cx_fails`, `cx_not_electorsBC`, `cx_not_within_one` (`VotingBarrier.lean`): `n = 4`, `t = 1`,
    node `1` faulty (Lean node `0`), `K = V` (good: 3 > ⌊8/3⌋), the consensus thread correct
    (outputs `1` at all correct electors after 1, 2, 2 rounds, `cx_hyps`), all nodes start in the
    same round, nobody strong, inputs `1, 0, 0`. Rounds 0-based (as in Lean): round 1: elector `2` broadcasts `elect(1)`; the
    faulty node sends `elect(1)` to `2, 3` only, so `2, 3` vote `1` in round 2 while `4` (only one
    `elect`) does not yet. Round 2: the faulty node sends `vote(1)` to `4` only; `4` now has
    `n − t = 3` votes and **returns `1` without ever voting**. Nodes `2, 3` have two votes forever
    (`4` stopped, the faulty node is silent) and return their own inputs `1` and `0` at the timeout.
    Electors' agreement fails (outputs `1, 1, 0`) and the returns are 2+ rounds apart. The proof's
    step "any correct node satisfies the precondition for sending `vote(b)` by the end of round `r`
    and broadcasts `vote(b)` in round `r + 1`. It follows that each correct node received
    `vote(b)` from all at least `n − t` correct nodes" ignores nodes that returned in round `r`.
    **Repair** (`fix = true` in `alg7`): a node that returns still broadcasts its pending votes in
    the next round, then stops. With it every bullet of Lemma 4.2 holds (`lemma_4_2`: validity,
    electors' agreement, return within `max{T + 3, 4}` local rounds, returns within one global
    round of each other, ≤ 3 broadcasts per node; `good_ret`: with a good `K` and consensus
    outputs by local round `D ≤ T`, every correct node has returned by local round
    `max{D, 1} + 3`; `cx_repaired`).
14. **Use of Lemma 4.2 in Algorithm 8: terminated nodes (proof gap / under-specified).** In
    Algorithm 8 a correct node may return at line 7 or 16 while others continue (the termination
    check can split: `alg2_split_term`, `n = 7`, `t = 2`). The returned nodes do not run the later
    calls of Algorithm 7, and convention (3) does not say what they "send" there. Lemma 4.2's
    barrier argument needs all `n − f` correct nodes to take part: with two silent terminated
    correct nodes even the repaired Algorithm 7 lets one node return in round 1 and the others
    only at the timeout (`np_fails`, `n = 7`, `t = 2`, `K = {1, 3, 4}` with one faulty elector).
    Under the other reading (terminated nodes are deemed to send `vote(b)` in every round) the
    unrepaired algorithm also splits (`ph_fails`; the repaired one does not on that instance).
    Then the next compiled termination check starts with more than one round of skew, outside
    the precondition of Theorem 4.1. We did not formalize Algorithm 8, so we do not claim that
    Theorem 1.2 is false; but its proof does not cover these executions. A natural repair (not
    verified) is to let terminated nodes keep executing all remaining subroutine calls of the
    current instance without changing their output; this stays within the worst-case round and
    bit bounds, since such nodes only send what a non-terminated correct node may send.
15. **Algorithm 7, line 9: "elect(b) from at least `t + 1` nodes in `V`" should be "vote(b)"
    (typo).** The surrounding text and the proof use `t + 1` votes. Formalized with `vote(b)`.
16. **Lemma 4.2's proof: "Nodes with `strong_i = 0` maintain their opinion" should be
    `strong_i = 1` (typo).**
17. **"Each correct node broadcasts at most twice" (proof of Lemma 4.2) is wrong (minor slip).** An
    elector can broadcast `elect`, `vote(0)` and `vote(1)` in three different rounds when `K` is bad
    (`three_bcasts`); at most three (`lemma_4_2`). Asymptotically irrelevant.
18. **Theorem 4.1 is correct as stated** (`theorem_4_1`, `Synchronizer.lean`), including the
    paper's slot arithmetic. Modelling: the compiled node runs forever and outputs `A`'s decision
    on the simulated state (the paper's "return"); the theorem gives a synchronous execution `E`
    of `A` (CSLib `RoundRun`, `SyncFrom 0`) with `(state at local round 2r+1).s = E.s r`,
    corresponding decisions, and the message correspondence (A's message plus a tag bit).
19. **Desynchronized model** (`Desync.lean`, `DRun`): global lock-step rounds; node `p` performs
    local round `ℓ` in global round `σ p + ℓ`; messages between correct nodes arrive in the round
    they are sent (lost if the receiver has not started); correct nodes start within one round
    (`StartWithin1`). The consensus thread of Algorithm 7 is abstracted as part of the input
    (`cons i = some (τ, c)`; it uses separate messages), with correctness hypothesis
    `ConsCorrect` (only for electors' agreement and the early-stopping time bound).
20. **Theorem 1.2 is not formalized end to end.** Formalized pieces: Theorem 4.1, Lemma 4.2 (with
    the repair), Lemma 4.3 (`lemma_4_3`), and the arithmetic of the time recurrence of Lemma 4.5
    (`lemma_4_5_time`, explicit constant `C = c₀ + 3 + 2c₁`), whose case bounds are hypotheses.
    Not formalized: the composition of compiled code, Algorithm 7 and recursion into Algorithm 8,
    Corollary 4.4, and the bit recurrence of Lemma 4.5 (which uses
    `log(ℓ+2)/log(ℓ+1) < 1.6` for `ℓ ≥ 1`, true: `log 3/log 2 ≈ 1.585`).
21. **Lemma 4.5's proof, minor imprecisions.** The induction hypothesis is stated as
    `B(n, ℓ) ≤ C n t log(ℓ + 1)` but the proof bounds `C n² log(ℓ + 1)` (and the `n t` form is false
    for `n ∈ {2, 3}`, where `t = 0` but messages are sent). In case (3) the step
    `T(|V₀|, ⌈|V₀|/3⌉ − 1) ≤ T(|V₀|, f₀ − 1)` uses `T` outside its domain `f < n/3` when
    `f₀ − 1 ≥ |V₀|/3`; the intended bound `T(|V₀|, ⌈|V₀|/3⌉ − 1) ≤ C⌈|V₀|/3⌉ ≤ C f₀` holds
    directly (used in `lemma_4_5_time`). "`|V₀| ≤ n/2 ≤ 2^{k+1}`" should be `< 2^{k+1}`. The loop
    length of Algorithm 7 must be a known number; the induction shows that `C⌈k/3⌉` can be used.
