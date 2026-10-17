# Recursive Early-Stopping Phase King — PODC 2022

Christoph Lenzen, Sahar Sheikholeslami. *A Recursive Early-Stopping Phase King Protocol.* PODC 2022.
DOI [10.1145/3519270.3538425](https://doi.org/10.1145/3519270.3538425). Formalized version: the
proceedings version (no arXiv version exists). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** **Lemma 4.2 is false**: the voting barrier (Algorithm 7) can violate
electors' agreement and "termination within one round of each other", even with a good elector set
and a correct consensus routine. A one-line repair makes all of Lemma 4.2 true. So Theorem 1.2
(the `O(n²)`-bit recursive algorithm) is not established by the paper, though it is very likely
true after repairs. Theorem 1.1 and Theorem 2.9 (`6(f+1)` rounds) are correct. Lemma 3.1 and
Corollary 3.2 are off by one iteration for `f = 2`; this does not affect `O(f+1)`.

## Mistakes in the paper

- **Lemma 4.2 is false (false statement).** Take `n = 4`, `t = 1`, node 1 faulty, `K = V`, and
  a consensus thread that is correct (all correct electors output `1`, after 1, 2 and 2 rounds).
  All nodes start together, nobody is strong, and the inputs are `1, 0, 0`. Rounds are counted from 0
  (round 0 is the first round of Algorithm 7; an elector whose consensus run took `τ ≥ 1` rounds sends
  `elect` in round `τ`).
  - Round 1: elector 2 sends `elect(1)`. The faulty node sends `elect(1)` only to nodes 2 and 3,
    so nodes 2 and 3 vote `1` in round 2. Node 4 has one `elect` and does not vote yet.
  - Round 2: the faulty node sends `vote(1)` only to node 4. Node 4 now has `n − t = 3` votes and
    returns `1` without ever having voted.
  - Nodes 2 and 3 are stuck at two votes and return their own inputs `1` and `0` at the timeout.

  Electors' agreement fails, and the returns are two rounds apart. The proof assumes that once
  `t + 1` correct votes exist, every correct node votes in the next round. That fails for a node
  that has already returned.
  - **Repair:** a returning node still broadcasts its pending votes for one more round.
  - **Proved:** with the repair, all bullets of Lemma 4.2 (`cx_fails`, `cx_not_electorsBC`,
    `cx_not_within_one`; repaired: `lemma_4_2`, `good_ret`).
- **Algorithm 8 does not account for correct nodes that have already terminated (proof gap).**
  A termination check can let some correct nodes return while others continue (`alg2_split_term`).
  - **Why it matters:** the returned nodes no longer run the later calls of Algorithm 7, and
    convention (3) ("assume that `i` sends `b`") is not defined for `elect`/`vote` messages. The
    barrier argument needs all `n − f` correct nodes.
  - **Counterexamples (Algorithm 7 level):** with two silent terminated nodes (`n = 7`, `t = 2`),
    even the repaired Algorithm 7 lets one node return in round 1 and the others at the timeout
    (`np_fails`). The "phantom voter" reading of convention (3) fails similarly for the unrepaired
    algorithm (`ph_fails`).
  - **Consequence:** the next compiled step starts with more than one round of skew, outside the
    precondition of Theorem 4.1. We did not formalize Algorithm 8 end to end, so we do not claim
    Theorem 1.2 is false.
- **Lemma 3.1 and Corollary 3.2 are false for `f = 2` (false statement, harmless).**
  - **Claim:** some iteration `j ≤ ⌈log(max{f/2, 1})⌉` has fewer than a third faulty electors.
  - **Counterexample:** for `f = 2` the bound is `j = 0`, but the first elector set
    `{1, 2, 3, 4}` can contain both faults (`n = 7`). The proof's final inequality equals `2 > 2`
    exactly at `f = 2`. A spec-level execution where no node terminates in iteration 0 refutes the
    corollary.
  - **Proved instead:** termination by iteration `jStar f` (least `J` with `2^{J+1} + J > f`).
    This is at most the paper's bound, except for `f = 2`, where it is `1` (paper: `0`) (`lemma_3_1_false`,
    `corollary_3_2_false`; corrected: `lemma_3_1`, `corollary_3_2`, `jStar_le_paperJ`).
- **Algorithm 4 never returns for `n ≤ 3` (false only in a degenerate case).** The loop
  `for j = 0 to ⌈log(n/6)⌉` is empty there, including for `t = 0` under the paper's own
  "run on `3t + 1` nodes" convention (`loopEnd_neg`). For `n ≥ 4` the loop is long enough
  (`jStar_le_loopEnd`).
- **Minor.**
  - Typos:
    - Algorithm 4 line 5 has `max` for `min`.
    - Algorithm 7 line 9 has "`elect(b)` from `t + 1` nodes" for `vote(b)`.
    - The proof of Lemma 4.2 has `strong_i = 0` for `strong_i = 1`.
  - "Each correct node broadcasts at most twice" should be three times (`three_bcasts`).
  - Lemma 4.5's induction states `B ≤ C n t log(ℓ+1)` but proves `C n² log(ℓ+1)`; the `nt` form
    fails for `n ∈ {2, 3}`. Its case (3) applies `T` outside its domain.
  - The `O(n t log(f+2))` bit bound of Theorem 1.1 is literally `0` for `t = 0`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Setting.** Deterministic, synchronous, full mesh, authenticated channels, static Byzantine
  faults: at most `t` faulty nodes with `3t < n` (the paper's `t = ⌈n/3⌉ − 1` is the largest such
  `t`). `f = |F|` is the actual number of faults. Binary inputs.
- **Algorithm 1 (Theorem 2.9).** One CSLib `RoundAlgorithm` (Algorithms 2 and 3 inlined), verified
  against every synchronous `RoundRun` (`SyncFrom 0`, faulty messages arbitrary).
  - Convention (3) is implemented literally: receivers record termination broadcasts and
    substitute the recorded value.
  - Arbitrary choices are tie-breaking parameters; results hold for all of them.
  - Kings of iterations `0…t` are distinct.
- **Algorithm 4 (Corollary 3.2, Theorem 1.1).** Spec-level executions (`Trace`): each call's
  outputs are arbitrary subject to Definitions 2.2/2.5/2.7, as Corollary 3.2 is stated.
  - Terminated nodes keep taking part with their final value (convention (3)).
  - The cited recursive Phase King of [2] (Theorem 3.3) is not implemented. Its correctness and
    its bounds `R(k) ≤ ak + b` rounds and `B(k) ≤ ckn` bits are hypotheses. The concrete
    Algorithms 2, 3, 5 are proved to meet the specifications.
- **Section 4.** Desynchronized lock-step model `DRun`: node `p` runs local round `ℓ` in global
  round `σ p + ℓ`, and correct start rounds differ by at most one.
  - Algorithm 6 is a compiler on CSLib round algorithms.
  - Algorithm 7's consensus thread (separate messages) enters as an input `(τ, c)`, with a
    correctness hypothesis.

**Main results in Lean** (namespace `RecursivePhaseKing`).

| Paper | Lean | File |
|---|---|---|
| Defs 2.2, 2.5, 2.7 | `WeakValidatorSpec`, `ElectorsBCSpec`, `WeakAgreement` | `Subroutines.lean` |
| Lemmas 2.3, 2.4, Cor 2.8 (Algorithm 2) | `Alg2Inst.lemma_2_3`, `lemma_2_4`, `spec`, `corollary_2_8` | `Subroutines.lean` |
| Lemma 2.6 (Algorithm 3) | `lemma_2_6` | `Subroutines.lean` |
| Lemma 3.4, correctness (Algorithm 5) | `lemma_3_4` | `Subroutines.lean` |
| Theorem 2.9 (Algorithm 1): validity, agreement, `6(f+1)` rounds, `6n²(f+1)` one-bit messages | `theorem_2_9_validity`, `theorem_2_9_agreement`, `theorem_2_9_termination`, `theorem_2_9_messages` | `EarlyStopping.lean` |
| Lemma 3.1 (false at `f = 2`; corrected) | `lemma_3_1_false`; `lemma_3_1`, `jStar_le_paperJ`, `jStar_two` | `Doubling.lean` |
| Corollary 3.2 (false at `f = 2`; corrected) | `corollary_3_2_false`; `corollary_3_2`, `Trace.validity`, `Trace.agreement` | `Doubling.lean` |
| Algorithm 4 loop range | `jStar_le_loopEnd` (`n ≥ 4`), `loopEnd_neg` (`n ≤ 3`) | `Doubling.lean` |
| Theorem 1.1: `(6 + b + 7a)(f+1)` rounds; `5n²(log₂(f+1)+1) + 7(c+1)n(f+1)` bits | `theorem_1_1_rounds`, `theorem_1_1_bits` | `Doubling.lean` |
| Theorem 4.1 (Algorithm 6) | `theorem_4_1` | `Synchronizer.lean` |
| Lemma 4.2 (false; repaired) | `cx_fails`, `cx_not_electorsBC`, `cx_not_within_one`; `lemma_4_2`, `good_ret`, `three_bcasts` | `VotingBarrier.lean` |
| Gap in Algorithm 8 | `alg2_split_term`, `np_fails`, `ph_fails` | `Recursive.lean`, `VotingBarrier.lean` |
| Lemma 4.3 | `lemma_4_3` | `Recursive.lean` |
| Lemma 4.5, time recurrence (`C = c₀ + 3 + 2c₁`) | `lemma_4_5_time` | `Recursive.lean` |

**Not formalized.**
- Algorithm 8 end to end: Corollary 4.4, Theorem 1.2 and the bit recurrence of Lemma 4.5.
  Their pieces are above, and the paper's proof has the gaps listed.
- The cited recursive Phase King protocol of [2].

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`.
- **Non-vacuity:** `NonVacuity.lean` builds an execution of Algorithm 1 for every adversary
  (`syncRun`) and the paper's king schedule (`kingFin_injOn`). It also computes a 4-node run that
  decides in 6 rounds (`example_decides`).
- The counterexamples satisfy all hypotheses (`cx_hyps`), and `badTrace` inhabits `Trace`.
- The models are CSLib's `RoundAlgorithm`/`RoundRun` (`Cslib/Computability/Distributed/Byzantine/PartialSync/Rounds.lean`)
  and `Desync.lean`.

**Shared infrastructure.** `WeakValidatorSpec` (Definitions 2.2, 2.7) is binary graded consensus
`Cslib.Byzantine.Problem.GradedConsensus` and `ConsensusOn` uses `Cslib.Byzantine.Problem.Consensus`
(`Cslib/Computability/Distributed/Byzantine/Specs.lean`; unfolded forms `weakValidatorSpec_iff`, `consensusOn_iff`). Lemma 2.6
is the generic phase-king pair `kingPhase_agreement`/`kingPhase_persistence`
(`Cslib/Computability/Distributed/Byzantine/KingPhase.lean`). Vote counts `cntIn`, `cnt` are `Finset.countEq`
(`Cslib/Foundations/Data/Finset/Quorum.lean`).
