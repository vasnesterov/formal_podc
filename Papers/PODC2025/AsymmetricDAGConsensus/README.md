# DAG-based Consensus with Asymmetric Trust — PODC 2025

Ignacio Amores-Sesar, Christian Cachin, Juan Villacis, Luca Zanolini. *DAG-based Consensus with Asymmetric
Trust.* PODC 2025. DOI [10.1145/3732772.3733527](https://doi.org/10.1145/3732772.3733527). Formalized
version: arXiv [2505.17891](https://arxiv.org/abs/2505.17891) v1 (extended version); numbering follows it.

**Verdict: ❌ False claim.** The gather part of the paper holds. Lemma 3.2 is true: the 30-process
system of Figure 1 satisfies `B³` and makes the quorum-replacement gather (Algorithm 2) miss a common
core. The new constant-round asymmetric gather (Algorithm 3) is correct: Lemmas 3.3–3.8 hold, but the
proofs of Lemmas 3.5 and 3.7 need a repair. The claim in Appendix A that the quorum-replacement
pattern reaches a common core within `log n − 1` rounds is false. The DAG consensus protocol of
Section 4 is not formalized.

## Mistakes in the paper

* **The "`log n − 1` rounds" claim is false (Appendix A; also "would require `log n` rounds",
  §3).** Appendix A says that, by quorum consistency, the common core "can be obtained in
  `log n − 1` rounds" of receiving messages from a quorum and sending them on. For `n = 8` that is
  `log₂ 8 − 1 = 2` rounds. Counterexample: 8 processes with single quorums `{1,2,4}`, `{3,4,5}`,
  `{1,4,5}`, `{1,5}`, `{1,3,4}`, plus three processes that copy the first quorum. The quorums
  pairwise intersect, so the canonical fail-prone system satisfies `B³`. All processes are correct
  and each one hears exactly its own quorum. After 2 rounds no quorum lies inside every output.
  After 3 rounds a common core does exist. The first five processes alone already defeat 2 rounds
  (5 < 2³), so the §3.2 heuristic "3 rounds suffice below 16 = 2⁴ processes" does not carry over to
  2 rounds. Rounds are counted as the paper counts them: "the 3 rounds of Algorithm 2", which waits
  for a quorum three times. With the floor reading, `⌊log₂ 30⌋ − 1 = 3`, the claim is refuted by
  the paper's own Figure 1. This is an unproved side remark, not a headline result.
  (`log_rounds_claim_false`, `two_rounds_five_processes`)
* **Lemmas 3.5 and 3.7: two proof gaps, statements true.**
  (i) Lemma 3.5 goes "all quorums contain a wise process (Lemma 7 of Alpos et al.), so a wise
  process sent `CONFIRM`; apply Lemma 3.4". But Lemma 3.4 needs a *maximal-guild* member, and a
  wise process need not be one. Fix: a quorum `Q` of a guild member `g` meets `g`'s quorum inside
  the guild, so `Q` contains a guild member. (ii) Lemma 3.7 picks a process in `Qᵢ ∩ Qⱼ` and uses
  that it put `Sᵢ` into its `T`. That process may be Byzantine. Both `pᵢ` and `pⱼ` are wise, though,
  so consistency against the actual faulty set gives a *correct* process in the intersection. In
  the same way, Lemma 3.5's "the processes of `Qᵢ` receive `DISTRIBUTES` before sending
  `DISTRIBUTET`" only makes sense for the correct members of `Qᵢ`. We prove that version.
  (`lemma_3_5`, `lemma_3_7`, `exists_candidate`)
* **Definition 3.1 has no termination property.** A protocol that never ag-delivers satisfies
  Definition 3.1 as written. Lemma 3.8 and the text clearly intend that every maximal-guild member
  ag-delivers, and Algorithm 3 does. We prove termination too. (`termination`, `lemma_3_8`)
* **Small slips.**
  - Appendix A's "easy way to observe" no common core is a non sequitur. "Every `S` set has an
    element in `[16,30]`" plus "every `U` misses some element of `[16,30]`" does not imply that no
    `S` lies in all `U`s. The conclusion is still true (`fig1_no_core`).
  - §3.2 says "3 rounds, fewer than 16 processes", then "`n` rounds, fewer than `2ⁿ`
    processes". These two statements do not match: `2³ = 8`.
  - §3.2 says Algorithm 2 gives a common core "after four rounds". Elsewhere it speaks of three
    rounds; "four" presumably also counts the input broadcast, as DAG-Rider's 4-round waves do.
    With that count the "`log n − 1`" claim is off by even more.
  - Line 62 ("upon receiving `DISTRIBUTET` from a quorum, ag-deliver `U`") should count only
    `DISTRIBUTET` messages already incorporated by line 60, that is, those with `T ⊆ Sᵢ`. If not,
    `U` may lack the core. We model the intended reading.
  - §2.4: "`2f − 1` processes" should be `2f + 1`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing in CSLib-style `Cslib.Byzantine.AsyncBroadcast` (staged in `Podc/`).
  Interleaving semantics, authenticated channels, Byzantine faults with *adaptive* corruption (stronger
  than the paper's static faulty set `F`). The faulty set of an execution is the set of processes
  corrupted at some time, and wise processes and guilds are defined relative to it. No randomness.
* Asymmetric trust (new, `Podc/Computability/Distributed/AsymmetricQuorum.lean`): fail-prone systems
  `F i`, `B³`, asymmetric quorum systems (consistency + availability), kernels (all sets meeting
  every quorum of `i`), wise processes, guilds, the maximal guild.
* The asymmetric reliable broadcast of the inputs is a `val` message. For Byzantine senders its
  consistency and totality towards the guild are hypotheses on the execution (`RBC`). These are
  exactly the guarantees of the primitive of Alpos et al. that the paper uses. Validity and
  integrity for correct senders follow from the model.
* Algorithms 2 and 3 are given by their handler guards. Liberal choices (e.g. which received `T`
  sets go into `U`) only add behaviours, so the safety results transfer. Liveness uses weak
  fairness: messages between correct processes are delivered, and a correct process whose guard
  for a message holds forever sends it.
* Lemma 3.2 and the round claims: an explicit fault-free run of the `r`-round quorum-replacement
  gather (`r = 3` is Algorithm 2) is reachable, with all processes ag-delivering. All
  processes form the maximal guild. Every possible core `S` (a set with a pair for each member of
  a quorum) misses some output. In a fault-free run every arb-delivery order can happen, so these
  runs are genuine.
* Algorithm 3: results hold for every nonempty guild `G` with `RBC` for `G`, in particular for the
  maximal guild (as in the paper).

**Main results in Lean.** (namespace `Podc.AsymmetricDAGConsensus`)

| Paper | Lean | File |
|---|---|---|
| Lemma 3.2 (Fig. 1: `B³`, quorum system, Alg. 2 has no common core) | `lemma_3_2` | `Counterexamples.lean` |
| Appendix A "`log n − 1` rounds" — false | `log_rounds_claim_false` | `Counterexamples.lean` |
| 2 rounds fail already for 5 processes | `two_rounds_five_processes` | `Counterexamples.lean` |
| Lemma 3.3 | `Gather3.lemma_3_3` | `Gather3Liveness.lean` |
| Lemma 3.4 | `Gather3.lemma_3_4` | `Gather3.lean` |
| Lemma 3.5 (correct members of the quorum) | `Gather3.lemma_3_5` | `Gather3.lean` |
| Lemma 3.6 | `Gather3.lemma_3_6` | `Gather3Liveness.lean` |
| Lemma 3.7 (common core) | `Gather3.lemma_3_7` | `Gather3.lean` |
| Termination (implicit in Lemma 3.7/3.8) | `Gather3.termination` | `Gather3Liveness.lean` |
| Lemma 3.8 (Alg. 3 is an asymmetric gather) | `Gather3.lemma_3_8`, `Gather3.lemma_3_8_maxGuild` | `Gather3Liveness.lean`, `NonVacuity.lean` |

**Not formalized.** Section 4 (asymmetric DAG-Rider, Lemmas 4.2–4.10). Remarks from reading it, not
checked in Lean: line 148 of Algorithm 6 commits with "a quorum `Q ∈ Qⱼ` for some `Qⱼ ∈ ℚ`", a
quorum of *any* process. The text says a quorum of `pᵢ`, and Lemma 4.2's intersection argument needs
that. Lemma 4.3 writes `strong_path(u, v)` from round 1 to round 4, so the direction is reversed.
Lemma 4.4 needs the coin to be independent of the common core; the binding issue raised in §2.4 is
not addressed for the asymmetric protocol. Also not formalized: the §3.2 claim that Algorithm 2 always
reaches a common core with fewer than 16 processes. We neither proved nor refuted it. Exhaustive SAT
search found no single-quorum fault-free counterexample with `n ≤ 7`. Heuristic local search found
none up to 15, but it is weak evidence: the same search did not rediscover a 30-process example either.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Concrete checks use `decide`/`decide +kernel` (no `native_decide`). Figure 1 was
extracted from the paper's listing and cross-checked pixel by pixel against the figure. Non-vacuity:
`alg3_fig1` gives a fair execution of Algorithm 3 on the Figure 1 system that satisfies all
hypotheses of Lemma 3.8, so `alg3_fig1_commonCore` shows that Algorithm 3 reaches a common core
where Algorithm 2 does not. `rbc_of_bad_empty`: the `RBC` hypotheses hold without corruptions.
Models: `Podc.Computability.Distributed.Byzantine.AsyncBroadcast` and
`Podc.Computability.Distributed.AsymmetricQuorum`.

**CSLib candidates.** `Podc/Computability/Distributed/AsymmetricQuorum.lean` (whole file). In
`RoundGather.lean`, the `AsyncBroadcast` batch lemmas `reach_deliver_set`, `reach_send_finset`,
`reach_decide_finset`. In `Gather3.lean`, `step_sent_new` and `exec_sent_succ`. In
`Gather3Liveness.lean`, `eventually_const_of_mono`.
