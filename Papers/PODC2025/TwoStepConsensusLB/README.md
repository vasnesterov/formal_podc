# Revisiting Lower Bounds for Two-Step Consensus — PODC 2025

Fedor Ryabinin, Alexey Gotsman, Pierre Sutra. *Brief Announcement: Revisiting Lower Bounds for Two-Step
Consensus.* PODC 2025, pp. 58–61. DOI [10.1145/3732772.3733541](https://doi.org/10.1145/3732772.3733541).
Formalized version: arXiv [2505.03627](https://arxiv.org/abs/2505.03627) v2 (full version with appendices
A–C; numbering follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** Both headline theorems hold, and we prove them as "iff" statements in one
model. Theorem 1: an `f`-resilient `e`-two-step consensus task exists iff `n ≥ max {2e+f, 2f+1}`. Theorem 2: an
`f`-resilient `e`-two-step consensus object exists iff `n ≥ max {2e+f−1, 2f+1}`. Both need `n ≥ 2`,
`e ≤ f` and two values. The upper bound for objects, however, does not follow from the paper's protocol: the
object version of Fig. 1 is not wait-free. We prove Theorem 2 with a repaired protocol. Several proofs (Lemma 4,
Lemma 5, §B.2) have gaps, all of which we repaired.

## Mistakes in the paper

* **The object protocol (Fig. 1 with the red lines, §C.3) is not wait-free, so Theorem 2 "if" is not
  established by the paper.** The 1B messages do not carry `initial_val`, and a leader at line 37 can only
  propose its *own* `initial_val`. A value known only to a non-leader is therefore never proposed. Two concrete
  executions show this.
  - *Ω scenario, any admissible parameters.* No process crashes, and Ω permanently outputs a correct `l` that
    never calls `propose`. Every process moves to ballot 1 before anybody invokes (the ballot timer runs from
    startup: "Initially it is set to 2Δ", §C.1). Later a correct `r ≠ l`
    invokes `propose(v)`. Its `Propose` is ignored (`bal ≠ 0`), so `l` computes `val = ⊥` in every ballot and
    never sends a 2A, and `r` never returns. (`Fig1.object_not_wait_free_omega`)
  - *Crash scenario, any leader election, whenever `n − f − e ≥ 2`* (e.g. `n = 7, f = 3, e = 2`, which meets
    the paper's bound). `p` proposes `v`, only `r` accepts it, and `p` crashes. Everyone else moves to a slow
    ballot. `r` invokes `propose(w)` later; line 3 is skipped because `r` has already voted. Each 1B quorum
    shows at most one vote for `v`, which is below `n − f − e`, and no leader has an `initial_val`, so nobody
    ever decides. (`Fig1.object_not_wait_free`)

  Severity: the upper-bound proof is broken, but Theorem 2 itself is true. We fix lines 37–38 in the object
  version ("else, if `initial_val = ⊥`, propose the leader's own `val`"). We also replace Ω by clock-driven
  rotating ballots, so every correct invoker eventually leads a ballot after GST. The fix alone does not save
  the Ω version: the first scenario still applies. We prove the fixed protocol correct and two-step for
  `n ≥ max {2e+f−1, 2f+1}`. (`Impl.theorem_2_upper`, `theorem_2`)
* **Lemma 5 (object fast-path recovery): proof gap; the statement is true.** The proof considers the line-33
  case only when `v` itself has `> n−e−f` votes in `Q`. With `n = 2e+f−1` it can also happen that `v` has
  exactly `n−e−f = e−1` votes and another `w` has `e` votes; counting does not exclude this. The case is ruled
  out by the line-35 argument: all `f` processes outside `Q` voted for `v`, so `w`'s proposer did as well, and
  in the object version it then never proposed `w`. In the task version (Lemma 1) the same case is excluded by
  counting, and the paper skips it silently. (`Fig1.lemma5`, `Fig1.lemma1`)
* **Lemma 4 (slow-path safety): the proof does not work; the statement is true.** The induction on `b′`
  analyses line 30 by claiming that a process with `vbal_q′ = b` received its `Decide` from the leader of
  ballot `b`. That is false: `Decide` may come from a decision at a higher ballot, received before answering
  `1A(b′)`, and `decided_q′` need not be the value of `2A(vbal_q′)`. Agreement between two fast-path decisions
  is never argued either. We prove agreement through a "potentially chosen" invariant over all fast and slow
  decisions. (`Fig1.lemma4`, `Fig1.task_agreement`, `Fig1.object_agreement`)
* **Lower-bound proofs (§B): gaps; statements true.**
  - The proofs assume `n = 2e+f−1` (Thm 1) and `n = 2e+f−2` (Thm 2) without reducing smaller `n` to these
    cases.
  - Lemma 2 is stated without proof.
  - "All correct processes propose 0, thus 0 is decided" needs Lemma 2 first, because the crashed processes
    propose 1.
  - In §B.2 the correct processes never call `propose`, so wait-freedom forces no decision in the
    continuation. Moreover, the "w.l.o.g. 1 is decided" ignores a third proposed value.

  We prove both bounds for every `n ≥ 2`, using one generic merge lemma for all the indistinguishability
  arguments. (`theorem_1_lower`, `theorem_2_lower`, `merge_task`, `merge_object`)
* **Degenerate cases (outside the paper's assumption `n ≥ 3`; not an error).** The lower bounds fail for `n = 1`: deciding one's own input is `1`-resilient and
  `0`-two-step (`theorem_1_fails_n_one`). The paper assumes `n ≥ 3`. The fast path of Fig. 1 is vacuous when
  `n − e ≤ 1`; this only matters for `n ≤ 2`, where `f = 0`.
* **Typos and slips.**
  - §B.1, base case: `E₀′` should be `E₀`.
  - §B.2: `decide(p, 1)` in `σ′` should be `decide(p, 0)`, and "`F ∪ {p,q} = f`" should be a cardinality.
  - Brief announcement, lines 33 and 35: `Q_f` should be `S`.
  - Introduction: "EPaxos uses `2f+1 = 2e+f−1` processes, Lamport requires `2f+3`" holds only for even `f`.
    For odd `f`, EPaxos's `2f+1` equals `2e+f`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (our own; now in CSLib as `Cslib.CrashPartialSync`, `Cslib/Computability/Distributed/CrashPartialSync/`;
`Model.lean` here keeps Definitions 3–5).
- `n` deterministic crash-prone processes and point-to-point links, in the Dwork–Lynch–Stockmeyer partially
  synchronous model. Discrete time with one tick `= Δ`; GST is unknown.
- At each tick an alive process takes one atomic step. The step receives the messages delivered now, in an
  **adversary-chosen order**, together with an optional invocation (the task input at time 0, or an object
  `propose`). Processes see the clock.
- Links are reliable and timely after GST between correct processes; messages from or to faulty processes may
  be lost. The paper's proofs need this too.
- `E`-faulty synchronous runs (Def. 2), "two-step" (Def. 3: decided in the state after the step at time 2),
  `e`-two-step task and object (Defs. 4, 5) are stated literally, quantifying over the delivery order.
- Task: validity, uniform agreement, termination. Object: agreement of responses, "returned value was proposed
  before", wait-freedom.
- Clocks and the restricted step granularity only strengthen the lower bounds. The upper bound holds in this
  model; with rotating clock-driven ballots instead of Ω, no synchronizer argument is needed.

**Main results in Lean** (namespace `TwoStepConsensus`).

| Paper | Lean | File |
|---|---|---|
| **Theorem 1** (iff) | `theorem_1` | `ImplAgreement.lean` |
| **Theorem 2** (iff) | `theorem_2` | `ImplAgreement.lean` |
| Thm 1 "only if" (§B.1), Lemma 3 | `theorem_1_lower`, `lemma_3` | `LowerBound.lean` |
| Thm 2 "only if" (§B.2), only Def. 5 (1) used | `theorem_2_lower`, `theorem_2_lower_of_item1` | `LowerBound.lean` |
| `n ≥ 2f+1` [DLS] | `two_f_lt_task`, `two_f_lt_object` | `Basic.lean` |
| Lemma 2 | `syncRun_st_eq` | `Basic.lean` |
| merging two-round prefixes (all §B contradictions) | `mergeRun_st_symm`, `merge_task`, `merge_object` | `Merge.lean` |
| Fig. 1 as an abstract transition system | `Fig1.Step`, `Fig1.Reachable` | `Fig1Protocol.lean` |
| Lemma 1, Lemma 5, Lemma 4 | `Fig1.lemma1`, `Fig1.lemma5`, `Fig1.lemma4` | `Fig1Safety.lean` |
| Agreement / validity of Fig. 1 (§C.2, §C.3) | `Fig1.task_agreement`, `Fig1.object_agreement`, `Fig1.agreement_msgs` | `Fig1Safety.lean` |
| Object protocol not wait-free | `Fig1.object_not_wait_free`, `Fig1.object_not_wait_free_omega` | `Fig1Liveness.lean` |
| Fig. 1 in the model (rotating ballots, object fix) | `Impl.fig1` | `Impl.lean` |
| §3 two-step argument, Defs. 4/5 | `Impl.task_twoStep`, `Impl.object_twoStep` | `ImplTwoStep.lean` |
| Termination / wait-freedom (§C.1) | `Impl.task_termination`, `Impl.object_waitFree` | `ImplTermination.lean` |
| Refinement to the abstract system | `Impl.absState_reachable`, `Impl.task_agreement'`, `Impl.object_agreement'` | `ImplAgreement.lean` |
| Thm 1 / Thm 2 "if" | `Impl.theorem_1_upper`, `Impl.theorem_2_upper` | `ImplAgreement.lean` |
| `n = 1` counterexample | `theorem_1_fails_n_one` | `SmallCases.lean` |

**Not formalized.**
- The Ω leader-election service of §C.1 is replaced by rotating ballots.
- The comparison with Lamport's definition and Fast Paxos, and the EPaxos discussion, are not formalized.

**Trust.** There is no `sorry`. `theorem_1`, `theorem_2` and the theorems listed above use only `propext`,
`Classical.choice` and `Quot.sound`. Non-vacuity: `theorem_1`/`theorem_2` exhibit protocols satisfying the
hypotheses of the lower bounds whenever the bounds allow it, and `theorem_1_fails_n_one` is a degenerate
instance. The generic run facts (`Run.mem_inbox`, `Run.invariant`, `Run.st_mono`) are shared code in CSLib
(`Cslib/Computability/Distributed/CrashPartialSync/Model.lean`).
