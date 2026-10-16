# Differences between the formalization and the paper

Paper: arXiv 1803.05069v6 (PODC 2019 full version). Classification per item:
**false statement**, **proof gap (true statement)**, **under-specified**, **typo**, or
**modelling choice**.

## Chained HotStuff (Algorithm 3, Theorem 5, Appendix A)

1. **False statement — Theorem 5 for Algorithm 3 as written (lock downgrade).** Lines 17–22 are
   executed whether or not `safeNode(b*, b*.justify)` holds, and Line 20 overwrites `lockedQC`
   unconditionally. A Byzantine leader therefore lowers the lock of correct replicas with a proposal
   that is never voted for. Explicit execution (`n = 4`, `f = 1`, Byzantine `3` leads every view;
   the paper states that `leader` does not affect safety):
   - `y` (view 1), then `w ← w' ← w'' ← w*` (views 2–5), which commits `w`;
   - `x` with parent `y` and justify `QC(y)` (view 6), which resets the lock to genesis;
   - `u ← u' ← u''` extending `y` (views 7–9), which commits `y`.

   Lean: `Chained/Counterexample.lean`, `theorem5_false`. The same attack works with round-robin
   leaders and a synchronous execution.
   - Byzantine replica `2` leads views 2, 6 and 10; correct leaders use `createLeaf`, so their
     proposals have height equal to view.
   - The only height violation is `x` in view 6.
   - Correct replica `0` commits `w` (view 5) and the conflicting `u` (view 10).

   Lean: `theorem5_false_roundRobin`. It checks the height property of all correct leaders'
   proposals; that their justify is the QC they formed is argued in the docstrings, not modelled.
2. **False statement — also with a monotone lock (as in Algorithm 4), without a height check.**
   Replicas never check `b*.height = curView`, so Byzantine leaders decouple QC views from node
   heights. The commit rule uses parent links (heights) while `safeNode` compares QC views.
   Execution: `w` (view 1), a conflicting `c` (view 3, replicas 0, 1), `w' , w''` (views 5, 6),
   replica 2 commits `w` (view 7), replicas 0, 1 accept `d` extending `c` by the liveness rule
   (`3 > 1`, view 8) and commit `c` (view 10). Lean: `monoLock_unsafe`. Every proposal in this
   execution passes `safeNode`. So it also refutes the reading in which Lines 17–22 run only after
   a successful `safeNode`.
3. **Repair (modelling choice).** Variant `heightCheck`: a replica processes `b*` only if
   `b*.height = curView`, `b*.justify` is valid (tverify, implicit in the paper) and `b*.justify.node`
   is a strict ancestor of `b*` (the paper says it "assumes the constraint always holds and omits
   checking in the code"). Then Theorem 5 holds for all `n > 3f`, `|F| ≤ f` (`theorem5_fixed`).
   With the height check, the literal lock update is automatically monotone.
4. **Proof gap.** Appendix A says "the lock that `r` has on `w` is not changed before `qc_s` is
   formed". This fails for Algorithm 3 as written (item 1). Even with the height check, the step
   "by minimality of `qc_s`, `m.node.justify.viewNumber ≤ v_{w''}`" is unjustified: the justification
   may have a higher view and extend `w`, which also gives the contradiction. Our proof uses an
   inductive invariant and strong induction on QC views.
5. **Modelling choice.** The leader code of Algorithm 3 is not modelled: any proposal may arrive, as
   from a Byzantine leader. This over-approximation makes `theorem5_fixed` stronger. The
   counterexamples are executions with a Byzantine leader in every view, which the paper's
   statement covers. A round-robin variant with correct leaders running Algorithm 3 is not
   formalized.
6. **Modelling choice.** `committed` records the node `b` of Line 22. Executing "through `b`" means
   the branch of `b`, and conflict of branches is conflict of `b`.
7. **Not formalized.** Chained liveness ("we have to assume after GST two consecutive leaders are
   correct", omitted in the paper); `genericQC` handling at the leader.

## Basic HotStuff (Algorithm 2, Lemma 1, Theorem 2, Lemma 3, Theorem 4)

8. **Proof gap (true statement) — Theorem 2.** The paper's `qc_s` is the lowest-view `prepareQC`
   in `(v₁, v₂]` *conflicting* with `w`. That choice does not exclude a lock (or a justification)
   on a strict ancestor of `w`, or a justification with a view `≥ v_s`; replicas do not check
   `justify.viewNumber < curView`. Repaired by the invariant `SInv` (`Basic/Safety.lean`).
   - "Bad" QCs are those with view `> v₁` not *extending* `w`.
   - `inv2`: before any bad QC is valid, correct commit voters of `w` never vote for bad nodes.
   - `inv1`: once one is valid, fewer than `n − f` replicas can ever sign the commit QC of `w`.

   This is the "first in time" argument, stated without traces.
9. **Strengthening — Lemma 1.** Two valid QCs of the same view are on the same node, for any
   types (`Inv.node_eq`); the paper states it for equal types and conflicting nodes.
10. **Imprecision — Lemma 3.** The proof refers to the prepare votes (Line 10). The `f + 1` correct
    replicas that hold a matching `prepareQC` are the pre-commit voters (Lines 16–18). Formalized:
    a correct replica locked on a non-genesis QC has `≥ f + 1` correct pre-commit voters for it.
    Each of them has a current `prepareQC` with a view at least as high (`lemma_3`).
11. **Imprecision — Theorem 4.**
    - The proof claims the liveness rule (Line 27) holds for every correct replica. If `highQC` and
      the replica's lock have the same view, Line 27 fails (strict `>`). Then the safety rule
      (Line 26) holds, since same-view valid QCs are on the same node (`safeNode_of_correct_leader`).
    - The "highest kept lock among all replicas" must range over correct replicas.
    - The leader must ignore new-view messages with invalid QCs.
12. **Under-specified — buffering.** The pseudocode's "wait for message" must buffer messages of
    future views; otherwise the leader's proposal can arrive before a replica enters view `v`.
    The implementation buffers all messages.
13. **Under-specified — Theorem 4's hypothesis.** "All correct replicas remain in view `v` during
    `T_f`" is formalized as follows.
    - At `t₀ ≥ GST` all correct replicas are in view `v`.
    - The pacemaker does not interrupt any correct replica during `[t₀, t₀ + T_f)`.
    - A replica still leaves `v` when it decides.

    `T_f = 8(δ + 1)`: eight message delays, each `≤ δ` plus one step in the CSLib time model.
14. **Unsupported claim — §4.4 pacemaker.** "Since the interval is doubled at each time, the waiting
    intervals … will eventually have at least `T_f` overlap" is not justified. Let replica `A` decide
    in view 1 at time `α` (a Byzantine leader sends `decide` only to it) while `B` times out at `α`
    and doubles its interval. With no later decision, both are in the same view for exactly `α` in
    every view, forever (`Basic/Pacemaker.lean`, `overlap_constant`, arithmetic only). With
    `α < T_f`, `n = 4` and a silent Byzantine replica (every QC needs all three correct replicas),
    the adversary can prevent every later decision. Not a formal theorem of the paper; Algorithm 5
    later assumes synchronized leadership after GST.
15. **Typo.** Algorithm 2 Line 32 ("wait for message `m` from leader(curView)") duplicates Line 33;
    ignored.
16. **Modelling choice — signatures.** A QC carries the signed tuple and its signer set; the tokens
    `(i, tuple)` are the partial signatures. Validity is "genesis or `≥ n − f` signers", checked
    by every replica (tverify, implicit in the paper). Threshold signatures' constant size is not
    modelled, so authenticator complexity (`O(n)` per view) is **not formalized**.
17. **Modelling choice — messages.** `pre-commit`, `commit` and `decide` messages are represented by
    the QC they carry (the replica's checks use only `matchingQC`). New-view messages carry the
    sender's `prepareQC` at the moment it enters the view (`newView (v−1) prepareQC`, as Line 36).
18. **Modelling choice — pacemaker and clients.** `nextView` interrupts and the leader's client
    command per view are inputs of each replica. In the abstract model the pacemaker is arbitrary,
    and a replica may jump to any higher view. In the implementation views increase by one, as in
    the paper's loop.
19. **Modelling choice — time model.** CSLib PSync: discrete time, correct replicas awake from time
    0 with drift-free clocks, at most `f` Byzantine replicas, delivery between correct replicas
    within `max(τ, GST) + δ`. Byzantine messages are restricted only by unforgeability
    (`Run.AuthValid`: Byzantine signers, or tokens already emitted by correct replicas). Positive
    results in this model are weaker than in the DLS model with drift and late wake-up (CSLib
    caveat).
20. **Generalization.** All results hold for every `n > 3f` with quorums of size `n − f`; the paper
    fixes `n = 3f + 1`.
21. **Modelling choice — SMR.** A node is its whole branch (list of commands, newest first),
    justified by collision-resistant hashing. Safety is stated as "committed nodes do not
    conflict", i.e. executed logs are prefix-consistent. The client protocol is omitted, as in the
    paper.
22. **Strengthening.** Safety of the implementation (`impl_theorem_2`) holds in *every* run (any
    GST, any delays, any pacemaker inputs, any leader schedule). It is derived from the abstract
    system, where the leader's messages are arbitrary.

## Not formalized

Event-driven HotStuff (Algorithms 4–6), Appendix B (Lemmas 6–7, Theorem 8), the two-phase
variant and its livelessness scenario (§4.4), complexity claims, Section 7 (comparison with DLS,
PBFT, Tendermint, Casper), and Section 8 (implementation and evaluation).
