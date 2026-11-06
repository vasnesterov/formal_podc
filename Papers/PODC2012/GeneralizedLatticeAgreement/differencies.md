# Differences between the formalization and the paper

Paper: J. M. Faleiro, S. Rajamani, K. Rajan, G. Ramalingam, K. Vaswani, *Generalized Lattice Agreement*,
PODC 2012 (10-page extended abstract). Symbols were checked on rendered pages (Algorithm 2's `Propose` guard
is `proposedValue ⊔ bufferedValues ⊐ proposedValue`; `Learn` updates when `learntValue ⊏ value`).

## Errors in the paper (statement level)

1. **Theorem 5.15 is false** (`Cex515.theorem_5_15_false`, `Cex515b.theorem_5_15_false_reliable`,
   `Cex515c.theorem_5_15_false_singleton`, `LivenessCounterexample.lean`). All three executions use three processes playing all roles, with process 2
   faulty. They satisfy the liveness assumptions (a)–(d) of Section 5.2 and are fair.
   * Execution 1 (34 steps; singleton inputs `{1}, {2}, {3}`). The faulty acceptor's `ACK` of the
     decided proposal `{1,2}` reaches the proposer but not the learners: the acceptor crashes in the
     middle of `Accept`. This is explicitly allowed: "a process may fail in the middle of an execution
     step". Every other message sent to a correct process is processed (`AllDelivered`). Late `NACK`s
     make both correct proposers absorb all values into `proposedValue`, so `Propose` stays disabled.
     Final `learntValue = {2}`, although `{1}` was received by the correct process 0.
   * Execution 2 (37 steps; inputs `{2}, {1}, {1,2}`). Process 2 crashes between steps, and **every**
     message sent to a correct process (also by process 2) is processed (`AllDeliveredB`). The input
     `{1,2}` arrives at process 0 after it absorbed `{1,2}` through a late `NACK`. It is never included in
     any proposal or `ACK`, so it is never learnt in either reading of "learnt". The non-singleton input
     is legal: Section 4 lets a process receive any value of an arbitrary join semilattice (here the
     power set of ℕ); singleton inputs appear only in the application of Section 6.
   * Execution 3 (`Cex515c.theorem_5_15_false_singleton`, 27 steps; singleton inputs `{1}, {3}`).
     Executions 1 and 2 both rely on a passive proposer processing a late `NACK` (`ProcessNACK`
     has no `status = active` guard). Execution 3 does not: the faulty acceptor 2 acknowledges the
     proposals `{1}` of both correct proposers, its copies for the learners are lost (allowed: the
     sender is faulty), and the correct acceptor 1, holding `{3}`, rejects both. The learners stay at
     `⊥`. Every message between correct processes is processed (`AllCorrectDelivered`).
     `run_trNoNack` checks that the schedule without the two late `ProcessNACK` steps is a run in which
     both correct proposers stay passive with nothing to propose; so the variant with a
     `status = active` guard in `ProcessNACK` fails too. That variant is not a separate Lean model; the
     bridge is that its run is ours minus the two `ProcessNACK` steps, with those `NACK`s discarded. Under
     the strictest channel reading (only the last broadcast of a crashing process may be partially lost),
     Execution 2 applies instead.
   * ❌. The abstract presents the algorithm and its guarantee as a primary contribution ("We
     present a wait-free algorithm for solving generalized lattice agreement. The algorithm guarantees
     that every value received by a correct process is learnt in O(N) message delays"). The claim is
     about the paper's specific algorithm. No implicit assumption rescues it: the paper explicitly includes message loss
     and mid-step crashes in its failure model and requires delivery only between correct processes.
     Execution 2 needs neither. No local fix rescues it: Execution 3 survives the only local pseudocode
     fix in sight (`status = active` in `ProcessNACK`); the error is the proof's claim that a correct
     learner receives the `ACK`s of a chosen value, and repairing it changes the protocol. It is not a
     degenerate case: `N = 3` with one crash is the smallest non-trivial instance.
   * Consequences, not formalized separately: the `O(N)`/`O(k)`/"3 message delays" bounds (abstract, §1,
     §5.3); Section 6's progress claims ("every update operation will eventually be reflected in all read
     operations"); and the termination of Algorithm 4's `ExecuteUpdate` (`waituntil cmd ∈ LearntValue()`)
     for the command `{1}` of execution 1. Execution 1 uses singleton inputs, as Section 6 does. Section 6
     assumes "message delivery is reliable"; in execution 1 the only undelivered messages are the
     learners' copies of the crashing acceptor's last broadcast.
2. **Lemma 5.14 is false** (execution 2; `theorem_5_15_false_reliable` states that no proposal ever
   includes `{1,2}`). The proof assumes that a passive proposer receiving `u` initiates `u`. But a passive
   proposer's `proposedValue` may already include `u` through a late `NACK`. ❌
3. **Algorithm 1 violates Consistency** (`Cex1.alg1_consistency_false`, failure-free, 21 steps). The
   outputs are `{1,2}` and `{1,3}`. 🔧 The intended rule is recoverable from the
   prose of Section 3: "whenever a proposed value gets a majority of acceptances … its proposed value is a
   chosen value"; "If all these responses are acceptances, the proposer is done … Otherwise, it refines".
   The fix is local: add the conjunct `nackCount = 0` to `Decide`'s guard. The paper's proofs (Lemma 5.9)
   reason with the intended version ("`v₂` must be a chosen value").
   The repaired consistency is `consistency_of_clean`. Repaired validity: `theorem_5_1` (outputs are
   joins of initial values). That the output is above the proposer's own initial value is not formalized,
   but it is immediate: `proposedValue` only grows.
4. **Lemma 5.9, "at most one `Decide` step in a round", is false** for the pseudocode as written
   (`Cex59.lemma_5_9_decide_false`; failure-free fair execution, 46 steps, all messages delivered). The
   cause is the same as in item 3. 🔧, with the same fix as item 3; it holds for clean
   decisions (`lemma_5_9_decide_clean`).
5. **Lemma 5.13 lacks the hypothesis "initiated by a correct proposer"** (`Cex513.lemma_5_13_false`). In
   the counterexample the faulty proposer's messages are lost, which the failure model allows. ✏️: the
   hypothesis holds at its only use (Theorem 5.15 via Lemma 5.14 concerns values proposed by
   correct processes). Lemma 5.12 ("every round eventually terminates") is too vague to formalize. In the
   same execution, the round of the faulty proposer's step never completes.

## Proof gaps and repairs (statements true)

6. **Lemma 5.9, `Propose` half.** The proof says "`v₂` must be a chosen value". With the pseudocode as
   written, the decided value need not be chosen. The repaired proof: between two `Propose` steps of `q`
   there is a `Decide` at some proposal number `m`, so a quorum acknowledged proposal `m` and `w_m` is
   chosen. Then `u₁ ⊑ w_m ⊏ u₂`, so `w_m` separates the rounds (`lemma_5_9_propose`). 🔧
7. **Lemma 5.11.** The final step ("the strictly increasing sequence covered₁ ⊂ ⋯ ⊂ covered_k can have
   length at most `N_p + 1`") also needs a current-round value `u₀ ∈ covered₁`. If every initiated value
   below `w₁` were of an earlier round, the join of the chosen values above them would be a chosen value
   `c` with `w₁ ⊑ c` and `w₁ ⋢ c`; this uses that the chosen values form a chain. Then
   `Prev ∪ {u₀} ⊆ covered_j ⊆ Prev ∪ Curr` for `j ≥ 2`, and `|Curr| ≤ N_p` by Lemma 5.9. "Each proposed value
   is a join of values in All" is the invariant `InitInv` (`InitInv.lean`). It also needs that
   proposals are never `⊥`, so that `covered₁ ≠ ∅`. 🔧
8. **Lemma 5.10** is proved in a stronger form: for every chosen `c` with `w₁ ⋢ c`, `c ⊑ w₂`. The
   paper's "`a` must have acknowledged `v_{r−1}` before responding to `w₁`" is replaced by a time-free
   invariant: all `ACK` and `NACK` values of one acceptor form a chain (`Inv.resp_chain`).

## Definitions (under-specified or literally wrong)

9. **"Learnt".** Section 5 defines "`v` is learnt by `p` if `p` executes `Learn(w)` for some `w ⊒ v`".
   `Learn` runs on every `ACK`, so literally all values below any acknowledged proposal are "learnt", and
   Theorem 5.6 would fail at once (one `ACK` of `{1,2}` "learns" `{1}` and `{2}`). We formalize Theorem 5.6
   for the values of `learntValue` (the outputs, as in `LearntValue()`), and liveness as in the problem
   definition: `v ⊑ learntValue`. Execution 2 refutes Theorem 5.15 also for the literal definition. ✏️
10. **"Proposed"** literally means "is the value of some proposal". Lemma 5.14 must mean "is below the
   value of some proposal". Execution 2 refutes both readings.
11. **Rounds.** The paper indexes the chain of chosen values of a finite execution. We use the
   equivalent "below the same chosen values" (`SameRound`), relative to the values chosen by the end of a
   finite execution (a reachable state). In the counterexample to Lemma 5.9 the execution then stutters,
   so the final chosen set is the chosen set of the whole infinite execution. The dummy round 0 for
   `v = ⊥` is not modelled; proposals are never `⊥`.
12. **Quorum size** `⌈(N_a + 1)/2⌉` is `quorum A = N_a / 2 + 1` (`quorum_eq_ceil`).

## Modelling choices

13. **Messages and channels.** `sent` is the set of all messages ever sent, and receivers record the
   messages they consumed. A message never consumed is delayed forever or lost. Asynchrony is the
   scheduler's free choice of the next enabled action.
14. **Sender identities.** `ACK`/`NACK` carry the acceptor, and `InternalReceive` carries its sender. The
   paper's counters count messages; ours count distinct acceptors for the active proposal (resp. per
   `(proposer, number)` for learners). Each acceptor answers each proposal at most once, so the counts
   agree. Two identical `InternalReceive(v)` messages from the same sender are merged. This only affects
   `bufferedValues` by re-joining a value already included, and never the `Propose` guard or its effect.
15. **Counters as per-number sets.** `acks n`/`nacks n` are kept for all proposal numbers. The paper's
   counters are those of the active number; the others are ghost history. The reset
   `ackCount = nackCount = 0` is the reset of the new number's sets.
16. **Ghost state:** `received`, `initiated`, `decisions` (each `Decide` with its proposal number and
   whether `nackCount = 0`).
17. **Failures and fairness.** A crash is "the process takes no more steps" (`Exec.CrashStop`). Message
   loss is non-consumption. A crash in the middle of a step is modelled by the loss of the remaining
   copies of its broadcast. Fairness (`Exec.Fair`) is weak fairness for non-input actions of correct
   processes whose triggering message (if any) comes from a correct process. This combines the
   assumption "messages between correct processes are eventually delivered" with the paper's scheduler
   ("repeatedly selects any enabled action"). The counterexamples end in states where no such action is
   enabled, so they are fair under any reasonable fairness notion.
18. **Algorithm 1** is Algorithm 2 started with `bufferedValues = initialValue` and run without `Receive`.
   For `initialValue = ⊥`, Algorithm 1 would propose `⊥` and our model does not. The counterexample uses
   non-`⊥` initial values. The repaired Algorithm 1 is represented by the executions in which every
   `Decide` happens with `nackCount = 0` (`hclean` in `consistency_of_clean`). These are exactly the
   executions of the algorithm with the strengthened guard.
19. **Lemma 5.4** is stated for infinite executions (`Exec`) and two `Accept` steps at times `t < t'`.
   Theorem 5.6 is stated for any two learners at any two times of an execution, which covers "two values
   learnt by two different processes" and also a single learner.
20. **Theorem 5.1** is proved for all values in the system (`ValidityInv`), and "the join of some subset"
   allows the empty join `⊥`.
