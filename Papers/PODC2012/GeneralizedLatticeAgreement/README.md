# Generalized Lattice Agreement — PODC 2012

Jose M. Faleiro, Sriram Rajamani, Kaushik Rajan, G. Ramalingam, Kapil Vaswani. *Generalized Lattice
Agreement.* PODC 2012. DOI [10.1145/2332432.2332458](https://doi.org/10.1145/2332432.2332458).
Formalized version: the 10-page extended abstract as distributed by Microsoft Research; numbering follows
it. There is no arXiv version.

**Verdict: ❌ Intent lost.** The algorithm of the title does not solve its problem: Theorem 5.15 is false, so with three
processes, one of which crashes, a value received by a correct process is never learnt, even with reliable channels, and
the abstract's claim that "every value received by a correct process is learnt in `O(N)` message delays" falls with no
repair proved. The safety part of Algorithm 2 holds (Theorems 5.1, 5.3 and 5.6 and Lemmas 5.4 and 5.5), and so do the
round lemmas behind the `O(N)` bound (5.7, 5.10, 5.11, and the `Propose` half of 5.9). Algorithm 1 as written also
violates Consistency; a one-conjunct fix of `Decide` repairs that.

## Mistakes in the paper

### ❌ Theorem 5.15 (liveness of Algorithm 2)
Algorithm 2 does not solve generalized lattice agreement: with three processes, one of which crashes,
there are fair executions in which a value received by a correct process is never learnt, even with
reliable channels (`Cex515.theorem_5_15_false`, `Cex515b.theorem_5_15_false_reliable`,
`Cex515c.theorem_5_15_false_singleton`).

**Impact.** Sinks the abstract's claim that "every value received by a correct process is learnt in
`O(N)` message delays", the progress claims of Section 6, and the `O(N)`/`O(k)` bounds; a repair needs
a protocol design change. The safety results (Theorems 5.1, 5.3, 5.6) stand.

**Details.** Each process is a proposer, an acceptor and a learner (the setting of Section 6).
Process 2 crashes; 0 and 1 are correct, which is a majority. In all three executions, the learners
stay at `learntValue = {2}` (respectively `{1}`, `⊥`) forever, and every correct process ends passive
with nothing to do.
1. *Singleton inputs, a crash in the middle of a step.* Process 2 proposes `{3}`, and acceptor 1
   accepts it. Proposer 1 gets `{2}` chosen and learnt. Proposer 0 proposes `{1,2}`. Acceptor 0 and
   acceptor 2 acknowledge it, and proposer 0 decides. But acceptor 2 crashes in the middle of this
   `Accept`: its `ACK` reaches proposer 0, not the learners. Acceptor 1 holds `{3}` and rejects
   `{1,2}`. So the learners count only one `ACK` for `{1,2}`. Late `NACK`s with `{1,2,3}` reach the
   passive proposers 0 and 1. `ProcessNACK` is enabled for passive proposers too, so both proposers
   join `{1,2,3}` into `proposedValue`. Their buffered values are now below `proposedValue`, so
   `Propose` is never enabled again. The value `{1}`, received by the correct process 0, is never
   learnt. Every other message is delivered. (`Cex515.theorem_5_15_false`)
2. *Reliable channels, a clean crash, a non-singleton input.* Process 2 proposes `{2}`, which only its
   own acceptor accepts, and then crashes between two steps. Proposers 0 and 1 each get `{1}` chosen
   and decide. Then each receives a late `NACK` `{1,2}` from acceptor 2 and absorbs it. Afterwards
   process 0 receives the input `{1,2}`. It is already below its `proposedValue`, so it is never
   proposed, and the learners stay at `{1}`. Every message sent to a correct process, including those
   of the crashed process, is processed. Theorem 5.15 also fails under the paper's literal definition
   of "learnt" (see below). (`Cex515b.theorem_5_15_false_reliable`)
3. *Singleton inputs, no help from late `NACK`s.* Executions 1 and 2 use that a passive proposer
   still processes late `NACK`s; one might read a guard `status = active` into `ProcessNACK`. This one
   does not depend on it. Process 2 proposes `{3}`, which acceptor 1 accepts. Proposers 0 and 1 both
   propose `{1}`; acceptors 0 and 2 acknowledge both proposals, so both decide. Acceptor 1 rejects
   both. The faulty acceptor 2's `ACK`s to the learners are lost (assumption (d) covers only messages
   between correct processes). Each proposal reaches the learners with one `ACK` only, and the
   learners stay at `⊥`. Every message between correct processes is processed. Without the late
   `NACK`s the proposers stay at `proposedValue = {1}`, which is just as stuck.
   (`Cex515c.theorem_5_15_false_singleton`, `Cex515c.run_trNoNack`)

The proof of Theorem 5.15 says: "once a value is chosen, a correct learner will eventually receive the
acknowledgments sent for the chosen value". This is false when the quorum contains a faulty acceptor.
Both this and the Lemma 5.14 step below are protocol problems, not just proof gaps. The paper
explicitly allows crashes in the middle of a step and message loss, and asks only that messages
between correct processes be delivered. So no implicit assumption rescues the theorem. Execution 3
shows that the learner problem alone breaks the theorem. So a repair needs a design change (for
example, deciders forwarding their decisions to the learners), not a local fix of the pseudocode. The
same executions break the progress claims of Section 6. In Algorithm 4, `ExecuteUpdate` waits forever
for `cmd ∈ LearntValue()`, so it is not wait-free. They also break the `O(N)`/`O(k)` message-delay
bounds of the abstract and Section 5.3. We did not formalize a repaired algorithm.

### ❌ Lemma 5.14 (a passive proposer initiates every received value)
In execution 2 above no proposal and no `ACK` ever covers the received value `{1,2}`
(`Cex515b.theorem_5_15_false_reliable`).

**Impact.** A second, separate cause of the failure of liveness; no corrected lemma is proved.

**Details.** The proof says: "if any correct proposer … is passive when it receives `u`, it will
initiate `u`". This ignores that `proposedValue` grows while the proposer is passive.

### 🔧 Algorithm 1 and Lemma 5.9 (the guard of `Decide`)
`ProcessNACK` enlarges `proposedValue` while `ACK`s are still counted and `Decide` has no conjunct `nackCount = 0`, so
the output may be a value that was never chosen.

**Impact.** Algorithm 1 violates Consistency even failure-free, "at most one `Decide` per round" fails, and the proof
step "`v₂` must be a chosen value" is false. Lemma 5.11 needs only the `Propose` half of Lemma 5.9.

**Details.**
- *Algorithm 1 (Consistency, failure-free).* With initial values `{1}, {2}, {3}` and three acceptors, two proposers
  decide the incomparable `{1,2}` and `{1,3}` (`Cex1.alg1_consistency_false`). `ProcessNACK` joins a rejection value
  into `proposedValue` while `ACK`s for the same proposal are still being counted. `Decide` (guard
  `ackCount ≥ ⌈(N_a+1)/2⌉`) then outputs this enlarged value, which was never proposed. Proposer 0 processes a `NACK`
  `{1,2}` (caused by proposer 1's `{2}`) and then two `ACK`s for `{1}`, and it decides `{1,2}`. Proposer 2 is rejected,
  refines to `{1,3}` and decides it. The prose of Section 3 has the intended rule: "if all these responses are
  acceptances, the proposer is done".
- *Lemma 5.9 ("at most one `Decide` per round").* It fails for the same reason, even failure-free: proposer 0 decides
  the unchosen `{1,2}` (its `{1}` was chosen) and then the chosen `{1,2,3}`, which lie below exactly the same chosen
  values (`Cex59.lemma_5_9_decide_false`).
- *Lemma 5.9, `Propose` half.* "At most one `Propose` per round" is true, but the proof's "`v₂` must be a chosen value"
  is false.

**Repair.** Adding the guard `nackCount = 0` to `Decide` makes every output a chosen value, and Consistency holds
(`consistency_of_clean`). We prove the `Decide` half of Lemma 5.9 for decisions with `nackCount = 0`
(`lemma_5_9_decide_clean`). For the `Propose` half, which we prove for the printed algorithm (`lemma_5_9_propose`), the
right argument uses the *last proposal* before the `Decide`, which a quorum acknowledged.

### ✏️ Slips
- **Lemma 5.13 (missing "initiated by a correct proposer").** A proposer may initiate `{3}`, crash, and lose its
  messages; then `{3}` is never part of a chosen value (`Cex513.lemma_5_13_false`). The lemma is only used for correct
  proposers.
- **Section 5 (definition of "learnt").** "A value `v` is learnt by `p` if `p` executes `Learn(w)` for some `w ⊒ v`"
  makes Theorem 5.6 false if taken literally: every `ACK` makes all values below it "learnt", so one `ACK` of `{1,2}`
  "learns" the incomparable `{1}` and `{2}`. We read Theorem 5.6 as being about `learntValue`, and Theorem 5.15 with the
  problem definition "`v ⊑` a learnt value". Execution 2 above refutes Theorem 5.15 under both readings.

### Typos
- "Proposed" literally means "proposed exactly"; Lemma 5.14 needs "included in a proposal".
- The first author's name is misspelled "Falerio" on the paper.

## Proof gaps (statements true)

### 🔧 Lemma 5.11 (length of the `covered` chain)
The proof shows `covered₂ ⊇ Prev` and then asserts "the strictly increasing sequence … can have length
at most `N_p + 1`", which also needs `covered₁ ∩ Curr ≠ ∅`.

**Impact.** The lemma stands; a few lines close the step (`lemma_5_11`).

**Details.** `covered₁ ∩ Curr ≠ ∅` means that `w₁` is not a join of values of earlier rounds. That
holds because the chosen values form a chain. With it, `covered₂, …, covered_k` lie between
`Prev ∪ {u₀}` and `Prev ∪ Curr`, and `|Curr| ≤ N_p`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing, written as the paper's guarded actions (`Model.lean`). Proposers `P`,
  acceptors `A` and learners `Ln` are arbitrary finite types; the counterexamples use `P = A = Ln = Fin 3`
  (one process, all roles). Values form a join-semilattice with `⊥`; the counterexamples use `Finset ℕ`.
* The network is the set of all messages ever sent; each receiver records what it has consumed. So
  delays, reordering and loss are choices of the scheduler. Messages carry their sender. A proposer's
  `ackCount`/`nackCount` is the number of acceptors heard from for the active proposal; a learner's
  `ackCount[id][n]` likewise. Without duplication this is the paper's counting.
* Failures: crash-stop (a faulty process takes no more steps). Fairness (`Exec.Fair`): a non-input action
  of a correct process that consumes no message, or a message from a correct process, and stays enabled is
  eventually taken. This is the paper's assumption (d) plus the "repeatedly selects any enabled action"
  scheduler. Liveness assumptions (a)–(c) are `LivenessAssumptions`; liveness of the problem
  (Section 4.4) is `Exec.GLALiveness`.
* Safety results hold for **all** reachable states, under arbitrary loss, delays and crashes. Rounds
  (Lemmas 5.8–5.11) are taken relative to the values chosen by the end of a finite execution, as in the
  paper: `SameRound s u v` means `u` and `v` lie below the same chosen values.
* Algorithm 1 is the same system started with `bufferedValues = initialValue` and without `Receive`
  steps.
* Counterexamples are explicit schedules checked by `decide +kernel`. Each ends in a state where no action
  of a correct process on a message of a correct process is enabled; it is extended by stuttering, which
  gives a fair infinite execution (`Exec.ofRun_fair`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5.1 / Corollary 5.2 (validity) | `theorem_5_1`, `corollary_5_2` | `Safety.lean` |
| Theorem 5.3 (stability) | `Exec.learnt_mono` | `Model.lean` |
| Lemma 5.4 | `lemma_5_4` | `Safety.lean` |
| Lemma 5.5 | `lemma_5_5` | `Safety.lean` |
| Theorem 5.6 (consistency) | `theorem_5_6` | `Safety.lean` |
| Lemma 5.7 | `lemma_5_7` | `Rounds.lean` |
| Lemma 5.8 | `lemma_5_8` | `Rounds.lean` |
| Lemma 5.9, `Propose` half | `lemma_5_9_propose` | `Rounds.lean` |
| Lemma 5.9, `Decide` half: **false** / repaired | `Cex59.lemma_5_9_decide_false` / `lemma_5_9_decide_clean` | `OtherCounterexamples.lean` / `Rounds.lean` |
| Lemma 5.10 | `lemma_5_10` | `Rounds.lean` |
| Lemma 5.11 | `lemma_5_11` | `Rounds.lean` |
| Lemma 5.13: **false** without "correct" | `Cex513.lemma_5_13_false` | `OtherCounterexamples.lean` |
| Lemma 5.14: **false** | `Cex515b.theorem_5_15_false_reliable` | `LivenessCounterexample.lean` |
| Theorem 5.15: **false** | `Cex515.theorem_5_15_false`, `Cex515b.theorem_5_15_false_reliable`, `Cex515c.theorem_5_15_false_singleton` | `LivenessCounterexample.lean` |
| Algorithm 1 Consistency: **false** / repaired | `Cex1.alg1_consistency_false` / `consistency_of_clean` | `Algorithm1.lean` |

Lemma 5.10 is stated only for `v_{r−1}`; we prove it for every chosen `c` with `w₁ ⋢ c`.

**Not formalized.** Lemma 5.12 ("every round eventually terminates"; it is vague, and it fails in the
execution of `Cex513`). The time-complexity arguments of Sections 3 and 5.3 beyond Lemma 5.11. Liveness of
Algorithm 1. Section 6 (serializable and linearizable replicated state machines). A repaired liveness
theorem for a corrected Algorithm 2.

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The safety invariant (`Inv`, `InvStep.lean`) holds for every initial buffer, so it covers
Algorithm 1 and Algorithm 2. Non-vacuity: the counterexample executions satisfy the liveness assumptions
and the fairness condition. Paper-specific model; no CSLib dependency beyond Mathlib, and no CSLib
candidates.
