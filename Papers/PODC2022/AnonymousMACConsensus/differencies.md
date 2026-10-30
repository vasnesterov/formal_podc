# Differences between the formalization and the paper

Tseng, Zhang, *Brief Announcement: Computability and Anonymous Storage-Efficient Consensus with an Abstract MAC
Layer*, PODC 2022 (3-page BA; numbering as there).

## Model (`Model.lean`)

1. **Values carry sequence numbers.** The paper assumes that stored values are unique ("can be achieved using
   sequence numbers and node identifiers") and merges views by "the newer value from each node". We tag the value
   of the store operation `(j, m)` (the `m`-th operation of node `j`) with `m`: entries are `(m, v)`, and
   `View.merge` keeps the entry with the larger index. This makes the merge computable by a node. With values
   alone it is not: a node that holds `j`'s newer value and then receives a stale view cannot tell which entry is
   newer. Client values need not be unique in our model, so the assumption is dropped rather than added. This
   is an implied assumption (R4): sequence numbers are the paper's own suggested implementation.
2. **Operation identities in the history.** Events are `inv i n o` and `ret i n r`. Histories are lists, and
   `<_H` is the list order (`Before`, `Precedes`). In regularity, "`Store_j(v)`" is the store operation `(j, m)`
   whose entry is `(m, v)`. The paper's `v' ≠ v` becomes `m' ≠ m`.
3. **Event granularity.** Lines 1 and 2 (and 4 and 5) are one atomic step `exec`: compute `currentView` and
   start `mac-broadcast`. Starting the broadcast has no other effect, so a schedule in which the handler runs
   between line 1 and line 2 is equivalent to one in which it runs right after the combined step. Invocation is
   a separate step, so a client may invoke while messages are queued.
4. **MAC layer.** Each broadcast is delivered to each node at most once, in any order, and possibly to every
   node. The ack is enabled once every node that has not crashed yet has received it. Delivery may continue after
   the sender crashed, or stop: the adversary chooses. Deliveries to crashed nodes are allowed and have no
   effect. Single hop. These choices are at least as general as the paper's description.
5. **Handler.** One FIFO queue per node. A handler step pops one message and merges it (lines 7–8). Assumption
   (iii) ("the handler has a priority over the main thread") is the guard `prio = true → queue i = []` on the
   main-thread step that reads `view_i` (lines 1/4). The return step (lines 3/6) is not guarded, which only
   adds executions. With `prio = false` the guard is dropped (used only for the necessity counterexample).
6. **Nodes.** An arbitrary type `ι` (finite or infinite), `DecidableEq`. The algorithm does not use `n`.
   Any number of crashes. A crashed node takes no step.
7. **Executions.** Theorem 1 is proved for all finite executions from the initial configuration (`Reach`).
   Regularity is a safety property, so this covers every infinite execution. The wait-freedom counterexample is
   an infinite sequence of configurations with a valid step between consecutive ones.

## Theorem 1 (`Main.lean`: `theorem_1`)

8. **Statement.** "MAC-SC correctly implements the store-collect object" (Definition 1) becomes: every history
   of every execution with handler priority satisfies `Regular` (both bullets of the regularity definition and
   `⪯`, transcribed). In Property I(ii) the negated existential uses two independent `Before` facts for the
   middle event, which is slightly stronger than one chain of positions. Faithful otherwise.
9. **Proof.** The paper's sketch is morally right. Our proof is an inductive invariant (`Invariant.lean`,
   `Preservation.lean`, `Regular.lean`). Gaps in the sketch that we fill:
   - The sketch reasons with "node `i` has not received any message from `j`'s mac-broadcast". It must use
     (iii): a message *delivered* before a collect's invocation has been *processed* before line 4.
   - Property II: "all the fault-free nodes have received the broadcast message" should be "all nodes not
     crashed yet". The node of the later collect may crash after that collect returns, so it need not be
     fault-free.
   - Property I(ii) ("we can prove by contradiction") needs the merge to be monotone in the sequence number, and
     the stores of `j` to complete in increasing index order.

   These are routine details, not a genuine repair (✅-level for this statement).
10. **Assumption (iii) is necessary** (`theorem_1_needs_priority`). With `prio = false`, the two-node history
    `inv 0 0 (store 7), ret 0 0 ack, inv 1 0 collect, ret 1 0 (view ∅)` is reachable and violates Property
    I(i). The paper does assume (iii), so this is not an error. It documents that the assumption carries the
    proof.

## Wait-freedom (`Starvation.lean`: `Starvation.mac_sc_not_wait_free`)

11. **Claim.** Abstract: "All of the algorithms are wait-free." For MAC-SC this means that an operation of a
    node that does not crash completes, no matter what the other nodes do.
12. **Counterexample under literal (iii).** Two nodes, values in `ℕ`. After a preamble, node `1` has completed
    `Store₁(0)`, its message sits in node `0`'s queue, and node `0` has invoked `Collect₀`. Then each round of 8
    steps goes: node `1` invokes `Store₁(0)`, executes line 1, its broadcast is delivered to `1` and then to `0`
    (node `0`'s queue now holds 2 messages), node `0`'s handler processes the older one, node `1`'s handler
    processes its own, ack, return. Formally: an infinite sequence of configurations with a valid step between
    consecutive ones, starting from a reachable one. No crashes. Node `1`'s operation count is `k + 1` after `k`
    rounds. Node `0`'s handler steps once per round and its queue holds 1 or 2 messages, so every message
    delivered to it is processed. Node `0`'s queue is never empty, so its line 4 is never enabled and its phase
    stays `invoked collect` forever. Fairness: every broadcast is delivered to all nodes and acknowledged, and
    every handler message is processed. Node `0`'s main-thread step is never enabled, so even strong fairness
    holds.
13. **Classification (R3/R4, borderline with ❌).** The claim fails because of the literal reading of (iii).
    The proof of Theorem 1 only needs the messages delivered before the invocation of an operation to be
    processed before its line 1/4. The paper's own proof gives this repaired assumption ("a local fix of a
    hypothesis"). Under it the main thread cannot be starved (finitely many messages precede the invocation), and
    MAC-SC is wait-free given that the MAC layer acknowledges every broadcast of a live node. The usual
    convention that local computation takes no time also excludes the starvation. Not formalized: the regularity
    proof under the repaired rule (it would need `Knows` to record knowledge at invocation time) and the positive
    wait-freedom statement.

## Not formalized

14. The stacked constructions of [4] (snapshots, counters, sets, multi-writer atomic registers) and the claim
    that the abstract MAC layer and message passing have the same computability. These are references to other
    papers.
15. The anonymous approximate and randomized consensus algorithms (Section 4). The BA only mentions them.
