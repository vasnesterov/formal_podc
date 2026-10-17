# TetraBFT — differences between the paper and the formalization

Paper: Yu, Losa, Wang, *TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus*,
PODC 2024, DOI 10.1145/3662158.3662783. Formalized version: arXiv 2405.02615v2 (April 2026),
identical to the local copy. Compared with v1 (May 2024), v2 changes only wording (Table 1
discussion, typesetting); Rules 1–4, the lemmas and the proofs are the same.

## 1. Errors and gaps in the paper

1. **Theorem 1, termination: false** (false statement). The view-change rule of §3.2 is: (a) on
   timer expiry, broadcast `⟨view-change, v+1⟩`; (b) on `f + 1` view-change messages for `v'`,
   send `⟨view-change, v'⟩` *if no view-change message for `v'` or any higher view was sent*;
   (c) on `n − f` view-change messages for a view, move to it. Timers fire once per view and nothing is
   retransmitted. Rule (b)'s guard lets a node that already echoed a *higher* view refuse to echo
   the view the others are trying to reach. The result can be a permanent split.
   * Reliable channels (every message eventually delivered; after GST within Δ), `n = 7`, `f = 2`,
     timeout `9Δ`, Δ = 1, GST = 30. From time 41 on, correct nodes 2, 3, 4 sit in view 1 and nodes 5, 6
     in view 2. Nothing is in transit, no timer will fire, and no correct node ever decides
     (`Deadlock.termination_fails`, `Deadlock.views_stuck`, `Deadlock.not_solvesConsensus`). The same
     schedule with all times rescaled (GST = 54, quiet from time 75) deadlocks with timeout 17 = 8δ + 9.
     That is the bound under which the repaired rule provably terminates (`Deadlock17.*`), so the
     contrast with the repair is like-for-like. The key
     step: node 6 echoes view 3 (one correct + two Byzantine messages) before it receives the
     view-2 messages, so it enters view 2 without ever sending `⟨view-change, 2⟩`, and the three
     nodes in view 1 are left with 4 < n − f view-2 messages.
   * Paper's own model (messages sent before GST may be lost, §2): already `n = 4`, `f = 1`
     deadlocks. Node 2 enters view 1 alone, nodes 1 and 3 never see enough messages, and nothing is
     resent (`Lossy.termination_fails_lossy`).
   * The same reliable-channel pattern works for every `f ≥ 2` with `n = 3f + 1` (informal). Take
     `2f` correct nodes `A` (one of them, `x`, enters view `w`) and one correct node `b`. `b`
     echoes `w + 1` on `x` + `f` Byzantine messages, then enters `w` on `A` + 1 Byzantine message.
     `A \ {x}` stays below `w` with `2f < n − f` view-`w` messages and `2 < f + 1` view-`(w+1)`
     messages. For `f = 1` this pattern fails (it needs `2 < f + 1`); we did not find a deadlock for
     `n = 4` with reliable channels, but with message loss `n = 4` deadlocks (previous item).
   * Where the paper's argument breaks: the justification of the 9Δ timeout (§3.2) assumes that
     every correct node echoes the `f + 1` view-change messages it receives, and Theorem 1's
     termination proof cites only Lemmas 2, 4, 5, which assume a view with a well-behaved leader
     that all correct nodes enter after GST. View synchronization is never proved, and with this
     rule it fails.
   * Multi-shot TetraBFT (Algorithm 2, line 4: `if v' > proposed_v`) uses the same guard, so the
     liveness half of Theorem 2 is affected in the same way (informal, not formalized).
   * Repair (not in the paper): echo `⟨view-change, w⟩` for every `w ≥` the current view for which
     none was sent yet (drop "or any higher view"; `prm.fixEcho = true`). With reliable channels,
     `3f < n`, timeout `T ≥ 8δ + 9` and round-robin leaders, the repaired protocol solves consensus
     (`fixed_solvesConsensus`). The proof has three steps:
     - spacing: the first correct node reaches `u + 1` at least `T` after the first one reaches
       `u`;
     - catch-up: all correct nodes are in `u` from 2δ + 2 after that first entry until `T` after it;
     - within-view liveness: `decides_of_synchronized_view` needs 6(δ + 1) ticks.

     In the lossy model the repair would also need retransmission; this is not formalized.
   * The paper's view-local liveness argument (Lemmas 2, 4, 5 and the 6Δ budget inside the 9Δ
     timeout) is correct: `decides_of_synchronized_view`. If all correct nodes are in a view with a
     correct leader during `6(δ + 1)` ticks after GST, they all decide.
2. **Proof of Lemma 7: false intermediate claim** (proof gap; statement true). The proof says that
   if a correct node decides `val` in view `v`, then "every well-behaved node that sends a vote-1
   message does so with value `val`". With a Byzantine leader this is false. In a synchronous run
   with `n = 4`, `f = 1`, correct node 1 decides `true` in view 0 while correct node 3 sends vote-1
   for `false` in view 0 (`Lemma7.lemma7_proof_claim_false`). Lemma 7 itself follows from quorum
   intersection on vote-4/vote-3 (Lemma 6), which is what we prove (`Execution.lemma7`).
3. **Proof of Lemma 2: wrong choice of quorum** (proof gap; statement true). The proof takes "the last
   view `v'` in which some node in `q` sent vote-3", where `q` is the quorum of suggest messages
   the leader received, which may include Byzantine members with fabricated reports; then
   "node `i` must have received vote-2 messages from a quorum" fails. The argument works with `q` =
   the set of correct nodes, which Rule 1 allows the leader to choose (`Execution.lemma2`).
4. **Lemma 4: hypotheses only in the surrounding text** (under-specified statement). "A
   well-behaved node eventually determines that the leader's value is safe" needs: the leader is
   well-behaved and the node holds proof messages of *all* correct nodes for the view. We state
   these hypotheses; the leader's suggest quorum may be arbitrary (`Execution.lemma4`,
   `follower_determines_safe`).
5. **Mechanical verification covers a different rule** (scope of §5). The TLA+ specification
   (Appendix B, `ShowsSafeAt`) has only item 2(b)iiiA of Rule 3. Item 2(b)iiiB (two blocking
   sets for different values) is missing, so the Apalache check of the inductive invariant is about
   a stricter vote-1 rule than the paper's. The check is also restricted to `n = 4`, where iiiB is
   not needed for liveness either: two vote-1 quorums share a correct node, which claims every value
   safe. Our Lean safety proof covers the paper's Rule 3 including iiiB, for all `n > 3f`.
6. **Validity proof** (proof gap; statement true). The argument ("each well-behaved node sends
   vote messages ... for value `val` in the previous views. Consequently ... the initial value
   `val` is determined safe") is circular as written. The correct argument is an induction over
   time. If all reports carry only `val`, then whenever Rule 1 shows some value safe it shows `val`
   safe (`ShowsSafe.of_vals`). This needs the leader to propose its input whenever Rule 1 shows the
   input safe, which is our reading of "should the leader determine that arbitrary values ... are
   safe ..., it will propose its initial value" (`tetra_validity`).
7. **Section 6 (multi-shot, Theorem 2)** (under-specified; not formalized).
   * How a vote for slot `s` counts as vote-k for the ancestors when the slots are in different
     views is not specified.
   * Off by one: Fig. 2 makes the vote for slot `s + 3` the vote-4 for slot `s`, while the proof of
     Theorem 2 says "vote-4 for block `s − 4`".
   * The consistency proof reduces to per-slot agreement. It does not argue that finalizing a block
     also decides its ancestors in their own slots.
8. **Typos and slips.** Lemma 8 (d)ii ends with "Therefore, either `m` or `m'` satisfies Rule 4 Item 3";
   it should be "neither". In Lemma 8 (d)iii the view is written `v̄` and then `v̂`. Theorem 1's proof
   has "`i` decides `val_j`". §1 has "quadrati", "whooping"; §3.1 has "struture".

## 2. Modelling choices

* **Network and time.** CSLib's partially synchronous model `Cslib.Byzantine.PartialSync`.
  * Discrete global time; every correct node takes one deterministic step per tick and has no
    clock drift.
  * Authenticated point-to-point channels and no signatures: Byzantine nodes may send anything,
    including different messages to different nodes, but cannot forge senders.
  * A run fixes GST and all delivery times.
  * `Run.Valid f δ`: at most `f` faulty nodes, and every message between correct nodes is delivered
    by `max(send time, GST) + δ`. These are reliable channels, stronger than the paper's model.
  * `LossyValid` is the paper's model: messages sent before GST may be lost.

  Both counterexamples live in models where the adversary is *weaker* than the paper's, so they
  are stronger than needed. The safety results (`tetra_agreement`, `tetra_validity`) use no
  timing or delivery assumption, so they hold in fully asynchronous executions.
* **Δ and the timeout.** δ = Δ (one tick is the time unit). The counterexamples use Δ = 1 and the
  paper's timeout 9Δ = 9 ticks.
* **Messages.** Everything is broadcast, including suggest messages (the paper sends those to the
  leader only); other nodes ignore them. A node keeps all received messages, so votes for a view
  received before entering it count after entering. For Byzantine duplicates, the first proposal
  of the leader and the first proof/suggest message of each sender are used.
* **Storage.** A node keeps its full vote history and computes proof/suggest reports from it
  (`mkReport`: highest vote, highest vote for a value different from the highest one, highest
  vote-3/4). These are exactly the paper's report fields; the constant-storage bookkeeping is an
  optimization and is not modelled. The safety proof only uses the relational spec `IsReport`, so
  any implementation meeting it is covered.
* **Rules 1–4** are formalized verbatim (`ShowsSafe`, `Claims`). In particular:
  * "No member of `q` sent any vote-3/4 before `v`" (item 2a) is read as "reported no vote-3/4"
    (Algorithms 4/5: `vote3 = ∅`).
  * The blocking sets of item 2(b)iii may be any sets of senders, as in the rule text. Algorithm 5
    requires them inside the quorum, which is stricter, so our safety theorem covers it. The
    liveness lemmas produce blocking sets of correct nodes, inside the quorum of correct nodes.
  * Rule 3 at view 0 is "all values safe" (§3.2 step 1 and Lemma 4's first case).
  * The rules are decided classically; Algorithms 4 and 5 (efficient search) are not formalized.
* **Leader.** Once per view, the leader proposes its input if Rule 1 shows the input safe, and
  otherwise some value Rule 1 shows safe. It proposes as soon as possible, which is optimistic
  responsiveness. In view 0 it proposes its input.
* **View change.**
  * Echo (rule b): if several views have `f + 1` messages above the highest view-change message
    sent, the node echoes the highest; the paper does not fix an order. The counterexample never
    has two candidates at once.
  * Entering (rule c): the node moves to the highest view with `n − f` view-change messages,
    if it is higher than the current view (views never decrease).
  * Timer: fires once, `timeout` ticks after the view started, and then broadcasts
    `⟨view-change, v+1⟩` unconditionally, as in the paper.
* **One step** runs: receive, echo, view change or timer, propose, vote-1, vote-2, vote-3, vote-4,
  decide. Decisions are taken only in the current view, as in §3.2 step 7. The decision records
  its view as a ghost field.
* **Validity** is the paper's (Definition 1): no faulty node and a common input
  (`paperValidity` as a CSLib `ValidityProperty`).
* **Timing constants.** In discrete time each hop costs `δ + 1` ticks (delay plus the processing
  tick). So the within-view bound is `6(δ + 1)` and the repaired protocol needs `T ≥ 8δ + 9`.
  This corresponds to the paper's 2Δ + 6Δ < 9Δ.

## 3. Not formalized

* Multi-shot TetraBFT (Section 6, Theorem 2), see 1.7.
* Complexity claims: constant storage, `O(n²)` communication, the efficiency of Algorithms 4/5,
  latency 5δ (good case) and 7δ (with a view change).
* The TLA+ liveness argument of Appendix B.
* A repaired protocol for the lossy model (retransmission); see 1.1.
