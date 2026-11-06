# Differences between the formalization and the paper

Paper: Wang, Zhao, Mu, Chen, Li. *On the Parallels between Paxos and Raft, and how to Port
Optimizations.* PODC 2019, extended version (61 pp., Appendices A–C). The paper describes each
protocol three times, and the three descriptions disagree: pseudocode (Figures 1–3), TLA+
(Appendix B) and the refinement proof (Appendix C). We formalize the protocols the Appendix C proof
talks about (Figures 1 and 2, with the mapping table of Appendix C). We repair them where needed,
taking each repair from another of the paper's descriptions where possible.

## Statement-level issues

1. **TLA+ `theorem Invariance` of module MultiPaxos (B.1, line 177) is false** —
   `TLA.tla_invariance_false`. There are three acceptors and majority quorums. One leader runs
   `Propose(a1, 0, TRUE)` and then `Propose(a1, 0, FALSE)`, since `Propose` records nothing. Two
   quorums then accept, and `OneValuePerBallot`, `Inv` and agreement (`chosen[0] = {TRUE, FALSE}`)
   all fail. The grey comment "⇒ v is safe at i, b" does not help: both values are `SafeAt` ballot
   1 because nothing was voted below it. Independently, two acceptors can become leaders of the
   same ballot, because 1b messages are not addressed (`TLA.tla_two_leaders_same_ballot`).
   **🔧.** The fix (record proposals, address 1b messages) changes the protocol, it is not an index
   or symbol fix. The TLA+ specs are supporting material.
2. **Figure 2 vote rule (lines 9–11)** compares the voter's entry *at the candidate's last index*
   with the candidate's last term. Raft* as printed then loses committed entries
   (`Raft.fig2_not_commitSafe`; isolated step: `Raft.fig2_voter_reports_higher_term`). So the
   printed Figure 2 refines no safe Paxos, and step 4.2 of Appendix C is false for it.
   **🔧.** The fix is local (`s.log[lIndex]` → the voter's last entry), and the intent
   is recoverable from TLA+ B.2 (`Phase1b` uses `raftlogs[a][lastIndex[a]]`) and from Raft. The
   Appendix C proof does not reason with the printed rule; it gives no argument at all for 4.2.
   Raft* (Figure 2) is the paper's main protocol and is unsafe as printed. The intent is stated in
   the paper's own prose: Section 3 says "Raft* is
   identical to Raft, except for two introduced differences" (extra entries in votes, the `bal`
   field), neither of which concerns the vote rule, so Raft's last-entry check is intended; TLA+ B.2
   `Phase1b` uses it too.
3. **Figure 2 allows `AppendEntries` with `vals = []` (heartbeats)**. Then even Raft's own vote rule
   gives Raft's "Figure 8" loss of a committed entry (`Raft.heartbeat_not_commitSafe`). Section 3
   claims that re-stamping ballots replaces Raft's §5.4.2 commit rule, but that only works if every
   append carries an entry of the current term. **🔧.** TLA+ B.2's `ProposeEntries`
   always appends exactly one value, which recovers the assumption. Raft (which Raft*
   claims to equal "except two differences") does send empty `AppendEntries`, so a reader may be
   misled; but read the same way, Raft* would also keep Raft's §5.4.2 commit rule, which makes
   heartbeats safe. Either reading of the paper recovers a safe protocol; recorded here.
4. **Raft*-PQL / Raft*-Mencius "guaranteed correct" (Sections 4.3–4.4, Appendix A)**:
   *unestablished* (**❌**). The Section 4.3 argument needs a single-step refinement (`b_j ⇒ a_i`).
   The Raft* → Paxos refinement is multi-step (Appendix C 2.4/2.5 map one step to "several Phase2a
   steps"). For multi-step refinements, the recipe of conjoining the added clauses at the end points
   is unsound in general (`Porting.naive_multistep_port_unsound`). The ported protocols themselves
   are not formalized, so they are neither proved nor refuted. The abstract presents porting "from Paxos to Raft with guaranteed
   correctness" as a primary contribution, and its proof for Raft* relies on `b_j ⇒ a_i`, which the
   paper's own Appendix C contradicts (one `AppendEntries` = several Paxos steps; "3. Q.E.D. … each
   step of Raft* implies a step of Paxos" is false as stated). Nothing is refuted for
   Raft*-PQL/Mencius.

## Proof gaps of true statements (Appendix C)

5. **Step 2.3 / 4.2** ("`s.instances[0, s.lastIndex]` is already the safe entries") has no
   argument. For the repaired protocol it needs the invariant `Raft.Inv` (`RaftInv.lean`):
   - log matching;
   - at most one candidate with a quorum of votes per term (`Inv.cand_unique`);
   - a candidate's log equals its own vote (`cand_log`);
   - every voter's last term is ≤ the candidate's (`rvok_vote`);
   - every entry is a proposal of its own term and of its log's last term (`entry_props`,
     `last_props`), and proposals of a term come from that term's leader (`props_leader`).
6. **Step 2.5 (`ReceiveAppend ⇒ Phase2b`)** maps only the entries `prev+1 .. prev+|ents|`. Under
   the Appendix C mapping (accepted ballot = term of the last entry), the follower re-accepts its
   *whole* log in the leader's term. This is justified by log matching: the follower's prefix
   equals the leader's, so `Inv.receiveAppend_log` gives that the new log is the leader's log.
   The step ignores the follower's `commitIndex` update, which changes `chosenSet`. We map it to
   Paxos `Learn` steps. Showing that the already committed entries are not overwritten needs
   MultiPaxos safety itself (`PropSafe`, supplied by `Paxos.proposal_eq_of_chosenAt` inside the
   induction, `inv_and_reachable`).
7. **Truncation** (screening question): Raft* never truncates (`s.lastIndex ≤ prev + length(ents)`).
   A replaced entry corresponds to a Paxos acceptance in a higher ballot, never to un-accepting a
   value. This holds in our model.
8. **"Every Raft* step implies a Paxos step or a stutter"** (Section 4.1 and step 3): it is a
   *finite sequence* of Paxos steps (`refinement_step`, batches in `PaxosBatch.lean`). The paper
   itself says so in 2.4/2.5 ("several Phase2a steps").

## Modelling choices and repairs (not mistakes of the paper's results)

- **Mapping.** We use Appendix C's mapping `accBallot ↦ lastLogEntry.Term` for *every* entry.
  Figure 3 maps `instance.bal ↦ entry.bal` (the per-entry `bal` field of Figure 2). With that
  mapping the refinement fails even for repaired Raft*, although safety holds. A candidate keeps its
  entry at index 0 with `bal 1`, while a voter reports a different value at index 0 with `bal 3`,
  so Paxos `safeEntry` would pick the voter's value. Scenario: 5 servers; term 1 writes `x` to
  `C`; term 3 writes `u` to `V`; term 5 extends `C`'s log with prev = 0; `C` then wins term 6 with
  `V`'s vote. This is only in prose, not formalized, because our Raft* has no `bal` field (it is
  behaviourally irrelevant). Recorded as a remark (✏️).
- **Figure 1 (MultiPaxos) repairs** in `Paxos.lean`:
  - `Phase2a` must not propose a second value for the same instance and ballot. As printed it
    records nothing, the same flaw as TLA+ `Propose`.
  - `Phase1a` resets `phase1Succeeded`. As printed a leader keeps leadership after raising its
    ballot; TLA+ `IncreaseHighestBallot` resets it.
  - `Phase1a` sends the proposer's own `prepareOK`, and `Phase1Succeed` requires it and is guarded
    by `¬phase1Succeeded`, as TLA+ `BecomeLeader`.
  - `Phase1Succeed` sets all instances (empty above the largest reported one). The `unchosen`
    optimisation is dropped, as Appendix C does.
  - `Learn` only adds to `chosenSet`; Figure 1 also overwrites the instance with `(b, v)`.
    `acceptOK` messages are readable by every learner, which is the paper's "notify other servers".
- **Figure 2 (Raft*) repairs** in `RaftStar.lean`:
  - `RequestVote` resets `isLeader` and casts the candidate's own vote, which carries its log.
  - `BecomeLeader` needs the own vote among a quorum of votes and is guarded by `¬isLeader`,
    as TLA+ B.2. As printed it can re-run and *shrink* `lastIndex`.
  - Votes carry the whole log (Appendix C 3.5: "we can still assume Raft* includes the full log").
  - `append` messages carry the leader's log; the receiver uses only `prevLen`, `pTerm` and `ents`.
  - `safeEntry` among votes picks a vote with the largest *last term*, matching the mapping.
  - `LeaderLearn` commits any `k` at most the reported lengths. Figure 2 says exactly the minimum;
    allowing more nondeterminism only strengthens the safety result.
  - The vote rule is a parameter (`Rules.voteOK`). The theorem holds for every rule that never lets
    a voter vote for a candidate with a smaller last term (`VoteMono`). This covers Raft's/TLA+'s
    rule (`raftStar_commitSafe_raftVote`), the index-fixed Figure 2 rule
    (`raftStar_commitSafe_fig2Fixed`) and the most permissive rule "voter's last term ≤
    candidate's" (`refinement_repaired`).
  - `commitIndex` is stored as a length (`commit = commitIndex + 1`). Indices are 0-based, as in
    the paper.
- **Ghost variables** `props`/`acks` record the implied Paxos `accept`/`acceptOK` messages, like
  TLA+ `proposedValues`/`votes`.
- **Network and failures**: every message ever sent stays in a set, so loss, duplication and
  reordering are all possible; crash-stop is a server that takes no more steps; quorums are any
  intersecting family. These are the paper's assumptions (Section 2, TLA+).
- **Not formalized**:
  - the TLA+ module Raft* (B.2) — its `ProposeEntries` also records nothing in the leader's log, so
    its `Invariance` very likely fails the same way as B.1's; not checked;
  - PQL, Mencius and their Raft* ports (B.3–B.6, Appendix A);
  - Fig. 6's classification of Paxos variants;
  - the evaluation (Section 5).
- **Section 4 formalization** (`Porting.lean`):
  - Subactions are relations on full states. A modified subaction conjoins an arbitrary clause, and
    an added subaction must leave the variables of `A` unchanged ("non-mutating").
  - The paper's syntactic "does not mutate `Var_A`" for the clauses of *modified* subactions is not
    needed: any conjunct only restricts behaviour.
  - Parameter mappings (`f_args`) are subsumed by letting clauses read the full pre/post states.
  - A stuttering `b_j` keeps the new variables, which the recipe leaves implicit.
