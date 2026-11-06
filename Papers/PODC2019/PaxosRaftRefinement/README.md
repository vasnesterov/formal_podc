# Paxos vs. Raft, and porting optimizations — PODC 2019

Zhaoguo Wang, Changgeng Zhao, Shuai Mu, Haibo Chen, Jinyang Li. *On the Parallels between Paxos and
Raft, and how to Port Optimizations.* PODC 2019. DOI
[10.1145/3293611.3331595](https://doi.org/10.1145/3293611.3331595). Formalized version: the extended
version with Appendices A–C (TLA+ specifications and the refinement proof).

**Verdict: ⚠️ Weakened.** The first half of the paper holds for a repaired Raft*: a Raft variant whose leader adopts
the voters' extra entries refines repaired MultiPaxos under the Appendix C mapping, so it is safe, though this takes a
new inductive invariant. The porting guarantee, the other half, is proved only for single-step refinements (the
general theorem of Section 4), which excludes the multi-step Raft* refinement, and the ported protocols Raft*-PQL and
Raft*-Mencius were not checked. The printed protocols are unsafe, and short local changes repair them.

## Mistakes in the paper

### ❌ Section 4.3 applied to Raft* (porting Paxos optimizations to Raft* "with guaranteed correctness")
The correctness argument for ported optimizations assumes single-step refinement (`b_j ⇒ a_i`), but the Raft* → Paxos refinement is multi-step (one `AppendEntries` is several `Phase2a`/`Phase2b` steps).

**Impact.** The abstract's claim that optimizations port from Paxos to Raft "with guaranteed
correctness" is unestablished for Raft*, whose refinement of Paxos the paper itself proves only
multi-step (Appendix C 2.4/2.5); Raft*-PQL and Raft*-Mencius are neither proved nor refuted (not
formalized). The general theorem of Section 4.3 is true (`port_correct`). For
multi-step refinements, evaluating the added clauses at the end points is unsound in general
(`naive_multistep_port_unsound`).

### 🔧 TLA+ module MultiPaxos, `theorem Invariance` (Appendix B.1)
With 3 acceptors and majority quorums the spec reaches a state where one ballot has two proposals and both `TRUE` and `FALSE` are chosen at index 0, violating `OneValuePerBallot`, `Inv` and agreement (`tla_invariance_false`).

**Impact.** The paper's formal MultiPaxos is unsafe, and its stated invariance theorem is false.
The pseudocode MultiPaxos (Figure 1) has the same flaw. A repaired MultiPaxos is safe (`safety`).

**Details.** `Propose(a, i, v)` records nothing in `logs[a]`. So a leader may propose `TRUE` and then `FALSE`
for the same index in the same ballot. Then `{a0, a2}` accepts one value and `{a1, a2}` the other.
The grey comment "⇒ v is safe at i, b" does not help: both values are safe at ballot 1.
Figure 1's `Phase2a` also records nothing.

**Repair.** In `Paxos.lean`, a proposal per instance and ballot is recorded. Safety is proved in
`chosenAt_agree` and `safety`.

### 🔧 Appendix B.1, `Phase1b` and `BecomeLeader` (two leaders of one ballot)
1b messages are not addressed to the proposer, so two acceptors can become leaders of the same ballot from the same
1b messages (`tla_two_leaders_same_ballot`).

**Impact.** This breaks the spec independently of the previous item; the repaired MultiPaxos is safe (`safety`).

**Repair.** `Phase1Succeed` needs the proposer's own report.

### 🔧 Figures 1 and 2 (leadership guards)
The pseudocode lacks leadership guards: Figure 1's `Phase1a` does not reset `phase1Succeeded`, and `Phase1Succeed` and
`BecomeLeader` can re-run, which in Figure 2 can shrink `lastIndex`.

**Impact.** The repaired protocols are safe (`safety`, `raftStar_commitSafe_raftVote`).

**Repair.** In `Paxos.lean`, `Phase1a` resets leadership and `Phase1Succeed` needs `¬leader`; `BecomeLeader` in
`RaftStar.lean` is guarded in the same way.

### 🔧 Figure 2, `ReceiveVote` (lines 9–11, the vote rule)
Because a voter compares its entry *at the candidate's last index* (not its last entry) with the candidate's last term, it can vote for a candidate behind it, and a committed entry is overwritten (`fig2_not_commitSafe`; key step `fig2_voter_reports_higher_term`).

**Impact.** Raft* as printed is unsafe and refines no safe Paxos. Step 4.2 of Appendix C is false
for it. The fix is local: Section 3 says Raft* is "identical to Raft" except for two differences
unrelated to voting, and the TLA+ spec B.2 and Raft compare the voter's *last* entry, and with that
rule the refinement holds (`raftStar_commitSafe_fig2Fixed`).

**Details.** The run uses five servers; every `AppendEntries` carries a value:
1. `A` writes `x@1` only to itself.
2. `C` writes `y@2` only to itself.
3. `A` is re-elected in term 3, appends `z@3`, replicates `[x@1, z@3]` to `B, D, E` and commits `x`
   at index 0.
4. `C` (log `[y@2]`) runs in term 4. `B, D, E` vote for it: their entry at index 0 has term
   `1 < 2`, although their last term is `3`.
5. `C` keeps `y` at index 0 and commits it.

### 🔧 Figure 2, `AppendEntries` with no new value (heartbeats)
Figure 2 does not exclude `vals = []`, and with empty appends Raft*'s commit rule loses committed entries in Raft's "Figure 8" scenario, even with Raft's own vote rule (`heartbeat_not_commitSafe`).

**Impact.** Section 3 says re-stamping ballots makes Raft's §5.4.2 rule unnecessary. That holds
only if every append carries an entry of the leader's term. The TLA+ spec B.2 always appends one
value, and under that assumption the refinement holds (`refinement_repaired`).

### ✏️ Slips
- Figure 3 maps `instance.bal` to the per-entry `bal` field, which gives no refinement even for repaired Raft* (scenario
  in [differencies.md](differencies.md), in prose only). The intended mapping is in Section 3 and Appendix C, and the
  refinement is proved for it (`refinement`).

## Proof gaps (statements true)

### 🛠️ Appendix C, steps 2.3 and 4.2 (`BecomeLeader ⇒ Phase1Succeed`)
Step 4.2 ("the leader's entries are already the safe entries") has no argument.

**Impact.** For the repaired Raft* the step holds (`sim_becomeLeader`).

**Details.** Step 4.2 needs a real inductive invariant of Raft* (`Raft.Inv`, 18 clauses):
- log matching;
- one candidate with a quorum of votes per term;
- a candidate's log is its own vote;
- voters' last terms are at most the candidate's;
- every entry is a proposal of its term and of its log's last term.

### 🛠️ Appendix C, step 2.5 (`ReceiveAppend ⇒ Phase2b`)
Step 2.5 maps only the new entries, although under the mapping a follower re-accepts its *whole* log in the leader's
term, and it ignores the follower's `commitIndex` update.

**Impact.** For the repaired Raft* the step holds (`sim_receiveAppend`).

**Details.** The commit update maps to Paxos `Learn` steps. Showing that committed entries are never
overwritten needs MultiPaxos safety itself, so the refinement and the invariant are proved together
(`inv_and_reachable`). Raft* never truncates: a replaced entry is a Paxos acceptance in a higher
ballot.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous message passing. Every message ever sent stays in a set, so messages may be lost,
  duplicated and reordered.
- Crash-stop servers: a crashed server takes no further steps. No timing assumptions,
  deterministic protocols.
- Any intersecting quorum system; majorities are `QuorumSystem.majority`.
- Interleaving transition systems for MultiPaxos (`Paxos.lean`, Figure 1 repaired) and Raft*
  (`RaftStar.lean`, Figure 2 parametrised by the vote rule and by whether heartbeats are allowed).
- Ghost history variables record the implied Paxos `accept`/`acceptOK` messages.
- The mapping is Appendix C's: ballot = term, `phase1Succeeded` = `isLeader`, the accepted ballot
  of every entry is the term of the *last* entry, `chosenSet` = committed prefix.
- Figure 3's per-entry `bal` mapping does not give a refinement even for repaired Raft* (scenario
  in `differencies.md`, not formalized). The repaired Raft* needs no `bal` field.
- The refinement theorem covers every vote rule that never lets a server vote for a candidate with
  a smaller last term. This includes Raft's rule, the index-fixed Figure 2 rule and the permissive
  "last term ≤".

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| MultiPaxos is safe (assumed in §4.1; TLA+ B.1 `Invariance`, repaired) | `Paxos.safety`, `Paxos.proposal_eq_of_chosenAt` | `PaxosSafety.lean` |
| App. C: every Raft* step implies Paxos steps | `refinement_step` | `Refinement.lean` |
| App. C: Raft* is a refinement of Paxos | `refinement`, `refinement_repaired` | `Refinement.lean` |
| §3: Raft* is correct (state machine safety) | `raftStar_commitSafe`, `raftStar_commitSafe_raftVote`, `raftStar_commitSafe_fig2Fixed` | `Refinement.lean` |
| Invariants behind step 4.2 | `Raft.Inv`, `Raft.Inv.step` | `RaftInv.lean` |
| Fig. 2 as printed is unsafe | `Raft.fig2_not_commitSafe`, `Raft.fig2_voter_reports_higher_term` | `Counterexamples.lean` |
| Fig. 2 with heartbeats is unsafe | `Raft.heartbeat_not_commitSafe` | `Counterexamples.lean` |
| TLA+ B.1 `Invariance` is false | `TLA.tla_invariance_false`, `TLA.tla_two_leaders_same_ballot` | `TLAMultiPaxos.lean` |
| §4.2: `A∆` refines `A` | `Porting.Opt.refines` | `Porting.lean` |
| §4.3: `B∆` refines `A∆` and `B` | `Porting.port_refines_opt`, `Porting.port_refines_base`, `Porting.port_correct` | `Porting.lean` |
| §4.3 recipe fails for multi-step refinements | `Porting.naive_multistep_port_unsound` | `Porting.lean` |

**Not formalized.** The TLA+ module Raft* (B.2), PQL, Mencius and their Raft* ports (B.3–B.6,
Appendix A), the classification of Paxos variants (Fig. 6), and the evaluation. The `ProposeEntries` of B.2 also
records nothing in the leader's log, so its `Invariance` very likely fails the same way as B.1's; not checked.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity:
- repaired Raft* commits entries (`Raft.repaired_commits`);
- MultiPaxos chooses values (`Paxos.exists_reachable_chosen`).

Self-contained models; only Mathlib is used.
