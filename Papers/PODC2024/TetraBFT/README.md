# TetraBFT — PODC 2024

Qianyu Yu, Giuliano Losa, Xuechao Wang. *TetraBFT: Reducing Latency of Unauthenticated, Responsive
BFT Consensus.* PODC 2024. DOI [10.1145/3662158.3662783](https://doi.org/10.1145/3662158.3662783).
Formalized version: arXiv [2405.02615](https://arxiv.org/abs/2405.02615) v2 (April 2026); its
numbering is the same as v1's.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Termination (liveness after GST) in Theorem 1 is false for the
protocol as specified. After GST the view change can deadlock forever, both with reliable channels
(`n = 7`, `f = 2`) and in the paper's lossy pre-GST model (`n = 4`, `f = 1`). Agreement and validity
hold in every run, and we prove that the protocol terminates once its echo rule is repaired.

The statements of Lemmas 2, 4 and 5, the core of the liveness argument, are correct, and so is the
9Δ budget of a view. The safety proof covers Rule 3 item 2(b)iiiB, which the authors' TLA+/Apalache
check does not.

## Mistakes in the paper

* **Theorem 1 (termination) is false: the view change can deadlock forever.** The rule is: on
  timeout, send `⟨view-change, v+1⟩`; on `f + 1` view-change messages for `v'`, send
  `⟨view-change, v'⟩` *"if it has not sent a view-change message for view `v'` or any higher
  view"*; on `n − f` of them, move to `v'`. Timers fire once per view and nothing is resent.
  The guard lets a node that has already echoed a *higher* view refuse to help the others reach
  the view it is itself entering.

  Counterexample (`n = 7`, `f = 2`, Byzantine nodes 0 and 1 lead views 0 and 1, Δ = 1, timeout
  9Δ):
  1. Nodes 2–5 move to view 1 together; node 6's copies of their messages are delayed until
     GST + Δ.
  2. Nodes 2–5 time out in view 1. Node 5 alone reaches view 2, with one Byzantine view-2 message.
  3. Node 5 times out in view 2. Its view-3 message and two Byzantine ones make node 6 echo view 3.
  4. Only then does node 6 receive the view-2 messages, and it enters view 2. Because it has
     already sent view 3, it never sends view 2.
  5. Nodes 2, 3, 4 now see 4 < n − f view-2 messages and 2 < f + 1 view-3 messages forever.

  From time 41 nothing is in transit and no timer is pending, so no correct node ever decides
  (`Deadlock.termination_fails`, with timeout 9Δ; the same schedule rescaled deadlocks with
  timeout 17 = 8δ + 9, the bound of the repair theorem below: `Deadlock17.termination_fails`;
  both runs use reliable channels and satisfy CSLib's `Run.Valid`). The same pattern works for every `f ≥ 2` (informal). If messages before GST may
  be lost, as §2 of the paper allows, `n = 4`, `f = 1` already deadlocks
  (`Lossy.termination_fails_lossy`). That deadlock comes from the lack of retransmission, not
  from the echo guard: the repaired echo rule deadlocks there too.

  The paper never proves view synchronization. The 9Δ timeout justification assumes that every
  node echoes, and the termination proof only cites Lemmas 2, 4, 5, which assume all correct nodes
  are in a good view after GST. Multi-shot TetraBFT (Algorithm 2) has the same guard. The likely
  fix: echo every view `≥` the current one that was not echoed yet (plus retransmission in the
  lossy model). For reliable channels we prove that this repair works: with timeout `T ≥ 8δ + 9`
and round-robin leaders, the repaired protocol solves consensus (`fixed_solvesConsensus`).
* **Proof of Lemma 7 uses a false claim (statement true).** It asserts that once a correct node
  decides `val` in view `v`, every correct vote-1 in view `v` is for `val`. A Byzantine leader
  breaks this: a synchronous run with `n = 4` where correct node 1 decides `true` in view 0 while
  correct node 3 votes vote-1 for `false` in view 0 (`Lemma7.lemma7_proof_claim_false`). Lemma 7
  follows from Lemma 6 instead (`Execution.lemma7`).
* **Proof gaps with true statements.**
  * Lemma 2's proof picks the "last view with a vote-3" among a quorum that may contain
    Byzantine nodes with fake reports. It works when the quorum is the set of correct nodes
    (`Execution.lemma2`).
  * Lemma 4 leaves its hypotheses implicit: a correct leader, and proof messages from all correct
    nodes (`Execution.lemma4`).
  * The validity proof is circular as written. We prove it by induction over time
    (`tetra_validity`).
* **The mechanized check does not cover the paper's rule.** The TLA+ spec (Appendix B) omits Rule 3
  item 2(b)iiiB, and Apalache checked only `n = 4`. Our Lean proof covers the full Rule 3 for all
  `n > 3f`.
* **Typos.** Lemma 8 (d)ii: "either `m` or `m'` satisfies Rule 4 Item 3" should be "neither";
  Section 6's proof says "vote-4 for block `s − 4`" but Fig. 2 gives `s − 3`; plus a few spelling
  slips.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's partially synchronous Byzantine model (`Cslib.Byzantine.PartialSync`). Nodes are
  `Fin n`, at most `f` are Byzantine, and `3f < n`. Channels are authenticated, there are no
  signatures, and Byzantine nodes may equivocate. Time is discrete, and each node takes one
  deterministic step per tick.
* `Run.Valid f δ`: reliable channels, with delivery by `max(send, GST) + δ`.
  `LossyValid` is the paper's model, where pre-GST messages may be lost.
* `tetra prm` (`Protocol.lean`) is §3.2 written as a state machine. It covers timer, echo, view
  change, proof/suggest reports, the proposal (input if Rule 1 shows it safe), vote-1 (Rule 3),
  vote-2/3/4, and the decision. Rules 1–4 are verbatim (`Defs.lean`). Reports come from the full
  vote history; constant storage is not modelled. The flag `prm.fixEcho` switches to the
  repaired echo rule, which is not in the paper.
* Safety is first proved for *abstract executions*. These are the votes cast by correct nodes,
  subject to four guarantees: one vote per phase and view, quorum behind each vote, Rule 3 on
  honest reports, quorum behind a decision. A refinement then shows that every run of `tetra prm`
  is such an execution, with no timing assumption, so safety holds in asynchronous runs too.
* The counterexamples are concrete runs evaluated by `decide +kernel` through a memoised
  simulator (`simHist`, `Cslib/Computability/Distributed/Byzantine/PartialSync/Sim.lean`). A quiescence lemma extends them to infinite time.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `IsReport.claims_of_voted` | `Defs.lean` |
| Lemma 2 (abstract / protocol) | `Execution.lemma2` / `leader_determines_safe` | `Liveness.lean` / `ProtocolLiveness.lean` |
| Lemma 3 | `Execution.lemma3` | `Liveness.lean` |
| Lemma 4 (abstract / protocol) | `Execution.lemma4` / `follower_determines_safe` | `Liveness.lean` / `ProtocolLiveness.lean` |
| Lemma 5 + timing of a view (6 hops of `δ + 1` ticks) | `decides_of_synchronized_view`, `decide_same_of_synchronized_view` | `ViewLiveness.lean` |
| Lemmas 6, 7, 8 | `Execution.lemma6`, `lemma7`, `lemma8` | `Safety.lean` |
| Theorem 1, agreement (abstract / protocol) | `Execution.agreement` / `tetra_agreement` | `Safety.lean` / `Refinement.lean` |
| Theorem 1, validity | `tetra_validity` | `Validity.lean` |
| Theorem 1, termination: **false** (timeout 9 and 17) | `Deadlock.termination_fails`, `Deadlock.not_solvesConsensus`, `Deadlock.views_stuck`, `Deadlock17.*` | `Counterexample.lean` |
| — same, in the paper's lossy model, `n = 4` | `Lossy.termination_fails_lossy` | `Counterexample.lean` |
| Proof of Lemma 7: intermediate claim false | `Lemma7.lemma7_proof_claim_false` | `Counterexample.lean` |
| Repaired echo rule (not in the paper): views synchronize, termination, consensus | `sync_window`, `fixed_termination`, `fixed_solvesConsensus` | `ViewSync.lean` |

**Not formalized.** Multi-shot TetraBFT (Section 6, Theorem 2), which is under-specified. The
complexity and latency claims. A repair for the lossy model (it would also need retransmission).

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`; `decide +kernel` adds none. Non-vacuity: the safety hypotheses are discharged for
every run of the concrete protocol (`toExec_safetyHyp`). The counterexample runs are checked to
be valid, and the Lemma 7 run shows that decisions do happen in the model.
`fixed_solvesConsensus` is instantiated for `n = 4`, `f = 1`, `δ = 1`, `T = 17`.
