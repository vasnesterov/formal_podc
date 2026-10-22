# Distributed Computations in Fully-Defective Networks — PODC 2022

Keren Censor-Hillel, Shir Cohen, Ran Gelles, Gal Sela. *Distributed Computations in Fully-Defective Networks.*
PODC 2022. DOI [10.1145/3519270.3538432](https://doi.org/10.1145/3519270.3538432). Formalized version: the PODC
paper, with the proofs of the full version arXiv [2205.11148](https://arxiv.org/abs/2205.11148) v1. Numbering
follows the PODC paper; arXiv numbers in brackets.

**Verdict: ✅ Correct.** The simple-cycle simulator (Algorithm 1, Theorem 4, Lemma 5, [Theorem 6]) is proved
correct: safety, liveness under fair scheduling, no starvation and quiescence. The two-party impossibility
(Theorem 3) holds as stated. Robbins cycles exist exactly in the 2-edge-connected graphs.
For the Robbins-cycle simulator (Algorithm 3, Theorem 6 [Theorems 10, 12]), safety and deadlock freedom
are proved: single token holder, global consistency, consistent rotations, and the simulation of `π`. Its
liveness under fairness is not formalized, nor are the distributed construction of the Robbins cycle
(Section 5), the binary encoding and the complexity bounds; so the main Theorem 2 is only partly verified.
We found no mistakes. The paper's proofs are informal, real-time inductions over epochs; the formal proofs need
some invariants that the paper uses without stating them.

## Mistakes in the paper

None found. Three points are only implicit in the paper and needed real work:

* **Why the token is caught (Lemma 5(1)).** The paper says the token travels "until it reaches a node `v` with a
  non-empty `Q_v`, which must exist". Two invariants make this precise. First, a request pulse of the current
  token phase implies a node with a non-empty queue: the initiator keeps its message until it captures the token.
  Second, the released token has not passed such a node. Together they bound the token's hops by `n`. (`Inv2`,
  `progress_step`)
* **Lemma 11 [full version] is a sketch** ("we can now repeat the proof of Lemma 5"). The formal invariant
  for Algorithm 3 needs facts the sketch does not mention. The token always lies in segment 0 of every node
  (`RobbinsSim.Inv.rot`; the paper states this one). At most one token, data or end pulse is in transit, and the
  ghost variable `wv` names its channel. A node still in its data phase cannot read a request pulse of the next
  epoch at its occurrence 0 (`RobbinsSim.EndStage.read`).
* **Implicit model conventions.** Several conventions are only implicit. A `wait until` is a blocking receive:
  pulses from other directions stay buffered. Unary payloads must be positive. Fairness is needed for liveness.
  Theorem 3's proof also needs a fair execution to exist; we prove that a round-robin schedule gives one
  (`TwoParty.Protocol.rr_isFairExec`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Network.** Asynchronous; every channel is fully defective, so only the existence of a message matters and a
  link is a pair of pulse counters. Channels are not FIFO.
* **Nodes.** Deterministic. A `wait until` is a blocking receive on the named direction or edge.
* **Robbins cycles.** For Algorithm 3, a node reads one pulse at a time from a channel it waits on. Channels are
  counters per ordered pair. A node's rotation is stored as the position of its occurrence 0.
* **Rings.** Algorithm 1 runs on the oriented ring `ZMod n`, for every `n ≥ 1`, including `n = 1, 2`. A node
  knows its two neighbours.
* **The simulated protocol `π`** (`Protocol.lean`): deterministic, event-driven and asynchronous; it may send to
  any node. It is a black box. Every message delivered to `π` is processed after an arbitrary delay, and its
  outputs are enqueued at once. Messages are encoded by any injective map into the positive integers (unary
  lengths).
* **Simulation.** At every reachable configuration of the simulator there is a reachable configuration of `π`
  over the noiseless network with the same states and the same local transcripts at all nodes. Its in-transit
  messages are exactly those sent but not yet processed.
* **Liveness.** Executions are infinite (stutters allowed) and weakly fair: every node step, and every `π`
  processing step, that stays enabled is eventually taken. In such executions every message sent by `π` is
  eventually processed. A round-robin scheduler is weakly fair, so the hypotheses are satisfiable.
* **Theorem 3.** Two deterministic event-driven parties with any message alphabet. The adversary rewrites every
  delivered message. Executions are fair; outputs are irrevocable.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 1 (ring layer) | `Cycle.Phase`, `Cycle.onCW`, `Cycle.onCCW`, `Cycle.next` | `Cycle/Model.lean` |
| Lemma 5 safety: invariant | `Cycle.Inv`, `Cycle.Reach.inv` | `Cycle/Invariant.lean` |
| Lemma 5(2) single token holder | `Cycle.Inv.tok_unique` | `Cycle/Invariant.lean` |
| Lemma 5(3) global consistency | `Cycle.Inv.log_prefix` | `Cycle/Invariant.lean` |
| Lemma 5(1) progress | `Cycle.Inv.enabled_or_quiet`, `Cycle.progress_step`, `Cycle.rank_progress`, `Cycle.epoch_completion` | `Cycle/Progress.lean`, `Cycle/Liveness.lean` |
| Theorem 4 / [Thm 6], correctness (packaged) | `Cycle.theorem4` | `Cycle/Liveness.lean` |
| Theorem 4 / [Thm 6], safety | `Cycle.simulation` | `Cycle/Simulation.lean` |
| Theorem 4 / [Thm 6], liveness | `Cycle.liveness` | `Cycle/Liveness.lean` |
| [Thm 6], quiescence | `Cycle.quiescence`, `Cycle.quiescence_simulation` | `Cycle/Liveness.lean` |
| [Remark 2] no starvation | `Cycle.no_starvation` | `Cycle/Liveness.lean` |
| Non-vacuity: a fair execution | `Cycle.roundRobin_fair` | `Cycle/Liveness.lean` |
| Theorem 3 [Thm 20] | `TwoParty.Protocol.theorem3`, `TwoParty.Protocol.theorem3_strong` | `TwoParty.lean` |
| Remark before [Thm 20] | `TwoParty.estimateProtocol_stabilizes` | `TwoParty.lean` |
| Robbins cycles exist iff 2-edge-connected | `RobbinsCycle.exists_of_bridgeless`, `RobbinsCycle.nonempty_iff` | `Robbins.lean` |
| Algorithm 3 (network layer on a Robbins cycle) | `RobbinsSim.react`, `RobbinsSim.next` | `Robbins/Model.lean` |
| Lemma 11 [full version] safety: invariant | `RobbinsSim.Inv`, `RobbinsSim.Reach.inv` | `Robbins/Invariant.lean`, `Robbins/Preservation.lean` |
| Lemma 11(2) single token holder | `RobbinsSim.Inv.tok_unique` | `Robbins/Preservation.lean` |
| Lemma 11(3) global consistency | `RobbinsSim.Inv.log_prefix`, `RobbinsSim.Inv.log_eq` | `Robbins/Preservation.lean` |
| Token in segment 0 (Challenge 1) | `RobbinsSim.Inv.rot` | `Robbins/Preservation.lean` |
| Theorem 6 [Thm 12], safety | `RobbinsSim.simulation` | `Robbins/Simulation.lean` |
| Deadlock freedom (Algorithm 3) | `RobbinsSim.Reach.deadlock_free` | `Robbins/Deadlock.lean` |

All names are in the namespace `Podc.FullyDefective`.

**Not formalized.** These parts are not formalized:
* liveness and no starvation of Algorithm 3 under fairness (only deadlock freedom is proved);
* the binary encoding (Algorithm 2, Lemmas 8–9), which was only model-checked;
* all communication-complexity bounds (`CC_init`, `CC_overhead`, Lemmas 7, 9, 13, 14, 19);
* the distributed construction of a Robbins cycle (Section 5: Algorithms 4–6, Theorem 15);
* the reduction from networks with a bridge to Theorem 3;
* [Remark 1] (the derived noiseless scheduler is FIFO; our noiseless model is non-FIFO) and [Remark 3] (broadcast).

Hence Theorem 2 is covered only for a given Robbins cycle, not for the preprocessing phase.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: a weakly fair execution of the simulator exists (`Cycle.roundRobin_fair`), and so does a fair
two-party execution (`TwoParty.Protocol.exists_fairExec`); there is a concrete Robbins cycle
(`triangleRobbinsCycle`). Before the proofs, we model-checked Algorithms 1, 2 and 3 exhaustively on small rings
and Robbins cycles. This includes repeated edges and nodes with three occurrences. No violation was found. The
checkers are in [`modelcheck/`](modelcheck/) and are not part of the Lean development. The content-oblivious model
is new: CSLib's `ContentOblivious` rings have two ports per node and nodes that act only on start-up or on
consuming a pulse, while the simulators need environment events (`π` enqueues messages at any time),
spontaneous steps (line 1 fires on a non-empty queue) and, for Robbins cycles, arbitrary degree.
CSLib candidates: `Protocol.lean` (generic asynchronous protocol with transcripts) and Robbins' theorem in
orientation form with its helpers (`exists_strongOrientation`, `exists_closed_chain`, `reachable_of_steps` in
`Robbins.lean`).
