# Differences between the formalization and the paper

Paper: Censor-Hillel, Cohen, Gelles, Sela, *Distributed Computations in Fully-Defective Networks*, PODC 2022;
full version arXiv:2205.11148v1 (used for the proofs). Numbering: conference (Thm 2, 3, 4, Lemma 5, Thm 6 =
Robbins-cycle simulator); arXiv numbers in brackets where they differ (Thm 3 = [Thm 20], conference Thm 6 =
[Thm 10/12], the cycle-simulator correctness = [Thm 6]).

## Scope

- **Formalized.** Algorithm 1 (simple-cycle simulator, unary data phase) with Lemma 5 (safety and progress),
  the simulation theorem [Thm 6] (safety and liveness), Remark 2 (no starvation), quiescence; Theorem 3
  (two-party impossibility); the existence of Robbins cycles in 2-edge-connected graphs (background fact used by
  Section 4) and its converse; Algorithm 3 on a Robbins cycle: safety (Lemma 11 (2), (3), simulation [Thm 12])
  and deadlock freedom, but not liveness under fairness (last section).
- **Not formalized.** The binary encoding (Algorithm 2, Lemmas 8, 9) and all communication-complexity claims
  (`CC_overhead`, `CC_init`, Lemmas 7, 9, 13, 14, 19); the distributed content-oblivious construction of a
  Robbins cycle (Section 5: Algorithms 4–6, Theorem 15, Lemmas 16–18, Remarks 4–6). Consequently Theorem 2 is
  covered only in the form "given a Robbins cycle (which exists), the simulator of Section 4 works"; the
  pre-processing phase is not verified. Algorithm 2 was only model-checked (`modelcheck/alg2.py`, rings of
  1–4 nodes, `L ∈ {2, 3}`, no violation found).
- [Remark 1] (the noiseless scheduler derived from the simulator is FIFO) and [Remark 3] (broadcast) are not
  formalized; our noiseless model is non-FIFO, which the paper says is also covered.
- The reduction "a network with a bridge reduces to the two-party case" (Section 6, one sentence in the paper) is
  not formalized; only the two-party Theorem 3 is.

## Model (all papers' sections)

- **Fully-defective channels** are modelled as pulse counters: a node never sees message contents, so a link is
  the number of pulses sent and received in each direction. This is equivalent to the paper's alteration noise
  for the simulators, which ignore contents. Channels are not FIFO; for indistinguishable pulses this is
  irrelevant.
- **"wait until …"** in the pseudo-code is a blocking receive on the named direction/edge: pulses arriving from
  other directions stay in the incoming buffer (polling semantics). The paper's proofs assume exactly this
  (e.g. "T₁ might get the token pulse before getting a request pulse, in which case it delays its actions").
- **Line 1 ("wait until `Q_u` is not empty or …")** is an explicit step `start u`, enabled while `u` is at line 1
  with a non-empty queue; weak fairness makes it happen.
- **Rings.** Algorithm 1 is formalized on the oriented ring `ZMod n` for every `n ≥ 1`, including the degenerate
  `n = 1` (self-loop) and `n = 2` (double link); the paper assumes a simple cycle (`n ≥ 3`). Node identifiers are
  the ring positions; nodes know their clockwise/counterclockwise neighbours (as in Theorem 4).
- **The simulated protocol `π`** (`Protocol.lean`) is a deterministic event-driven asynchronous protocol whose
  messages may go to any node (the paper: to neighbours in `G`; a special case). Inputs/IDs are folded into the
  per-node functions. Its noiseless executions deliver any in-transit message at any time (non-FIFO).
- **`π` as a black box.** The paper lets `π` act "in parallel" and take arbitrary finite time. We model: delivery
  to `π` (Line 28) appends to an inbox; `π` processes inbox entries one at a time, each after an arbitrary delay
  (a `proc` step), atomically producing its outgoing messages, which are enqueued at once. The receive event of
  the transcript is the processing time. The initial messages of `π` are in the queues at time 0.
- **Encoding.** The unary length of `(m, u, v)` is given by any injective coding `enc : V × V × M → ℕ⁺` with a
  left inverse `dec` (`Coding`; `Coding.ofEncodable` for encodable types). Payloads must be positive: with
  `d = 0` the holder would send its `end` pulse at once and the others would read it as a token pulse.
- **The holder logs its own message.** In Algorithm 1(b) the token holder does not decode; we also append its
  own payload to its log, and deliver it to its own `π` if the destination is itself. This only matters for
  messages a node sends to itself, which never happens for `π` over a simple graph.
- **Simulation (Section 2, "noise-resilient simulator").** Safety (`Cycle.simulation`): for every reachable
  configuration of the simulator there is a reachable configuration of `π` over the noiseless network with the
  same states and the same local transcripts at every node; in addition, the messages in transit there are exactly
  the messages sent by `π` and not yet processed by their destination. The paper states the transcript condition
  for "an execution"; we state it for every finite prefix, which implies the paper's statement for finite
  executions, and add liveness separately. The witness `D` is determined by `C` (states, transcripts and
  `D.net = sent − processed`), but the theorem does not state that the witnesses of successive prefixes are
  reachable from one another (the proof builds them that way); for infinite executions this is the paper's own
  formulation ("simulates a prefix of a valid execution" at any time, plus liveness).
- **Fairness.** Executions are infinite sequences of configurations, each step a simulator step or a stutter
  (`SimExec`); weak fairness (`WeakFair`): every step label (`start u`, reading a clockwise / counterclockwise
  pulse at `u`, `π` processing at `u`) enabled from some time on is eventually taken. This is the paper's "every
  message is eventually delivered" plus "`π` takes finite time". Non-vacuity: the round-robin scheduler is weakly
  fair (`roundRobin_fair`).
- **Liveness** (`Cycle.liveness`): for every time `t` there is a later time by which every message sent by `π`
  by time `t` has been processed by its destination — the simulated noiseless execution is fair. The paper argues
  this informally in the last paragraphs of the proof of [Thm 6].

## Lemma 5

- (1) Progress is proved as `rank_progress` (the system moves token stage → data stage → end stage → next token
  stage unless it is quiet), `epoch_completion` (every node eventually completes every epoch started so far) and
  `Inv.enabled_or_quiet` (deadlock freedom). The paper's "at time `t_k` all nodes are in lines 1, 3 or 8" is the
  token stage of the invariant (`TokStage`).
- The progress proof needs two facts the paper uses without stating them as invariants (`Inv2`): (a) a request
  pulse of the current token phase implies some node with a non-empty queue (the initiator keeps its message until
  it captures the token); (b) the released token has not passed such a node, so it is caught within `n` hops (the
  paper: "until it reaches a node `v` with a non-empty `Q_v`, which must exist").
- (2) Single token holder: `Inv.tok_unique`; the holder clause of the invariant says who holds the token in each
  stage.
- (3) Global consistency: every node's log of decoded payloads is a prefix of the global sequence `ds` of the
  payloads of the started epochs, i.e. every node decodes in epoch `k` the payload sent by `T_k`
  (`Inv.log_prefix`). Of the sent transcript `P_{u,k}` we formalize the clockwise part (one `request` and `d_j`
  data pulses per epoch, `Common.cwS`), not the exact interleaving with the counterclockwise pulses.
- The paper's proof is an induction over epochs with real time; ours is a single inductive invariant over all
  reachable configurations (three stages, pulse counters as functions of local states, a "wave" condition for the
  `end` pulse, uniqueness of the counterclockwise pulse in transit).

## Remark 2 (no starvation)

- Proved (`no_starvation`): a node with a non-empty queue eventually broadcasts the message at its head. The proof
  uses the potential "counterclockwise distance from the current holder to `u`, plus the number of epochs", which
  never increases once a token phase has started with `u`'s queue non-empty (`TokenAhead`, `capture_cdist`).

## Theorem 3 (two-party impossibility)

- Parties are general deterministic state machines over an arbitrary message alphabet; the adversary may replace
  each delivered message by any element of the alphabet. The reduction to pulse counts is proved (the paper says
  "w.l.o.g.").
- "Gives output" = both parties eventually irrevocably output in every fair execution; termination is covered by
  this requirement only and not modelled separately.
- The paper leaves the existence of a fair execution implicit; it is proved (round robin, `rr_isFairExec`).
- The remark that revocable outputs make the problem solvable is proved for the paper's concrete protocol with
  `X = Y = ℕ` (`estimateProtocol_stabilizes`).

## Robbins cycles

- Definition (`RobbinsCycle`): a closed walk `C : ZMod L → V` with consecutive vertices adjacent, through every
  vertex, never traversing an edge in both directions — the paper's definition. Existence for finite, connected,
  bridgeless graphs with at least two vertices (`RobbinsCycle.exists_of_bridgeless`, which also traverses every
  edge) and the converse (`nonempty_iff`). The paper cites Robbins (1939); the proof goes through a strongly
  connected orientation built by ears.

## Algorithm 3 (simulator on a Robbins cycle, Theorem 6 [Thm 10/12], Lemma 11)

- **Proved:** safety (Lemma 11 (2), (3), the token-segment invariant of Challenge 1, the simulation theorem
  [Thm 12] in the same form as for the cycle) and deadlock freedom (`Reach.deadlock_free`: if no step of the
  network layer is enabled, every node idles at line 1 with an empty queue and has decoded every payload, and no
  pulse is in transit). **Not proved:** liveness/no starvation under fairness (Lemma 11(1) beyond deadlock
  freedom), Lemmas 13, 14.
- Channels are counters per ordered pair of nodes; a node reads one pulse at a time from a channel it waits on.
  At lines 1, 8 and the `until` test of line 37 the paper does not restrict the sender; we accept any channel of
  the right direction (clockwise: `x → u` used by the cycle; counterclockwise: `u → x` used by the cycle). The
  direction of a channel is well defined because a Robbins cycle never uses an edge in both directions.
- Occurrences are cycle positions; the numbering of `u`'s occurrences is stored as the position `o` of
  occurrence `0`; `RotateEdges()` is `o ← prevOcc o`. Program points carry occurrence positions instead of
  indices `i`.
- Line 3 ("wait until a request pulse is received on each `prev_{u,i}`") counts request pulses per physical
  channel with multiplicity (several occurrences may share a channel); extra pulses stay buffered and are read at
  line 8.
- Ghost variables `ds`, `τ` (position of the token) and `wv` (the channel of the unique token/data/end pulse in
  transit).
- As for Algorithm 1: unary encoding only; the holder appends its own payload to its log.
- The paper's proof of Lemma 11 is a sketch ("repeat the proof of Lemma 5"); it does not address why a node
  still in its data phase cannot read a next-epoch request pulse at its occurrence `0` (`EndStage.read`). The
  claim is true.
- Model checking (`modelcheck/alg3.py`) on Robbins cycles with up to 5 vertices, repeated edges and nodes with
  3 occurrences found no violation of safety or deadlock freedom.
