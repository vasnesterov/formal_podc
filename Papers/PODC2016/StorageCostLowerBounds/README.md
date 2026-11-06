# Storage-Cost Lower Bounds for Shared Memory Emulation — PODC 2016

Viveck R. Cadambe, Zhiying Wang, Nancy Lynch. *Information-Theoretic Lower Bounds on the Storage Cost
of Shared Memory Emulation.* PODC 2016. DOI
[10.1145/2933057.2933118](https://doi.org/10.1145/2933057.2933118). Formalized version: arXiv
[1605.06844](https://arxiv.org/abs/1605.06844) v2; numbering follows it.

**Verdict: ❌ Intent lost.** The paper claims bounds that make "no assumption on the structure of the algorithm", but
with reliable FIFO channels, also in the paper's I/O-automaton reading, a gossip-free, atomic, live *streaming relay*
with 36 states per server, independently of `|V|`, keeps the value in the reader's incoming channels and refutes all
six bounds (Theorems 4.1, 5.1, B.1 and Corollaries 4.2, 5.2, B.2). The proofs assume, without saying so, that servers
never send messages to an idle reader; with that assumption added (`ReaderQuiet`), Theorem 4.1, Corollary 4.2 and the
Singleton-type Theorem B.1 without gossip hold, and no bound with gossip is proved. Theorem 6.5 and non-FIFO channels
were not checked.

## Mistakes in the paper

### ❌ Theorems 4.1, 5.1, B.1 and Corollaries 4.2, 5.2, B.2 (storage lower bounds, FIFO channels)
All six bounds are false with reliable FIFO channels: a gossip-free, atomic, live *relay* emulation keeps the value in the reader's incoming channels, so its servers need only constant state (1 state, or 36 in the I/O-automaton version), independently of `|V|` (`not_theorem41`, `not_theorem41_ioa`, `relay_counterexample`, `stream_counterexample`).

**Impact.** The paper's main results fail as stated. They hold under the unstated assumption that servers never
send to an idle reader (`ReaderQuiet`): Theorem 4.1, Corollary 4.2 and the counting form of Theorem B.1 without
gossip are proved then. Non-FIFO and multi-reader versions are not refuted.

**Details.** The storage cost counts only server states. Channels and client states are free. Here is the
*relay algorithm* for `2f < n` and any value set `V`.
- Write number `t` with value `v` sends `W t v` to all servers. It returns after `n − f` acks.
- A server that receives `W t v` forwards `F t v` to the reader and acks `A t` to the writer. A
  server that receives the read query `Q j` answers `D j`. Its local state never changes.
- The reader always records the largest write index it has seen in an `F` message, with its
  value. Read `j` sends `Q j` to all servers. It returns the recorded value after `n − f` answers
  `D j`.

By FIFO, when the reader gets `D j` from a server, it already got every `F` that server sent earlier. Quorum
intersection then gives regularity, in fact atomicity. Liveness holds with up to `f` server crashes and any client
crashes. There is no gossip, and `|S_i| = 1` for every server. So the left-hand sides of all six bounds are 0
while the right-hand sides are positive. Lean instance: `n = 5`, `f = 2`, `V = Fin 4`. The theorems assume
regularity, so the counterexample is more than they need. (`not_theorem41`, `not_corollary42`, `not_theorem51`,
`not_corollary52`, `not_theoremB1`, `not_corollaryB2`; the algorithm: `relay_counterexample`)

Where the proofs break: in Section 4.3.1 "the readers and the channels from and to the readers do not perform any
actions" during `α`, and Lemma 4.8(a) concludes that reader channels are the same at both critical points. If a
server sends to the reader during `α`, the write cannot complete without that channel taking the message. Then the
reader-side state at `Q₁, Q₂` is not determined by the server states, and Claim 4.9 fails. Appendix B
(Theorem B.1) has the same gap: "all channels are empty" ignores what the live reader already received. This is a
false statement, not a proof gap.

*I/O-automaton reading (formalized).* In the multi-send relay above, one server step receives `W t v` and sends two
messages. In the paper's I/O-automaton model each send is a separate output action, so a server would have to
store the pending `F t v`. The *streaming relay* (`Stream.lean`) respects this restriction (`IOASends`: an input
step of a server sends nothing, a spontaneous step sends at most one message).
- The writer streams the bits of its values to each server, one bit at a time, waiting for an
  acknowledgement before sending the next bit.
- A server's state is (pending bit, pending ack, pending answer, turn), 36 states in all. Its
  spontaneous steps take turns forwarding the bit to the reader, acknowledging, and answering
  queries.
- The reader reassembles `B`-bit blocks per server and keeps the newest complete one. It sends
  one outstanding query per server and re-queries after a stale answer.

It is proved atomic, live (`2f < n`) and gossip-free. With `n = 5`, `f = 2`, `V = Fin 16 → Bool` (`|V| = 2^16`), all
six bounds fail for it. (`not_theorem41_ioa`, `not_corollary42_ioa`, `not_theorem51_ioa`, `not_corollary52_ioa`,
`not_theoremB1_ioa`, `not_corollaryB2_ioa`; the algorithm: `stream_counterexample`)

*Scope.* Both counterexamples need FIFO channels. The paper says only "reliable, asynchronous", and reliable FIFO
is the standard channel of Lynch's I/O-automaton framework, which the proofs use. They also use the theorems'
*single* reader. See **Not formalized.** below for the other channel and reader settings.

**Repair.** Theorem 4.1 holds when servers do not push to an idle reader. We add `ReaderQuiet`: if the reader
takes no step, no server has sent it anything. It follows from "servers send to the reader only when processing a
reader message" (`readerQuiet_of_repliesOnly`), which ABD-style algorithms satisfy. With it, the paper's proof
goes through. We prove `|V|(|V|−1) ≤ (∏_{𝒩}|S_i|)·∑_{𝒩}|S_i|` for every `𝒩` of at least `n − f` servers, which is
slightly stronger than the paper's `∏·(N−f)·max`. We also prove the logarithmic form, Corollary 4.2, and the
counting form `|V| ≤ ∏_{𝒩}|S_i|` of the Singleton-type Theorem B.1 without gossip. (`theorem41_count`, `theorem41`,
`corollary42`, `theoremB1_count`)

### ❌ Theorem 5.1, proof (Definition 5.3, Section 5.3.2)
Definition 5.3 "delivers all messages" between servers, but with gossip this need not terminate, and at `R₂` the
servers other than `s, s'` also receive messages that `s, s'` send during delivery, so they need not be in the same
state as at `R₁`, and the claim that all channels are empty is unjustified (also in Appendix B.3).

**Impact.** This step is broken independently of the reader issue, and no version with gossip is proved: our repair
of Theorem B.1 needs `NoGossip` for the same reason. With FIFO channels the statement is false anyway. This gap is
not formalized.

### ✏️ Slips
- Lemmas 4.4/4.6 (writer-crash step assumes lossy channels from crashed clients): after a critical point, the
  valency executions delay the writer's messages "indefinitely", justified as "indistinguishable from a fair
  execution where the write client fails before sending the messages", but those messages were already sent. With
  channels reliable even from crashed processes, liveness does not guarantee the read terminates, so the step needs
  channels from crashed processes to be lossy. Our model (CSLib `ChannelFailures`) does not require them to deliver,
  which matches the paper's use (`exists_canon_ret`, `exists_crit`).
- `N − f ≥ 1` is implicit (we assume `f < n`).
- The definition of critical points (Lemmas 4.6, 5.6, Definitions 4.7, 5.7) ranges over `{0, 2, …, M−1}` instead of
  `{0, 1, …, M−1}`.

### Typos
- The hypothesis `f ≥ 2` of Theorem 4.1 is never used. The counting argument works for every `f`, and
  Corollary 4.2's total-storage bound needs only `f ≥ 1` (we assume `1 ≤ f < n`).
- In Theorem 4.1's proof, Case II says the read in `γ` "should return `v₂`" because `Q₂` is 2-valent. It
  actually follows from Lemma 4.5 together with `Q₂` not being 1-valent.
- `P₁ = P^{(v₁,v₁)}` in Section 4.3.2 should be `P^{(v₁,v₂)}`, and "Definition 6.8" in Case (II) of Theorem 5.1
  should be Definition 5.3.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing, CSLib/Podc `Cslib.ChannelFailures`: deterministic processes,
  reliable **FIFO** channels, and a step receives one message (or is an invocation or a spontaneous
  tick) and sends any list of messages. The I/O-automaton restriction for servers is the predicate
  `Stream.IOASends`. Client states are not counted, so clients may buffer outputs for free. Nodes: `n` servers, one writer, one reader (`Node n`). The
  object is CSLib's `register V v₀`. The environment is SWSR (`EvOk`).
* Crash failures are not events. A crashed process takes finitely many steps, and channels out of a
  crashed process need not deliver. Fairness: correct processes step infinitely often, and channels
  between correct processes deliver everything.
* Safety `IsRegular` is Lamport regularity of every finite execution, via a reads-from index per
  read. `IsAtomic` is CSLib linearizability.
* Liveness `Live A f` is the paper's: in every fair execution with at most `f` server failures and
  any number of client failures, every operation of a non-crashed client returns.
* Storage: `StateBound A S` says server `i`'s state always lies in the finite set `S i`. Cost is
  `log₂|S i|`, with `maxStorage` and `totalStorage`.
* `NoGossip` says servers never send to servers (Theorem 4.1's hypothesis). `ReaderQuiet` is our
  repair hypothesis.
* Only deterministic algorithms are covered (the paper allows nondeterministic IOAs). The
  counterexample is deterministic, so the refutation is unaffected.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.1 as stated: **false** | `not_theorem41` (statement `Theorem41`) | `Refutation.lean` |
| Corollary 4.2 as stated: **false** | `not_corollary42` | `Refutation.lean` |
| Theorem 5.1 / Corollary 5.2 as stated: **false** | `not_theorem51`, `not_corollary52` | `Refutation.lean` |
| Theorem B.1 / Corollary B.2 as stated: **false** | `not_theoremB1`, `not_corollaryB2` | `Refutation.lean` |
| The counterexample: atomic, regular, live, no gossip, 1 state per server | `relay_counterexample` (`Relay.isAtomic`, `Relay.isLive`) | `Refutation.lean`, `RelayInv.lean`, `RelayLive.lean` |
| Theorems 4.1, 5.1, B.1, Cor. 4.2, 5.2, B.2 false for I/O-automaton-style algorithms (36 server states) | `not_theorem41_ioa`, `not_corollary42_ioa`, `not_theorem51_ioa`, `not_corollary52_ioa`, `not_theoremB1_ioa`, `not_corollaryB2_ioa` | `RefutationIOA.lean` |
| the streaming relay: atomic, live, no gossip, `IOASends`, 36 states | `stream_counterexample` (`Stream.isAtomic`, `Stream.isLive`, `Stream.ioaSends`) | `RefutationIOA.lean`, `StreamSafe.lean`, `StreamLive.lean` |
| the relay algorithm violates the hidden assumption | `relay_not_readerQuiet` | `Refutation.lean` |
| Theorem 4.1, repaired (counting form) | `theorem41_count` | `Theorem41.lean` |
| Theorem 4.1, repaired (log form) | `theorem41` | `Corollary42.lean` |
| Corollary 4.2, repaired | `corollary42` | `Corollary42.lean` |
| Theorem B.1, repaired (counting form, no gossip) | `theoremB1_count` | `Theorem41.lean` |
| Lemma 4.5 / 4.4, 4.6, 4.8 / Claim 4.9 | `read_value` / `exists_crit` / `agree_of_loc`, `readExt_of_agree` | `Theorem41.lean` |
| sufficient condition for `ReaderQuiet` | `readerQuiet_of_repliesOnly` | `Theorem41.lean` |

**Not formalized.**
* Section 6 (Theorem 6.5, multi-version bound under protocol assumptions). Whether the reader-channel flaw affects it
  was not examined.
* A repaired Theorem 5.1 with gossip.
* Non-FIFO channels. We have no counterexample for them: there the adversary could hold back the forwarded messages
  while a valency read runs, so the bounds may well hold, although the written proofs still ignore server-to-reader
  messages.
* Multi-reader versions. The counterexamples use the theorems' *single* reader. They would extend to any fixed finite
  set of readers (forward to each; not formalized), but not to the "possibly infinite" set of read clients of
  Section 3, so multi-reader versions of the bounds are not refuted.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexample's atomicity is proved with CSLib's SWSR reads-from criterion
(`SWSRReadsFrom.isLinearization`). Its liveness is proved over fair infinite executions.
Non-vacuity of the repaired hypotheses: a single-server register (`n = 1`, `f = 0`, `|V|` server states) is proved atomic, live, gossip-free and `ReaderQuiet` (`Witness.witness_hyps`, `nonvacuous_hyps`, `nonvacuous_theorem41` in `Witness.lean`, `NonVacuity.lean`). Non-vacuity for `f ≥ 1` would need a bounded-state ABD-type algorithm and is not formalized. Infrastructure staged in `Podc/`:
`ChannelFailures/Steps.lean` (well-formed histories, pending accounting, step locality,
`exists_canon_ret`: from liveness to a finite canonical extension) and `ChannelFailures/Delivery.lean`
(`Algorithm.Fair.delivered`: eventual FIFO delivery). Both are CSLib candidates.
