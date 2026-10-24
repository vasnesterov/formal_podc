# Storage-Cost Lower Bounds for Shared Memory Emulation — PODC 2016

Viveck R. Cadambe, Zhiying Wang, Nancy Lynch. *Information-Theoretic Lower Bounds on the Storage Cost
of Shared Memory Emulation.* PODC 2016. DOI
[10.1145/2933057.2933118](https://doi.org/10.1145/2933057.2933118). Formalized version: arXiv
[1605.06844](https://arxiv.org/abs/1605.06844) v2; numbering follows it.

**Verdict: ❌ False claim.** With reliable FIFO channels, Theorems 4.1, 5.1, B.1 and Corollaries 4.2,
5.2 and B.2 are false, and this holds in the paper's I/O-automaton reading as well. The Lean
counterexample is the *streaming relay*. Each server step either receives a message and sends
nothing, or sends at most one message, so a server keeps its pending outputs in its state. Every
server has 36 states independently of `|V|`, and the emulation is still atomic, live and
gossip-free. With `n = 5`, `f = 2` and `|V| = 2^16`, all six bounds fail. The value is kept in the
reader's incoming channels. The proofs assume, without saying so, that servers never send messages
to an idle reader. With that assumption added (`ReaderQuiet`), Theorem 4.1 and Corollary 4.2 hold,
and so does the Singleton-type Theorem B.1 without gossip. Theorem 6.5 is not formalized.

## Mistakes in the paper

* **Theorems 4.1, 5.1, B.1 and Corollaries 4.2, 5.2, B.2 are false (FIFO channels).** The storage
  cost counts only server states. Channels and client states are free. Here is the *relay algorithm*
  for `2f < n` and any value set `V`.
  - Write number `t` with value `v` sends `W t v` to all servers. It returns after `n − f` acks.
  - A server that receives `W t v` forwards `F t v` to the reader and acks `A t` to the writer. A
    server that receives the read query `Q j` answers `D j`. Its local state never changes.
  - The reader always records the largest write index it has seen in an `F` message, with its
    value. Read `j` sends `Q j` to all servers. It returns the recorded value after `n − f` answers
    `D j`.

  By FIFO, when the reader gets `D j` from a server, it already got every `F` that server sent
  earlier. Quorum intersection then gives regularity, in fact atomicity. Liveness holds with up to
  `f` server crashes and any client crashes. There is no gossip, and `|S_i| = 1` for every server.
  So the left-hand sides of all six bounds are 0 while the right-hand sides are positive. Lean
  instance: `n = 5`, `f = 2`, `V = Fin 4`. The theorems assume regularity, so the counterexample is
  more than they need. Where the proofs break: in Section 4.3.1 "the readers and the channels from
  and to the readers do not perform any actions" during `α`, and Lemma 4.8(a) concludes that reader
  channels are the same at both critical points. If a server sends to the reader during `α`, the
  write cannot complete without that channel taking the message. Then the reader-side state at
  `Q₁, Q₂` is not determined by the server states, and Claim 4.9 fails. Appendix B (Theorem B.1)
  has the same gap: "all channels are empty" ignores what the live reader already received. This
  is a false statement, not a proof gap. (`not_theorem41`, `not_corollary42`, `not_theorem51`,
  `not_corollary52`, `not_theoremB1`, `not_corollaryB2`; the algorithm: `relay_counterexample`)
  *I/O-automaton reading (formalized).* In the multi-send relay above, one server step receives
  `W t v` and sends two messages. In the paper's I/O-automaton model each send is a separate output
  action, so a server would have to store the pending `F t v`. The *streaming relay* (`Stream.lean`)
  respects this restriction (`IOASends`: an input step of a server sends nothing, a spontaneous step
  sends at most one message).
  - The writer streams the bits of its values to each server, one bit at a time, waiting for an
    acknowledgement before sending the next bit.
  - A server's state is (pending bit, pending ack, pending answer, turn), 36 states in all. Its
    spontaneous steps take turns forwarding the bit to the reader, acknowledging, and answering
    queries.
  - The reader reassembles `B`-bit blocks per server and keeps the newest complete one. It sends
    one outstanding query per server and re-queries after a stale answer.

  It is proved atomic, live (`2f < n`) and gossip-free. With `n = 5`, `f = 2`, `V = Fin 16 → Bool`,
  all six bounds fail for it. (`not_theorem41_ioa`,
  `not_corollary42_ioa`, `not_theorem51_ioa`, `not_corollary52_ioa`, `not_theoremB1_ioa`,
  `not_corollaryB2_ioa`; the algorithm:
  `stream_counterexample`)
  *Scope.* Both counterexamples need FIFO channels. The paper says only "reliable, asynchronous",
  and reliable FIFO is the standard channel of Lynch's I/O-automaton framework, which the proofs
  use. We have no counterexample for non-FIFO channels. There the adversary could hold back the
  forwarded messages while a valency read runs, so the bounds may well hold, although the written
  proofs still ignore server-to-reader messages. The counterexamples also use the theorems'
  *single* reader. They would extend to any fixed finite set of readers (forward to each; not
  formalized), but not to the "possibly infinite" set of read clients of Section 3. So
  multi-reader versions of the bounds are not refuted.
* **Repair: Theorem 4.1 holds when servers do not push to an idle reader.** We add `ReaderQuiet`:
  if the reader takes no step, no server has sent it anything. It follows from "servers send to the
  reader only when processing a reader message" (`readerQuiet_of_repliesOnly`), which ABD-style
  algorithms satisfy. With it, the paper's proof goes through. We prove
  `|V|(|V|−1) ≤ (∏_{𝒩}|S_i|)·∑_{𝒩}|S_i|` for every `𝒩` of at least `n − f` servers, which is
  slightly stronger than the paper's `∏·(N−f)·max`. We also prove the logarithmic form,
  Corollary 4.2, and the counting form `|V| ≤ ∏_{𝒩}|S_i|` of Theorem B.1 without gossip.
  (`theorem41_count`, `theorem41`, `corollary42`, `theoremB1_count`)
* **The writer-crash step in Lemmas 4.4/4.6 assumes lossy channels from crashed clients.** After a
  critical point, the valency executions delay the writer's messages "indefinitely". The paper
  justifies this as "indistinguishable from a fair execution where the write client fails before
  sending the messages". But those messages were sent before the point. With channels reliable even
  from crashed processes, liveness does not guarantee the read terminates. Our model (CSLib
  `ChannelFailures`) does not require channels from crashed processes to deliver, which matches the
  paper's use. This is a modelling imprecision, not an error in the result.
* **Theorem 5.1's proof has an additional gap (not formalized).** Definition 5.3 "delivers all
  messages" between servers. With gossip this need not terminate, because servers can keep sending.
  At `R₂` the servers other than `s, s'` also receive messages that `s, s'` send during delivery,
  so they need not be in the same state as at `R₁`. The statement is false anyway (first item).
* **Minor.** The hypothesis `f ≥ 2` of Theorem 4.1 is never used. The counting argument works for
  every `f`, and Corollary 4.2's total-storage bound needs only `f ≥ 1` (we assume `1 ≤ f < n`).
  `N − f ≥ 1` is implicit (we assume `f < n`). In Theorem 4.1's proof, Case II says the read in
  `γ` "should return `v₂`" because `Q₂` is 2-valent. It actually follows from Lemma 4.5 together
  with `Q₂` not being 1-valent. Typos: the definition of critical points ranges over
  `{0, 2, …, M−1}`, and `P₁ = P^{(v₁,v₁)}` in Section 4.3.2.

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

**Not formalized.** Section 6 (Theorem 6.5, multi-version bound under protocol assumptions) and a
repaired Theorem 5.1 with gossip.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexample's atomicity is proved with CSLib's SWSR reads-from criterion
(`SWSRReadsFrom.isLinearization`). Its liveness is proved over fair infinite executions.
Non-vacuity of the repaired hypotheses: a single-server register (`n = 1`, `f = 0`, `|V|` server states) is proved atomic, live, gossip-free and `ReaderQuiet` (`Witness.witness_hyps`, `nonvacuous_hyps`, `nonvacuous_theorem41` in `Witness.lean`, `NonVacuity.lean`). Non-vacuity for `f ≥ 1` would need a bounded-state ABD-type algorithm and is not formalized. Infrastructure staged in `Podc/`:
`ChannelFailures/Steps.lean` (well-formed histories, pending accounting, step locality,
`exists_canon_ret`: from liveness to a finite canonical extension) and `ChannelFailures/Delivery.lean`
(`Algorithm.Fair.delivered`: eventual FIFO delivery). Both are CSLib candidates.
