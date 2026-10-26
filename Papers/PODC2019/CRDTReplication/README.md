# Linearizable SMR of State-Based CRDTs without Logs — PODC 2019

Jan Skrzypczak, Florian Schintke, Thorsten Schütt. *Linearizable State Machine Replication of State-Based CRDTs
without Logs.* PODC 2019 (brief announcement). DOI [10.1145/3293611.3331568](https://doi.org/10.1145/3293611.3331568).
Formalized version: the full version, arXiv [1905.08733](https://arxiv.org/abs/1905.08733) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** Algorithm 2 is **not linearizable**. Theorem 3 (Consistency), Lemma 3 and Theorem 4
(Update Stability) are false: a five-process execution with majority quorums lets two queries learn the
incomparable states `{u₁}` and `{u₂}`, although `u₁` completed before `u₂` was invoked. Lemmas 1, 2, 4,
Corollary 1 and Theorems 1, 2, 5 hold, and so does the Section III-E reduction (Theorems 1–5 ⇒ linearizability).
A one-line repair of the `VOTE` handler restores Theorems 1–5 and linearizability, which we prove.

## Mistakes in the paper

* **Theorems 3 and 4 and Lemma 3 are false, and Algorithm 2 is not linearizable.** Take five processes
  `p₀…p₄`, majority quorums, a G-set, and only incremental prepares; no message is lost, some are only late.
  1. A query `C` raises the round numbers of `p₀, p₁, p₃, p₄` to 1.
  2. Query `A` (at `p₀`) gets `ACK((2,A), ∅)` from `p₀` and `p₁`.
  3. Update `u₁`, issued at `p₄`, is merged at `p₀, p₁, p₂` and completes on their three `MERGED`s.
  4. Query `B` reads `{u₁}` from `p₀, p₁, p₂` and learns it **by consistent quorum**.
  5. Update `u₂` is applied at `p₃` only.
  6. `A`'s `PREPARE` reaches `p₂, p₃, p₄`, which all move to round `(2, A)`. The round numbers coincide because of
     step 1. `A` takes the quorum `{p₀, p₁, p₃}` with states `∅, ∅, {u₂}`, all in round `(2, A)`, and sends
     `VOTE((2,A), {u₂})`.
  7. `p₂, p₃, p₄` are still in round `(2, A)` and answer `VOTED`, so `A` **learns `{u₂}` by vote**, although
     `p₂` and `p₄` hold `u₁`.

  So `{u₁}` and `{u₂}` are incomparable, which refutes Theorem 3 and Lemma 3. Since `u₁` precedes `u₂`, Theorem 4
  fails too. For the G-set, `A` returns `{u₂}` after `u₁` completed and `u₂` was invoked, so the history has no
  linearization.

  Both proofs confuse the `ACK` quorum with the `VOTED` quorum. The proof of Lemma 3 applies condition C1, which
  holds only on `Q₁ ∩ Q₂` (here `{p₀, p₁}`), to the voter `a = p₂ ∈ Q₁` outside `Q₂`. It also tacitly assumes
  that a later `PREPARE` cannot get the same round number at all acceptors. The proof of Theorem 4 says "∄Q: a.r = r
  for all a ∈ Q, as all a ∈ Q_u updated their round". But the acceptors of `Q_u` that receive the `PREPARE`
  *after* the `MERGE` do hold round `r`, and their payloads (with `u₁`) are not part of the proposed LUB. The flaw
  is in the protocol, not only in the proofs: a `VOTED` certifies that the acceptor's round is unchanged, not that
  its payload is `⊑` the proposal.

  The schedule respects the paper's own reading of line 47 too: the voters' payloads changed *before* they
  received `A`'s `PREPARE`, not "in the meantime". The same flaw is in arXiv v1 (2019), whose handlers and proofs
  (Lemma 3.6, Theorem 3.9) are identical in the relevant lines.

  The non-linearizability needs queries that can tell which updates are included. On the paper's own G-counter
  with the `sum` query, this particular execution is linearizable, although the same schedule still yields the
  incomparable learned vectors `e₄` and `e₃` (not formalized). (`Cex.lemma3_false`, `Cex.theorem3_false`,
  `Cex.theorem4_false`, `Cex.not_linearizable`, `paper_false`)
* **Repair.** An acceptor answers `VOTE(r', s')` only if, in addition, its payload *before the merge* is `⊑ s'`
  (`Variant.fixed`). Then every learned state was, at some moment, the exact payload of every acceptor of a quorum.
  Consistency follows from monotonicity alone, and Lemma 4's Paxos-style round argument is no longer needed.
  Update stability follows because a quorum acquired `u₁` before `u₂` existed. We prove Theorems 1–5 and
  linearizability for the repaired protocol. (`fixed_theorem3`, `fixed_theorem4`, `fixed_linearizable`)
* **Lemma 4 is true, but its proof is incomplete.** It does not handle two attempts with the same round number,
  and it uses that round numbers of accepted prepares strictly increase at each acceptor. We prove it with the
  Paxos-style invariant "every `ACK` with a larger round number carries a state above an earlier `VOTED`".
  (`paper_lemma4`)
* **Under-specified definitions (minor).**
  * Line 13 tests `sᵢ ≡ s'`, and the paper defines `≡` as query equivalence. The proof of Lemma 2(i) needs
    `s' ⊑ a.s`, i.e. equality, so we use equality.
  * The causal history `C(s)` is treated as a function of the state, which is not well defined for every CRDT.
    Also `u ∈ C(u(s))` is too weak for Theorem 1. We assume a causal-history map with `C(s₀) = ∅`,
    `C(u(s)) = C(s) ∪ {u}`, `C(s ⊔ t) = C(s) ∪ C(t)` and Shapiro et al.'s `C(s) = C(t) ⇒ s ≡ t`. The G-set has one.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous message-passing model `Cslib.AsyncMP`: unordered channels with arbitrary delays, crash-stop.
  Safety concerns finite executions, so a lost message is one that is never delivered. Histories are CSLib
  `Label`s, and linearizability is CSLib's `IsLinearization` w.r.t. the CRDT's sequential specification
  `CRDT.spec` (updates apply the command, queries return `cmd_q(s)`).
* Every process is a proposer and an acceptor (`alg V QS`). Clients are the processes themselves, with one pending
  operation per process. Each handler is atomic.
* The quorum system `QS` is an arbitrary pairwise-intersecting family of sets.
* The CRDT is arbitrary (`CRDT`: join semilattice, inflationary updates, queries). The theorems mentioning
  "includes `u`" use a causal-history map `H`.
* Proposer behaviour is generous, which makes the positive results stronger:
  * the internal action `advance` may act on *all* `ACK`s received so far, as soon as they contain a quorum;
  * `retry n` lets a pending query abandon its attempt at any time and restart with an incremental or arbitrary
    fixed prepare, which models NACK-triggered retries;
  * the local acceptor counts towards the `MERGED` quorum.

  The counterexample uses only the paper's literal behaviour.

**Main results in Lean** (namespace `Podc.CRDTReplication`; statements in `Statements.lean`).

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (payloads grow) | `paper_lemma1` (`lemma1`) | `Main.lean`, `Safety.lean` |
| Corollary 1 | `paper_corollary1` | `Main.lean`, `Safety.lean` |
| Lemma 2 | `paper_lemma2` | `Main.lean`, `Safety.lean` |
| Theorem 1 (Validity) | `paper_theorem1` | `Main.lean`, `History.lean` |
| Theorem 2 (Stability) | `paper_theorem2` | `Main.lean`, `History.lean` |
| Lemma 3: **false**; true after repair | `Cex.lemma3_false`; `fixed_lemma3` | `Counterexample.lean`; `Main.lean` |
| Lemma 4 | `paper_lemma4` | `Main.lean`, `Safety.lean` |
| Theorem 3 (Consistency): **false**; true after repair | `Cex.theorem3_false`; `fixed_theorem3` | `Counterexample.lean`; `Main.lean` |
| Theorem 4 (Update Stability): **false**; true after repair | `Cex.theorem4_false`; `fixed_theorem4` | `Counterexample.lean`; `Main.lean` |
| Theorem 5 (Update Visibility) | `paper_theorem5` | `Main.lean`, `History.lean` |
| Lemma 5 | `CRDT.CausalHistory.C_mono` | `CRDT.lean` |
| Lemmas 6–8 (Theorems 1–5 ⇒ linearizable) | `linearizable_of_learnedHistory` | `Linearizability.lean` |
| Main claim (linearizable SMR): **false**; true after repair | `Cex.not_linearizable`, `paper_false`; `fixed_linearizable` | `Counterexample.lean`, `Main.lean` |

**Not formalized.** Liveness (Section III-F, finite-writes termination), the optimizations (Section III-G) and the
experiments.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
The counterexample execution is checked by evaluation (`rfl`), with no `native_decide`.

Non-vacuity:
* `Cex.qs5_isQuorumSystem` shows the counterexample's quorums form a quorum system.
* `fixed_nonvacuous` shows the repaired protocol has executions in which queries learn states, and that the
  counterexample run is not one of them.
* `gsetHistory` is a causal history for the G-set.

The model is CSLib `Cslib.Computability.Distributed.MessagePassing.Async`, with linearizability from
`Cslib.Computability.Distributed.SharedMemory.History`.

CSLib candidates: the CRDT vocabulary (`CRDT.lean`) and the Section III-E reduction (`Linearizability.lean`).
