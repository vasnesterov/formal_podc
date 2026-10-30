# Embedding a Deterministic BFT Protocol in a Block DAG — PODC 2021

Maria A. Schett, George Danezis. *Embedding a Deterministic BFT Protocol in a Block DAG.* PODC 2021. DOI
[10.1145/3465084.3467930](https://doi.org/10.1145/3465084.3467930). Formalized version: arXiv
[2102.09594](https://arxiv.org/abs/2102.09594) v2 (full version with appendix); numbering follows it.

**Verdict: 🚨 Headline claim false.** The interpreted block DAG does not give an authenticated *perfect*
link: a Byzantine server that equivocates makes a correct server receive the same message twice. So
Lemma 4.3 (2) (no duplication) is false. Theorem 5.1 (every property that `P` has over reliable links is
kept) is false too: some deterministic `P` relies on no duplication. Everything else checks out: the block
DAG lemmas of Sections 2–3, gossip safety and liveness, the order-independence of the interpretation
(Lemma 4.2), reliable delivery and authenticity. We prove a repaired Theorem 5.1: it holds for every
property that `P` keeps over authenticated links that may duplicate messages of Byzantine senders.

## Mistakes in the paper

* **Lemma 4.3 (2) is false: equivocation duplicates messages.** The proof says a correct `s₂` can
  receive the same message `m` twice only by referencing the same block twice, which Lemma A.6
  forbids. But two *different* blocks can trigger the same `m`. Take `n = 4`, `f = 1`, with server 3
  Byzantine. Server 3 builds two genesis blocks `Bb₁` and `Bb₂` that differ only in their payload. Both
  are valid, and this is exactly the equivocation of Example 3.5 / Fig. 3. Each triggers the protocol
  message `ECHO` from 3 to 1. The correct server 1 follows Algorithm 1: it references `Bb₁` in its first
  block `D₁` and, after receiving `Bb₂`, references `Bb₂` in its second block `D₂`. In the
  interpretation, `1` receives the message `(3 → 1, ECHO)` at `D₁` and again at `D₂`. The 12-event
  run is a checked run of Algorithms 1 and 3. (`Counterexample.lemma_4_3_2_false`)
* **Theorem 5.1 (headline) is false as stated.** Theorem 5.1 transfers properties that `P` has "using
  the reliable point-to-point link abstraction", and Lemma 4.3 says this abstraction is Cachin et al.'s
  authenticated perfect link, no duplication included. A protocol written for that abstraction may rely
  on no duplication. Our example is the deterministic protocol "echo once when requested; deliver after
  `2f+1 = 3` received messages". Its messages are unique and carry their sender. Over authenticated
  perfect links it satisfies "if a correct server delivers, then two different correct servers were
  requested". In the run above only server 0 is requested. Yet `shim(P)` at server 1 delivers, since
  it counts 0's echo once and 3's echo twice. (`Counterexample.theorem_5_1_false`; the variant
  that echoes on *every* request, as the paper's convention "messages triggered by requests do not
  depend on the state" requires, fails the same way: `Counterexample.theorem_5_1_false_stateless`)
  *Borderline.* Section 4 says in passing that a BFT protocol "can deal with duplicate messages". If
  "BFT protocol" is read as *assuming* that, the theorem survives in the form we prove
  (`theorem_5_1_repaired`), and the verdict would drop to ❌ (because of the false Lemma 4.3 (2)). We
  keep 🚨 because Lemma 4.3 and Theorem 5.1 explicitly promise a link with no duplication. The paper's
  demonstration protocol (Algorithm 4, Bracha's broadcast) counts *senders*, so it is not affected.
  Repairs: dedup per receiver chain in Algorithm 2, or restrict Theorem 5.1 to properties that survive
  Byzantine duplicates.
* **Under-specified validity (no verdict impact).** Definition 3.3 (iii) "`s` considers all `B' ∈ B.preds`
  valid" must mean "has already *inserted* them". If validity is read recursively ("would consider
  valid"), line 6 of Algorithm 1 may insert a block before its predecessor, and Lemma A.5 (`G` is a
  block DAG) fails. We use the reading under which Lemma A.5 holds (`lemma_A_5`).
* **Small slips.**
  - Line 6 of Algorithm 2 *assigns* `B.Ms[out, ℓⱼ] ≔ B.PIs[ℓⱼ].rⱼ` inside the loop over `B.rs`. With two
    requests for one label, the messages of the first request are lost. We accumulate them.
  - Lemma 4.3 (1) needs no correctness of the sender `s₁`, as the text remarks.
  - In Lemma A.7, "any `G ⩾ G_s ∪ G_{s'}`" should be the union itself (or a block DAG containing it).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Blocks* are content-addressed: `Block` is a nested inductive type whose blocks contain their
  predecessors. This idealizes collision and preimage resistance of `ref`, and makes Lemma 3.2 and
  acyclicity structural. Signatures are idealized in the execution model: a Byzantine server may send any
  block in which every block built by a correct server was really created by it (`Authentic`).
- *System* (`Gossip.lean`). Asynchronous message passing, with servers `S`, an arbitrary set `Byz` of
  Byzantine servers and no bound on `|Byz|`. The network is a set of sent messages that may be
  received any number of times, in any order. Correct servers run Algorithm 1 handler by handler, each
  handler atomic, plus the request buffer of Algorithm 3. `disseminate` seals all buffered requests.
  `valid(s, B)` means "locally valid, and all predecessors already in `G_s`".
- *Liveness* (`GossipLive.lean`). Fair runs: a message between correct servers is received at least once
  (Assumption 1, slightly weaker than the paper's version). Lines 6–9 and 10–11 are weakly fair, with
  the timeout `Δ` abstracted away, and every correct server disseminates infinitely often (Algorithm 3,
  lines 10–11).
- *Protocol `P`* (`Interpret.lean`). A deterministic black box, given by `init ℓ s` and `step : state →
  (request | message) → state × messages × indications`. Messages have a sender and a receiver. For
  sender-related lemmas we assume `P.Owned` (messages carry their process's identity). For no
  duplication with correct senders we assume `SendUnique` (Cachin's convention that messages are unique).
- *Link abstraction* (`Link.lean`). Finite executions over authenticated links, for one instance `ℓ`:
  events at correct servers, authenticity (`LinkSafe`) and no duplication (`NoDup`). A property is a
  predicate on the interface trace (requests and indications with their server).
- *Interpretation* (`Interpret.lean`). Algorithm 2 is given both as a canonical function `interp P ℓ B`
  and as the nondeterministic traversal (`TStep`), which computes exactly `interp`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.2 (1)–(3) (+ the two remarks after it) | `DGraph.insert_eq_self`, `DGraph.le_insert`, `DGraph.acyclic_insert` (`not_le_insert_of_mem`, `not_acyclic_insert_of_mem`) | `Graph.lean` |
| Lemma 3.2 | `Block.edge_asymm` | `Block.lean` |
| Def. 3.3, 3.4 | `Block.LocallyValid`, `Block.Valid`, `IsBlockDAG`, `PaperBlockDAG`, `IsBlockDAG.paper` | `Block.lean` |
| Lemmas A.2, A.3, A.7 | `insertBlock_eq_self`, `paperBlockDAG_insertBlock`, `isBlockDAG_union` | `Block.lean` |
| Lemmas A.4, A.5, A.6 | `lemma_A_4`, `lemma_A_5`, `lemma_A_6` (invariant `Inv`, `reachable_inv`) | `Gossip.lean` |
| Lemma A.8, Lemma 3.6 (1), (2), Lemma 3.7 | `lemma_A_8`, `lemma_3_6_1`, `lemma_3_6_2`, `lemma_3_7` | `GossipLive.lean` |
| Lemmas A.9, A.10, A.11 | `TReach.val_eq_none`, `TReach.exists_step` / `TReach.exists_complete`, `TStep.val_eq` | `Interpret.lean` |
| Lemmas A.12, A.13, A.14 | `out_origin`, `owner_interp`, `sender_of_mem_out` | `Interpret.lean` |
| Lemma 4.1 (1), (2) | `lemma_4_1_1`, `lemma_4_1_2` | `Interpret.lean` |
| Lemma 4.2 | `lemma_4_2` (via `TReach.val_eq_interp`) | `Interpret.lean` |
| Lemma A.16 | `lemma_A_16` | `Interpret.lean` |
| Lemma 4.3 (1) reliable delivery | `lemma_4_3_1` | `GossipLive.lean` |
| Lemma 4.3 (2) no duplication — **false** | `Counterexample.lemma_4_3_2_false`; correct senders: `lemma_4_3_2_correct`, `trace_noDupCorrect` | `Counterexample.lean`, `Embedding.lean` |
| Lemma 4.3 (3) authenticity | `trace_linkSafe` | `Embedding.lean` |
| Lemmas A.17, A.18 | `lemma_A_17`, `lemma_A_18` | `GossipLive.lean`, `Shim.lean` |
| Theorem 5.1 — **false** | `Counterexample.theorem_5_1_false`, `Counterexample.theorem_5_1_false_stateless` | `Counterexample.lean` |
| Theorem 5.1, repaired (safety; liveness = `lemma_4_3_1`, `lemma_A_17`) | `theorem_5_1_repaired`, `trace_exec` | `Embedding.lean` |

**Not formalized.** The BRB example of Section 5 / Algorithm 4. Property transfer for infinite traces:
liveness of the embedding is given by Lemma 4.3 (1) and A.17, not as a statement about all liveness
properties of `P`. Partial synchrony and the extensions of Section 7.

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: `FairExample.run_fair` is a fair run. `countP_owned` and `countP_sendUnique`
show that the protocol hypotheses of `theorem_5_1_repaired` can be met, by the very protocol of the
counterexample. The counterexample run is checked by `decide`/`simp` against the step relation
(`reachable_run12`). The model is self-contained (Mathlib only). `Link.lean` (executions of a black-box
protocol over authenticated links) is a CSLib candidate.
