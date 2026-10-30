# Differences between the formalization and the paper

Paper: Schett, Danezis, *Embedding a Deterministic BFT Protocol in a Block DAG*, PODC 2021,
arXiv:2102.09594v2. Rule labels (R1–R6) refer to the verdict scale.

## Statement-level issues (decide the verdict)

1. **Lemma 4.3 (2) (no duplication) is false.** It fails for messages with a Byzantine sender.
   Counterexample: `Counterexample.lemma_4_3_2_false`, with `n = 4`, `f = 1` and an equivocating
   server 3 building two valid genesis blocks. Correct server 1 references them in two of its blocks and
   receives the same message twice. The proof's claim "a duplicate requires `B₁ = B₁'`" is wrong.
   No R2–R4 excuse: the lemma is explicitly about every message received by a correct server, and the
   equivocation used is the one the paper itself describes (Example 3.5, Fig. 3). → ❌ (numbered lemma, R1).
   What holds: no duplication for correct senders when messages are unique (`lemma_4_3_2_correct`,
   `trace_noDupCorrect`).
2. **Theorem 5.1 is false as stated** (`Counterexample.theorem_5_1_false`). Our counting protocol
   `countP` is deterministic, its messages are unique and carry their sender. Over authenticated perfect
   links it satisfies `Φ` = "if a correct server delivers, then two different correct servers were
   requested" (`holdsOverAPL_phi`). The embedding violates `Φ` in a reachable state.
   → 🚨 (headline, R5: the theorem is about the paper's specific construction).
   `countP` echoes only on its first request, so its request handling depends on the state, which
   the paper's interface convention (Section 4: "messages triggered by requests do not depend on the
   state") excludes. The variant `countP₀` that echoes on every request satisfies that convention and
   fails in the same run (`Counterexample.theorem_5_1_false_stateless`); in `run12` each process
   instance is requested at most once, so no correct process sends a message twice.
   *Borderline (R4).* Section 4 says that, `P` being BFT, the simulated servers "can deal with duplicate
   messages". Reading "BFT protocol" as *assuming* tolerance of duplicated Byzantine messages would
   excuse the theorem; then `theorem_5_1_repaired` is the theorem and the verdict would be ❌ because of
   item 1. We do not apply R4, for two reasons. First, the theorem's hypothesis is "using the reliable
   point-to-point link abstraction", and Lemma 4.3, cited for exactly this, claims no duplication. A
   reader taking the paper at its word is misled about a channel property the proof needs. Second, the
   remark is about Byzantine behaviour in general, not a stated hypothesis of the theorem.
   Third, read literally the remark concerns case (2), a Byzantine `š` referencing a block several
   times. Those duplicates reach the simulated instance of `š` itself, a Byzantine receiver, whose
   behaviour is arbitrary anyway. The counterexample duplicates a message at a *correct* receiver,
   through equivocation (case (1)). For case (1) the paper only foresees "conflicting messages"
   to servers referencing `B` or `B'`, not the same message twice to one correct server.
3. **Definition 3.3 (iii) is ambiguous; this does not affect the verdict.** We read "`s` considers all
   predecessors valid" as "`s` has already inserted all predecessors into `G`". Under the recursive
   reading, line 6 of Algorithm 1 may insert a block before its predecessor (both in `blks`, both
   "valid"). `G` then stops being closed, and Lemma A.5 fails. The paper's proof of A.5 implicitly uses
   our reading. Under-specified definition, charitable reading adopted, no Lean counterexample.
4. **Algorithm 2, line 6** assigns `B.Ms[out, ℓⱼ] ≔ …` in a loop over `B.rs`. With two requests for the
   same label in one block, the first request's messages would be lost, and Lemma 4.1 (1) "⇒" would fail
   for them. We accumulate the messages. Typo with evident intent (R3), no verdict impact.

## Modelling choices

- **Hashes and signatures.** Blocks are a nested inductive type (`Block`) whose blocks contain their
  predecessors (symbolic model of `ref`). Equal content means equal block, and acyclicity holds by
  construction, so Lemma 3.2 holds for every block, not just with overwhelming probability. Signatures
  are not a field. Unforgeability is the execution constraint `Authentic`: a Byzantine server may send
  any block in which every block built by a correct server was created by that server. Byzantine
  servers may use every block created by correct servers (a slightly stronger adversary than "blocks
  it received").
- **Byzantine set.** Arbitrary (`Byz : Set S`). No `n ≥ 3f + 1` is needed for the positive results; the
  counterexample uses `n = 4`, `f = 1`.
- **Block DAG (Definition 3.4).** It is represented by its vertex set; the edges are exactly
  `{(B, B') | B ∈ B'.preds}` (`toGraph`). The paper only requires these edges to be present, but every
  graph built by `insert` from `∅` has exactly them. `PaperBlockDAG` is the graph version of
  Definition 3.4, and `IsBlockDAG.paper` connects the two. For these graphs, `G ⩽ G'` is inclusion of
  vertex sets (`toGraph_le_toGraph_iff`).
- **`valid(s, B)`** is server-independent: `Valid` (locally valid ancestors) plus "received", i.e.
  membership in `G_s`. Signature checking (Def. 3.3 (i)) is replaced by `Authentic`.
- **Network.** A set of sent messages; a correct server may receive any sent message addressed to it,
  any number of times. The `from` field is authentic.
- **Algorithm 1.** Each handler is one atomic event. Lines 12–13 answer a `FWD` only if `B ∈ G` at
  receipt time; otherwise it is dropped (for correct requesters this never happens: `FwdOK`).
  `rqsts.get()` takes all buffered requests. The local `G` is the list `log` of blocks in insertion
  order. Ghost variables `own` (disseminated blocks) and `reqs` (user requests) are added.
- **Fairness** (`Run.Fair`). Assumption 1 becomes "a message between correct servers is received at
  least once" (weaker than per send). Lines 6–9, lines 10–11 (timeout `Δ_B'` abstracted away) and
  `disseminate` are weakly fair. Requests and Byzantine actions are unconstrained.
- **Protocol `P`.** Steps on requests and messages both return messages *and indications*, and
  requests may change the state. This is more general than the paper's "messages triggered by requests
  do not depend on the state". Lemmas A.13/A.14 need `P.Owned` (messages carry their process's
  identity), which the paper takes for granted.
- **Indications of `shim(P)`.** These are the indications triggered at the blocks of `G_s` built by
  `s` (`ShimIndicates`). Algorithm 2 interprets all of `G` eventually (A.10), and the values do not
  depend on the order (4.2).
- **Link abstraction and properties** (`Link.lean`). For one instance `ℓ`: finite event lists at correct
  servers, with authenticity (`LinkSafe`) and no duplication (`NoDup`, or `NoDupCorrect` for correct
  senders). A property is a predicate on the interface trace (requests and indications with their
  server). Theorem 5.1 is formalized for such (safety) properties of finite executions. Liveness of the
  embedding is stated directly (Lemma 4.3 (1), Lemma A.17), not as transfer of arbitrary liveness
  properties over infinite traces.
- **`SendUnique`** (Cachin's convention that messages are unique) is needed for no duplication with
  correct senders. Without it a correct `s₁` that sends `m` at two of its blocks may have `m` received
  twice (two blocks of `s₂`), or once (one block of `s₂` referencing both: `Ms[in]` is a set).

## Statements formalized in a different (equivalent or stronger) form

- Lemma 2.2: the graph well-formedness `E ⊆ V × V` is an explicit hypothesis (`DGraph.WellFormed`).
- Lemma 3.2 is proved as acyclicity (`Block.not_transGen_self`), which is stronger.
- Lemma A.6: "every block is referenced at most once by the blocks of `s`" is the `Nodup` of the
  concatenation of the predecessor lists of all of `s`'s blocks, including the current one.
- Lemma A.7: the union of two block DAGs is a block DAG and contains both (`⩽`).
- Lemma A.10: progress (`TReach.exists_step`) and completion on finite `G` (`TReach.exists_complete`).
- Lemma 4.2 holds for all labels and also for `Ms[in, ℓ]`: interpreted blocks hold `interp P ℓ B`,
  whatever the pick order, the server and the block DAG (`TReach.val_eq_interp`).
- Lemma A.15 (`PIs ≠ ⊥` at line 7) is vacuous in the functional model (states are always defined).
- Lemma 4.1: `Sends`/`Receives` are defined via the out/in buffers of blocks built by the server; (1),
  (2) then add the paper's witnesses (`B'` with a request, `B₁ ⇀ B₂`).
- Lemma 3.7: "eventually `G'_s ⩾ G_s ∪ G_{s'}`" means vertex inclusion. The result is a block DAG with
  `toGraph (G_s ∪ G_{s'}) ≤ toGraph G'_s`.
- Lemma 4.3 (1) is proved for an arbitrary sender `s₁`. Lemma 4.3 (3) is proved at the trace level: a
  delivered message from a correct sender is in the sent messages of the prefix (`trace_linkSafe`).
- Lemma A.17: a request to correct `s` eventually appears in a block of `s` in the block DAG of every
  correct server. By `interp`, it is fed to `B.PIs[ℓ]`.
- Lemma A.18 is definitional for `ShimIndicates`.
- Theorem 5.1 repaired (`theorem_5_1_repaired`): for every reachable state and every correct `s`, the
  replay of `G_s` in insertion order is an execution over authenticated links, with no duplication
  for correct senders. Its interface trace satisfies every `Φ` that holds over such links. Process `s`
  indicates exactly what `shim(P)` at `s` indicates. Indications of other correct processes are shim
  indications, and requests are user requests.
