# Amortized Communication Complexity of Byzantine Broadcast — PODC 2023

Jun Wan, Zhuolun Xiang, Atsuki Momose, Ling Ren, Elaine Shi. *On the Amortized Communication Complexity of
Byzantine Broadcast.* PODC 2023. DOI [10.1145/3583668.3594596](https://doi.org/10.1145/3583668.3594596).
Formalized version: the PODC proceedings version (9 pages; no arXiv version). Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** The honest-majority protocol (Algorithm 4), which the abstract presents
as achieving amortized linear communication, is not a correct multi-shot Byzantine broadcast. Its
**Validity** fails, and so does **Lemma 3** ("an honest leader's epoch always succeeds"). Consistency
(Lemmas 1, 2, Theorem 1) is correct and proved. The dishonest-majority protocol (Algorithm 5.2) satisfies
Validity (Lemma 4) and Consistency (Lemma 5) only under a corrected reading of how TrustCast is invoked.
Read literally, both lemmas fail.

## Mistakes in the paper

* **Lemma 3 is false and Algorithm 4 violates Validity.** In step (8) (Query-1), a node `u` without a
  commit-proof sends `query₁` to the smallest node `v` that "has not accused `L_i`". An honest `v` that
  also lacks the commit-proof accuses `L_i` *in the same round*, so `u` cannot know this. `v` has
  nothing to send in Respond-1, and in Query-2 `u` accuses the honest `v`. Together with the Byzantine
  nodes' accusations this produces a corrupt-proof `thsig(accuse, v)` of an honest node. From then on,
  every honest node skips every epoch led by `v`, in every slot. The proof of Lemma 3 fails exactly at
  this point: "if `L_i` does not have a commit-proof … then `L_i` must have also accused the epoch's
  leader, and `u` would not have sent `query₁` to `L_i`".

  Concrete run: `n = 6`, `f = 2`, `ε = 1/6`, `G_ε = K₆` (a valid `(n, 2ε, 1−2ε)`-expander). Nodes 5 and 6
  are Byzantine; node 5 sends slot 1 and node 1 sends slot 2 (paper numbering). In epoch 0 of slot 1 the
  Byzantine leader runs the protocol correctly but sends the commit-proof only to node 4. Nodes 1, 2, 3
  accuse the leader; three accusations are too few for a corrupt-proof. Nodes 2 and 3 query node 1, and
  node 1 queries node 2; none of them has the commit-proof. In Query-2, nodes 2, 3, 5, 6 accuse node 1,
  which gives the `n − f = 4` accusations of a corrupt-proof. Node 4 then answers the `query₂`s and slot 1
  completes. In slot 2 the honest sender node 1 broadcasts `true`, and every honest node has committed
  slot 1, so sequentiality allows the invocation. Epochs 0 and 1 of slot 2 are led by node 1 and are
  skipped by every honest node. The honest leader of epoch 2 (node 2) proposes its arbitrary value
  `false`, which everybody commits. By consistency, no honest node ever commits `true` in slot 2, so
  **Validity fails** (`not_validity`). In the same run, slot 2's epoch 1 has an honest leader and nobody
  commits in it, so **Lemma 3 fails** (`not_lemma3`).

  The skip condition ("runs the following steps if it has neither committed in slot `k`, nor received
  `thsig(accuse, L_i)`") does not say when it is evaluated, so we checked three readings. Validity fails
  when "committed" is checked at the start of the epoch (with the corrupt-proof checked at the start of
  the epoch or at every step). Read literally, both conditions are checked at every step, so a node that
  holds a commit-proof has already committed and never answers queries. Rounds 8–11 then cannot
  disseminate anything, and Lemma 3 fails in the same run, already in slot 1. Fixing the bug needs a
  protocol change, not a local edit. A second, independent mismatch: Respond-1 condition 2 ("`u` is the
  smallest node `v` has not accused") ignores the Query-1 filter "has not accused `L_i`". A helper chosen
  past a smaller node that had accused `L_i` therefore refuses to answer and gets accused (not formalized).
  The complexity analysis (§4.2) and Termination are claims about this broken protocol. We did not
  formalize them.

* **Lemmas 4 and 5 (Algorithm 5.2) need a reading the pseudocode does not give.** Algorithm 5.2 invokes
  `TrustCast(G_u, n, k)`, whose rules run in rounds `1..n` of the slot and only consider proposals of
  slot `k`. The trust graph, however, is shared across slots. Read literally, equivocation evidence that
  one honest node receives in round `n` reaches the others when it is no longer processed, and the honest
  trust graphs diverge forever. Concrete run: `n = 3`, `f = 1`, Byzantine sender in slots 1 and 2,
  honest sender in slot 3. In slot 1 one honest node commits `⊥` and the other commits a value, so
  Lemma 5 fails (`literal_consistency_fails`). In slot 2 an honest node accuses an honest node, so
  TrustCast's integrity fails (`literal_integrity_fails`). In slot 3 an honest node commits `⊥` although
  the sender is honest, so Lemma 4 fails (`literal_validity_fails`). Running graph maintenance in every
  round is not enough: equivocation evidence must also persist across slots
  (`slotLocal_validity_fails`). The proof of Lemma 5 uses transferability in the Dolev–Strong rounds,
  i.e. graph maintenance after round `n`. With maintenance in every round and evidence of every slot,
  both lemmas hold for every slot of the multi-shot execution (`validity`, `consistency`). We count this
  as a statement issue whose intent is recoverable from the proof (⚠️).

* **Imprecisions.**
  * The definition of equivocation requires the two proposals to carry the same certificate `C`. Taken
    literally, a leader escapes detection by attaching different certificates. We use "two proposals
    with different values".
  * The proof of Lemma 2 refers to a "Leader setup" round; this is Collect.
  * The TrustCast properties are stated only for a complete initial graph, but they are used for the
    shared multi-slot graph. We prove them there.
  * The expander definition ("for any set `S` of `αn` vertices, the number of neighbours of `S` is more
    than `βn`") does not say whether `S` counts among its neighbours. It must: no graph has more than
    `n − |S| = (1 − 2ε)n` neighbours outside a set of `2εn` vertices, so the exclusive reading admits no
    `(n, 2ε, 1 − 2ε)`-expander at all. We assume only the weaker form `|S ∪ N(S)| > βn`. `K₆` in the
    counterexample satisfies even the stronger form `|⋃_{v∈S} N(v)| > βn`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model (Algorithm 4, `Model.lean`).**
* Lock-step synchrony. A message sent in round `r` is available from round `r+1`, and multicasts include
  the sender.
* `n` nodes `Fin n` and a static Byzantine set `F` with `|F| ≤ f`. The paper's adaptive adversary only
  matters for the positive results; for the deterministic protocol it is no stronger than a static
  adversary that may send anything.
* Ideal (threshold) signatures, expressed as a validity condition on the adversary (`AdvValid`). A
  signed atom of an honest node may be used once some honest node has sent it (rushing, eavesdropping
  adversary). A threshold signature may be used once `n − f` of its shares may be used.
* Slots of `f + 2` epochs of 11 rounds, with leaders `S_k, 1, …, f+1`. `act` transcribes steps (1)–(11)
  and the four `(★)` rules. Honest states (all messages received and sent) are computed from the
  adversary's messages (`exec`). The input `bc_k` of each sender is fixed in advance, which covers causal
  inputs because the protocol is deterministic.
* The skip condition is a parameter `Skip` (`epochStart`, `everyStep` = literal, `mixed`). Consistency is
  proved for all three.
* Expander hypothesis: `IsExpander G (2ε) (1−2ε)` with `0 < ε`, `f ≤ (1/2 − ε) n`. It implies the
  property `Expands` used in the proofs (`expands_of_isExpander`).

**Model (Algorithm 5.2, `DishonestMajorityModel.lean`).**
* Lock-step synchrony, a static honest set `H`, ideal signatures.
* Cumulative knowledge plus one trust graph per node, shared by all slots. `G_u` is the component of
  `u`, and distance is `edist`.
* A `Reading` parameter says in which rounds graph maintenance runs and which slots' equivocation
  evidence counts: `literal n` or `charitable`. The commit happens at the end of the slot.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `lemma1` | `Consistency.lean` |
| Lemma 2 | `lemma2` | `Consistency.lean` |
| Theorem 1 (consistency of Alg. 4) | `theorem1` | `Consistency.lean` |
| Lemma 3 — false (all readings) | `Counterexample.not_lemma3` | `Counterexample.lean` |
| Validity of Alg. 4 (Def. 2) — false | `Counterexample.not_validity` | `Counterexample.lean` |
| Expander parameters of the run | `Counterexample.isExpander_K6`, `theorem1_applies` | `Counterexample.lean` |
| TrustCast integrity (multi-slot) | `DishonestMajority.Setup.integrity`, `honest_never_accuses_honest` | `DishonestMajorityValidity.lean` |
| Lemma 4 (validity of Alg. 5.2, every slot) | `DishonestMajority.Setup.validity` | `DishonestMajorityValidity.lean` |
| TrustCast transferability / termination | `Setup.transferability`, `Setup.termination` | `DishonestMajorityConsistency.lean` |
| Lemma 5 (consistency of Alg. 5.2) | `DishonestMajority.Setup.consistency` | `DishonestMajorityConsistency.lean` |
| Lemmas 4/5 fail under the literal reading | `literal_validity_fails`, `literal_consistency_fails`, `literal_integrity_fails`, `slotLocal_validity_fails` | `DishonestMajorityLiteral.lean` |

**Not formalized.** The communication-complexity analyses (§4.2, §5.4; amortized `O(κn)` and `O(κn²)`).
Termination of Algorithm 4. Appendix A (HotStuff).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`; no `native_decide`. The counterexample run is computed by the kernel (`decide +kernel`,
88 rounds), and its adversary is proved unforgeability-respecting (`advValid`). The same run satisfies
every hypothesis of `theorem1`, which is also non-vacuity for the consistency theorem. Section 5 has
non-vacuity examples showing that the literal-reading attack satisfies all hypotheses of the charitable
`validity`/`consistency` theorems. Self-contained models; CSLib's `LockStep` was not used because a
state-based model with symbolic threshold signatures was simpler here. No CSLib candidates.
