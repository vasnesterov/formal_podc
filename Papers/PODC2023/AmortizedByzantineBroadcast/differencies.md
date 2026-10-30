# Differences between the formalization and the paper

Paper: Wan, Xiang, Momose, Ren, Shi. *On the Amortized Communication Complexity of Byzantine Broadcast.*
PODC 2023 (proceedings version).

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Lemma 3 is false** (`Counterexample.not_lemma3`). It is a numbered lemma, false for every reading of
   the skip condition, and not a typo: the proof reasons with the wrong step (R1, R3 not applicable).
   This alone gives ❌.
2. **Algorithm 4 violates Validity (Definition 2)** (`Counterexample.not_validity`), for the readings in
   which a committed node keeps answering queries. In the literal reading the protocol is worse:
   committed nodes never answer, so rounds 8–11 never deliver a commit-proof. Validity of Algorithm 4 is
   the correctness claim of the headline protocol. The abstract says "We present a protocol that
   achieves optimal amortized linear complexity under an honest majority", i.e. it names the paper's
   specific protocol (R5), hence **🚨**.
   *Borderline (R6):* the contribution list states the result existentially ("we show how to achieve
   `O(κn)` amortized communication"). Under that reading, and since we do not know whether a repaired
   protocol exists, the result would be "unestablished" and the label ❌. We chose 🚨 because the abstract
   names the presented protocol and its correctness is what fails. The fix is not local (R3): the querier
   cannot know a same-round accusation, so the protocol needs another round or a different response rule.
   Respond-1 condition 2 also conflicts with the Query-1 filter.
3. **Lemma 4 and Lemma 5 (Algorithm 5.2) fail under the literal reading** of "`TrustCast(G_u, n, k)`"
   (`literal_validity_fails`, `literal_consistency_fails`, `literal_integrity_fails`). They hold when
   graph maintenance runs in every round and equivocation evidence of every slot is processed
   (`Setup.validity`, `Setup.consistency`). Label ⚠️ (R3/R4). The proof of Lemma 5 uses transferability
   during the Dolev–Strong rounds, and the TrustCast properties are claimed "for any round `t`", so
   maintenance after round `n` is the evident intent. That equivocation evidence must outlive its slot
   (`slotLocal_validity_fails`) is less evident; we record it here as the borderline part of this
   ⚠️ call.
4. **Termination of Algorithm 4** is not formalized. Theorem 1 does not depend on it. The validity
   counterexample already shows the protocol is not a multi-shot BB.

## Modelling choices — Algorithm 4 (`Model.lean`)

* **Synchrony.** Lock-step rounds. A message sent in round `r` is usable from round `r + 1`. Multicasts
  include the sender, so a leader counts its own vote and share.
* **Adversary.** A static Byzantine set `F` with `|F| ≤ f` that may send arbitrary items, subject only to
  unforgeability (`Scenario.AdvValid`, `availAt`). The paper's strongly adaptive adversary (corruption
  during the run, after-the-fact removal) is not modelled.
  * For the counterexamples this is harmless: a static adversary is a special case.
  * For consistency: a node corrupted later behaves arbitrarily from the protocol's point of view. Our
    honest set is the paper's set of never-corrupted nodes, and our adversary may use every honest
    signature as soon as it is sent (rushing and eavesdropping). So the static model covers the safety
    argument.
* **Signatures.** Ideal and symbolic. A threshold signature (certificate, commit-proof, corrupt-proof) is
  usable iff `n − f` of its shares are usable. A share is usable iff its signer is Byzantine or an
  honest node has sent it in this or an earlier round. Message sizes (`κ`) are not modelled.
* **Inputs.** `inp u k` is the value `u` would broadcast as sender of slot `k`, fixed in advance. Because
  the protocol and adversary are deterministic, this covers inputs that depend on earlier decisions.
* **Nodes.** Paper nodes `1..n` are `Fin n` indices `0..n−1`, and the leader of epoch `i ≥ 1` is index
  `i − 1`. The paper's example nodes are shifted by one in the Lean file (Lean node `4` = paper node `5`).
* **Skip condition.** Parameter `Skip`:
  * `epochStart`: both conditions are evaluated at the start of the epoch.
  * `everyStep`: the literal reading.
  * `mixed`: "committed" is evaluated at epoch start, the corrupt-proof at every step.
  The `(★)` rules always run.
* **"Arbitrary value"** of an honest leader in epochs `i > 0` without certificate: a parameter `dflt`.
  The counterexample uses `false` with sender input `true`. Any fixed rule loses in the same way when the
  sender's input differs from it.
* **Collect** sends the freshest held slot-`k` certificate, or nothing for `⊥`; Propagate-1 compares
  against it. Certificates carried inside proposals count as held certificates.
* **Propagate-1** forwards every received proposal of `L_i` for this epoch that is at least as fresh.
  "`u` has sent `L_i`'s proposal on `m` in Propagate-1" is read from `u`'s own send record, so a node
  without neighbours never votes; with an expander this does not occur.
* **Equivocation** is detected when `u` holds two proposals of `L_i` for `(k, i)` with different values,
  whatever their certificates. The paper's definition literally requires the same `C`; we take this as a
  typo.
* **Query-1.** The smallest `v ≠ u` with (1) `u` has not accused `v`, counting the accusation of `L_i`
  just made, and (2) `u` holds no `⟨accuse, L_i⟩_v`.
  * Excluding `v = u` is our choice. If `u` may query itself, the counterexample still works: node 1
    then accuses itself, which only adds an accusation.
  * "If not yet sent" for the accusation of `L_i` is implemented.
* **Respond-1** condition 2: `u` is the smallest node `w ≠ v` with no `⟨accuse, w⟩_v` held by `u`.
  Without `w ≠ v`, a querier with a smaller index than its helper could never be answered.
* **Query-2.** Triggered if no commit-proof of epoch `(k, i)` was received from `v` in this epoch.
* **Respond-2.** "First time `u` receives `⟨accuse, w⟩_v`": received in the previous round and not
  before. The commit-proof sent is the first one held.
* **`(★)` rules.** Implemented as events ("upon receiving" = received in the previous round).
  * Corrupt-proofs are aggregated when the count of distinct accusers first reaches `n − f`.
  * Accusations are forwarded to the accused node when first received, and not by the accused node to
    itself. Otherwise a node accused of something would re-forward the accusation to itself in every
    round; this only adds messages.
  * A newly received commit-proof is multicast if `n − f` accusers of that epoch's leader are held.
* **Committing.** `Commits u k m`: `u` ever holds a commit-proof `thsig(C_{k,j}(m))`.
* **Expander.** `IsExpander G α β`: every `S` with `|S| ≥ αn` has `|S ∪ N(S)| > βn`. This is weaker than
  the open-neighbourhood reading and holds for sets of at least `αn` vertices rather than exactly `αn`
  (equivalent by monotonicity). With `0 < ε` and `f ≤ (1/2 − ε)n`, `expands_of_isExpander` derives the
  form used in the proofs: sets of `n − 2f` nodes reach more than `2f` nodes, and `2f < n`.
  The reading that excludes `S` from its neighbourhood is unsatisfiable for `α = 2ε`, `β = 1 − 2ε`
  (`|N(S) \ S| ≤ n − αn = βn`), so `S` must count. The counterexample's `K₆` satisfies even the form
  "the union of the open neighbourhoods of the vertices of `S` has more than `βn` vertices" (for
  `|S| ≥ 2` it is all of `Fin 6`), so the counterexample does not depend on this choice.
* **Lemma 1** is proved without the adversary-validity hypothesis: it is a statement about existing
  certificates.
* **Lemma 2** is stated for commit-proofs and certificates that are usable by the adversary at some
  round. This is the formal meaning of "exists".
* **Theorem 1** covers `u = v`, so a node never commits two values in one slot.

## Modelling choices — Algorithm 5.2 (`DishonestMajority*.lean`)

* **Nodes and timing.**
  * A finite type `N` and a static honest set `H`. Lemma 4 needs no bound on `|N \ H|`; Lemma 5 needs
    `|N \ H| ≤ f`.
  * Slots are indexed from 0 (the paper starts at 1) and have length `T = n + f + 3`.
* **Adversary.**
  * Unforgeability: the adversary may deliver an honest-signed atom only if some honest node multicast it
    in an *earlier* round. This is slightly weaker than the rushing adversary of the Algorithm 4 model;
    it affects only the positive Lemmas 4 and 5, not the counterexamples.
  * The adversary may send different atoms to different nodes.
* **Trust graph.**
  * State = cumulative knowledge plus a `SimpleGraph`. `G_u` is the component of `u`, so vertex removal
    is immediate.
  * Accusations are processed (and forwarded) only when both endpoints are in `G_u` at the start of the
    round.
  * An equivocating sender loses all its edges.
  * Distance accusations use the graph after this round's accusations, before equivocation removal (the
    paper's order). Distance is `edist` (`⊤` if unreachable).
  * "`S_k ∉ G_u`" is checked on the end-of-round graph.
* **Votes and commit.**
  * `⟨corrupt, v⟩_w` votes count across slots, including the node's own vote.
  * The committed value is a proposal known after round `n`, or `⊥` if the node ever sent
    `⟨corrupt, S_k⟩`.
  * "If not yet sent" clauses are dropped: resending changes nothing.
* **Reading.** `Reading.literal n` (maintenance in rounds `1..n`, evidence of the current slot only) and
  `Reading.charitable` (maintenance in every round, evidence of every slot). Prop forwarding and
  distance accusations always run in rounds `1..n`.
* The TrustCast properties (transferability, termination, integrity) are proved for the shared
  multi-slot graph, not only for a complete initial graph.

## Not formalized

* Communication complexity: §4.2 (amortized `O(κn)`) and §5.4 (amortized `O(κn²)`).
* Termination and sequentiality of Algorithm 4.
* Appendix A (HotStuff).
* The Respond-1 / Query-1 mismatch (second bug in Algorithm 4) is described only in prose.
