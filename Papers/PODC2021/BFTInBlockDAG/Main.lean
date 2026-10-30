import Papers.PODC2021.BFTInBlockDAG.Counterexample
import Papers.PODC2021.BFTInBlockDAG.GossipLive

/-!
# Embedding a Deterministic BFT Protocol in a Block DAG (PODC 2021) — index

Schett, Danezis, PODC 2021, arXiv:2102.09594v2.

* `Graph.lean`: directed graphs, Definition 2.1, Lemma 2.2.
* `Block.lean`: blocks (Definition 3.1), Lemma 3.2, validity (Definition 3.3), block DAGs
  (Definition 3.4), Lemmas A.2, A.3, A.7.
* `Gossip.lean`: Algorithm 1 (+ the request buffer of Algorithm 3) as an asynchronous system with
  Byzantine servers; invariant with Lemmas A.4, A.5, A.6.
* `GossipLive.lean`: fair runs; Lemmas A.8, 3.6, 3.7, 4.3 (1), A.17.
* `Interpret.lean`: Algorithm 2; Lemmas A.9–A.14, 4.1, 4.2, A.16.
* `Link.lean`: executions of a protocol over authenticated (perfect) point-to-point links.
* `Shim.lean`: Algorithm 3's indications, Lemma A.18.
* `Embedding.lean`: the interpretation is an execution over authenticated links (Lemma 4.3 (3),
  Lemma 4.3 (2) for correct senders), Theorem 5.1 repaired (`theorem_5_1_repaired`).
* `Counterexample.lean`: Lemma 4.3 (2) and Theorem 5.1 are false
  (`lemma_4_3_2_false`, `theorem_5_1_false`).
-/
