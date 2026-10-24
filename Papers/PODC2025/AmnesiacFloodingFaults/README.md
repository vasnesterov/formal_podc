# Amnesiac Flooding: Easy to Break, Difficult to Escape — PODC 2025

Henry Austin, Maximilien Gadouleau, George B. Mertzios, Amitabh Trehan. *Brief Announcement: Amnesiac
Flooding: Easy to Break, Difficult to Escape.* PODC 2025. DOI
[10.1145/3732772.3733523](https://doi.org/10.1145/3732772.3733523). Formalized version: arXiv
[2502.06001](https://arxiv.org/abs/2502.06001) v2 (29 Oct 2025), the full version with all proofs (Appendices A–D).
Numbering follows it.

**Verdict: ❌ False claim.** The main result holds and is fully verified: from an arbitrary message
configuration, amnesiac flooding terminates iff the configuration is balanced (Theorem 5.1), iff it is
reachable from the empty configuration by multicasts (Theorem 5.5), and then within `2|E|` rounds
(Corollary 5.1.1). Two fault-sensitivity statements are false as stated:
* the first claim of Theorem 5.7 (uni-directional link failure) fails for initiator sets with two nodes;
* the broadcast half of Theorem 5.8 (Byzantine failure) fails.

All other Section 5 claims are proved. The Section 4 uniqueness theorem is not formalized.

## Mistakes in the paper

* **Theorem 5.7, first claim, is false for non-singleton initiator sets.** The claim: for every
  graph and every initiator set `I ⊊ V`, some uni-directional link failure makes flooding fail to
  broadcast or fail to terminate. Counterexample: the path `0 – 1 – 2` with `I = {0, 2}`. Each of the
  four possible failures leaves at least one of `0 → 1`, `2 → 1` working, so node `1` is informed in
  round 1. Node `1` forwards at most one message, to a leaf, and flooding stops by round 3. The
  paper's proof speaks of "the initiating node" and so only covers singletons. For a single
  initiator `s` the claim holds: fail the link from `s` to any neighbour `b`. Then either `b` is
  unreachable along working links, or there is a cycle `s ⇝ b → s` of working links. Around that
  cycle, one more message travels with it than against it, and this surplus never decreases
  (Lemma D.3). We prove this, and the second claim of Theorem 5.7 the same way, with a simpler proof
  than the paper's strong-connectivity case split.
  (`theorem_5_7_multi_false`; `theorem_5_7_singleton`, `theorem_5_7_second`)
* **Theorem 5.8, broadcast part, is false.** The claim: Byzantine nodes `J` can force a failure
  to broadcast iff `J` contains a cut vertex set. Counterexample: the same path, with `I = {0, 2}`
  and `J = {1}`. `{1}` is a cut vertex set, but whatever the adversary does, every node is an
  initiator or receives the message in round 1. This holds whether or not Byzantine nodes must
  receive it. The "if" direction also fails for one initiator if failure is counted over honest
  nodes only. Example: a star with centre `c`, the initiator `s` a leaf, and `J` = everything except
  `s`. `J ⊇ {c}` is a cut vertex set, but the only honest node is `s`. What is true, and proved, is
  this: the adversary can make some honest node never receive the message iff some honest node is
  unreachable from every initiator in `G − J`. For the "if" direction the adversary stays silent
  until flooding on `G − J` has died out. The same example refutes consequence (3) of the PODC
  version. Node `1` is not a leaf, but it can force neither non-termination (the path has no cycle)
  nor a broadcast failure.
  (`theorem_5_8_broadcast_false`; `theorem_5_8_broadcast`)
* **Theorem 5.1: the proof of the hard direction is only a sketch; the statement is true.** The
  hard direction is "balanced ⇒ terminates". Appendix A argues informally:
  * Lemmas A.3–A.6 bound how long a message can stay on a cycle or FEC. Their proofs are "new
    messages must collide with …" sketches.
  * The word combinatorics of Lemmas A.8–A.15 then show that a recurrent message's path must linger
    on a cycle or FEC.
  
  We replace all of this with a different proof:
  1. Pull the configuration back along any closed walk. Amnesiac flooding becomes flooding on a
     cycle with external activations.
  2. A three-line prefix-sum potential shows that a message cannot travel once around a closed walk
     if the walk is balanced (`not_balancedOn_of_front`).
  3. Every message surviving `2|E|` rounds has an ancestor chain. It repeats a directed edge, so it
     contains such a tour.
  4. Balance on cycles and FECs implies balance on every closed walk. This is a spanning theorem for
     cycles and "handcuffs" (the circuits of the signed-graphic matroid), proved by walk surgery
     (`walkSig_eq_zero_of_isCycle_of_fec`).
  
  The easy direction (Lemma A.1, invariance) is as in the paper.
  (`theorem_5_1`, `corollary_5_1_1`, `theorem_5_5`)
* **Proposition C.2 (Random Flooding): the termination argument is wrong.** The paper claims that if
  all bits are `1` for `D + 1` rounds and then all `0`, flooding has stopped two rounds later. On the
  5-cycle (`D = 2`) a reachable configuration with a single message violates this. Choosing bits
  that keep a single message `(0,1)` alive, then `1, 1, 1, 0, 0`, leaves messages in flight. The
  statement (almost sure termination) is plausible with a longer window (about `2n` all-ones rounds),
  but we do not formalize the probability.
  (`random_flooding_window_false`)
* **Lemma 5.2 as printed is false (typo).** The statement takes `T` to be the sinks of `S`. The proof
  uses the sinks of `S̄`, i.e. the nodes sending to all neighbours in `S`. Counterexample with the
  printed `T`: a single message on an edge. We prove the lemma with the proof's `T`, and Lemma 5.3
  from it. (`lemma_5_2_as_stated_false`; `lemma_5_2`, `lemma_5_3`)
* **The PODC version's bound `2|E| − 3`** (its Theorem 4.1(2)) fails on the path with two edges:
  `{(0,1)}` needs 2 rounds. It also fails on a single edge. This is a degenerate case only: the full
  version's `2|E|` holds, and brute force on all graphs with `n ≤ 6` and `3 ≤ |E| ≤ 8` agrees with
  `2|E| − 3`, which we do not formalize. (`podc_bound_false`; `corollary_5_1_1`)
* **Fault-model indexing.** Section 5.2.2 lets uni-directional failures act only from `S_2` on
  (`∀ i ≥ 1, S_{i+1} = A(S_i) \ X`), and drops only from round `k ≥ 1`. Read literally, the
  initiator's first-round messages cannot fail, and the second claim of Theorem 5.7 fails on a single
  edge. We let faults act from the first round, which is what the proofs use.
* **Typos and slips.**
  * Lemma 5.2 reads "`∀ v ∈ N(v)`".
  * Definition A.1 has an empty bullet.
  * Appendix C refers to "Theorem C.3" (a lemma), Lemma B.6 to "Theorem B.4", and Observation C.5
    to "Theorem D.5" for balance under Parrot Flooding.
  * Two figures are both labelled "Fig. 5".
  * Theorem 5.6 states only "if" for non-termination. Brute force (all graphs with `n ≤ 6`, `|E| ≤ 8`) shows it
    is in fact "iff"; we prove the "if" as stated.

Full list of differences: [differencies.md](differencies.md).

## The formalization

**Model.**
* `G : SimpleGraph V` on a finite type, in synchronous rounds. A configuration is `S : Set (V × V)`
  (`IsConfig`: messages along edges). One round with initiators `I` is `step G I` (`A_{I,G}`,
  Definition 3.2); `af G = A_{∅,G}`. `Terminates G S` means `A_∅^k(S) = ∅` for some `k`.
* Multicast runs are `runFrom G Is S`, and `Reachable` is statement (2) of Theorem 5.5.
* Single-source flooding is `srcRun` (agrees with Hussak–Trehan's `sends`, `mem_srcRun_iff_sends`).
* Balance (Definition 5.4) is `Balanced`. It is balance (`BalancedOn`) along every cycle and along
  the closed walk `c₁ ++ p ++ c₂ ++ p⁻¹` of every faux-even cycle (`FEC`); this walk traverses the
  paper's `H²`. Pulling `S` back along it gives exactly `S^{2,H}` (Definition 5.3).
* `BalancedOn S w` says that for every position `k₀` the clockwise and anticlockwise messages with
  heads at `k₀ + 2i` are equinumerous. For odd cycles this is "as many each way"
  (`balancedOn_iff_of_odd`); for even cycles it is the paper's head-parity classes.
* Faults:
  * `dropRun`: one lost message.
  * `uniRun`: a set `X` of failed directed links, every round.
  * `byzRun`: until a round `k ≥ k₀` chosen by the adversary, nodes of `J` send arbitrary messages
    along edges; everyone is honest afterwards. The paper's `k₀` is twice the diameter.
* "Fails to broadcast" means some (honest, non-initiator) node never receives a message.
* Connectivity is assumed only where needed (Theorem 5.6, broadcast part).

**Main results in Lean** (namespace `AmnesiacFloodingFaults`).

| Paper | Lean | File |
|---|---|---|
| Definition 5.4 (balanced) | `Balanced`, `BalancedOn`, `FEC`, `FEC.walk` | `Theorem51.lean`, `Lift.lean`, `WalkAlgebra.lean` |
| Theorem 5.1 | `theorem_5_1`; closed-walk form `terminates_iff_balancedAll` | `Theorem51.lean`, `Dichotomy.lean` |
| Corollary 5.1.1 (`≤ 2\|E\|` rounds) | `corollary_5_1_1`, `iterate_eq_empty_of_balancedAll` | `Theorem51.lean`, `Dichotomy.lean` |
| Lemma A.1 / Cor. A.1.1 | `lemma_A_1`, `balancedOn_step_iff`, `Terminates.balancedAll` | `Theorem51.lean`, `Lift.lean`, `Dichotomy.lean` |
| (new) replaces Lemmas A.3–A.15 | `not_balancedOn_of_front`, `walkFlow_eq_zero_of_isCycle`, `walkSig_eq_zero_of_isCycle_of_fec` | `Lift.lean`, `WalkAlgebra.lean` |
| Lemmas 5.2, 5.3, 5.4 | `lemma_5_2`, `lemma_5_3`, `lemma_5_4` | `Model.lean`, `Theorem51.lean` |
| Theorem 5.5 | `theorem_5_5` (closed-walk form `theorem_5_5_walks`) | `Theorem51.lean`, `Dichotomy.lean` |
| Theorem 2.1 / Lemma 3.1 (multicast terminates) | `theorem_2_1`, `lemma_3_1` | `Dichotomy.lean` |
| Theorem 5.6, non-termination | `theorem_5_6_nonterm` | `Faults.lean` |
| Theorem 5.6, broadcast (iff) | `theorem_5_6_broadcast` | `DropBroadcast.lean` |
| Lemma D.3 / Theorem 5.7 | `fails_of_failed_link`, `theorem_5_7_singleton`, `theorem_5_7_second`, `theorem_5_7_multi_false` | `Faults.lean`, `Examples.lean` |
| Theorem 5.8, non-termination (iff) | `theorem_5_8_nonterm` | `Faults.lean` |
| Theorem 5.8, broadcast | `theorem_5_8_broadcast_false`; corrected `theorem_5_8_broadcast` | `Examples.lean`, `ByzBroadcast.lean` |
| Prop. C.2 proof, Lemma 5.2 typo, PODC bound | `random_flooding_window_false`, `lemma_5_2_as_stated_false`, `podc_bound_false` | `Examples.lean` |

**Not formalized.**
* Theorem 4.1 (uniqueness). Definition 4.1 is under-specified, the proof needs Ramsey numbers
  `R(9,8)`, and it rests on dozens of gadget graphs and an unspecified "exhaustive search".
* Theorem 4.2 (relaxed protocols). Its 1-bit/Parrot Flooding part (Lemma C.3) was checked by brute
  force: it terminates from every non-leaf initiator on all graphs with `n ≤ 6` and on 3000 random
  graphs with 7–10 nodes.
* The probabilistic statement of Proposition C.2.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Concrete runs are checked by `decide` through `Finset` simulations proved equal to the
model (`coe_stepF`, `coe_uniSim`, `coe_rfStepF`); no `native_decide`. Non-vacuity: `bowtieFEC` and
`dumbbellFEC` are faux-even cycles of both kinds. Before formalizing, brute force checked:
* Theorem 5.1 and the `2|E|` bound on all connected graphs with `n ≤ 6`, `|E| ≤ 8`, over all
  configurations;
* Theorems 5.6 and 5.7 on the same graphs;
* Theorem 5.8 by an adversarial state search on graphs with `n ≤ 5`.

The model of single-source flooding is linked to `Papers/PODC2019/FloodingTermination`, whose parity
distances are reused.

**CSLib candidates.**
* `WalkAlgebra.lean`: additive walk functionals, and the spanning theorem for cycles and handcuffs.
* `exists_odd_cycle` (an odd closed walk contains an odd cycle on its support).
* The closed-walk lift with its per-node conservation law (`Lift.lean`).
