# Uniform Content-Oblivious Leader Election on Eulerian Graphs — PODC 2026

Fabian Frei, Ran Gelles, Ahmed Ghazy, Alexandre Nolin. *Brief Announcement: Toward Uniform
Content-Oblivious Leader Election on General Graphs.* PODC 2026. DOI
[10.1145/3796701.3815949](https://doi.org/10.1145/3796701.3815949). Formalized version: the 4-page
brief announcement (no arXiv version). Numbering follows it.

**Verdict: 🛠️ Proof repaired.** The combinatorial core is correct. Any port pairing of a graph with
all degrees even induces a unique circuit decomposition (Lemma 2). Re-pairing at a node merges
distinct circuits into one (Lemma 4). The merging phases of Lemma 5 end, after at most `log₂ n`
phases, in a single Eulerian circuit with a single leader, and the pulse arithmetic of Theorem 1
gives `O(|E|·IDmax)`. Two steps of the Lemma 5 sketch need a repair: in a mutually selecting pair
of circuits both merges must not be executed, and the OR protocol does not say how the leader's own
input is used. The OR protocol (with the leader's input) is verified on an asynchronous
content-oblivious ring. The other pulse-level parts (Lemma 3 with its ring-election black box, the
max-ID protocol, the synchronisation of merges) are not formalized.

## Mistakes in the paper

* **Lemma 5, merging phases: mutually selecting circuits (proof gap, statement true).** The sketch
  lets *every* circuit `C` merge into the adjacent circuit `C'` with the largest leader ID. A
  designated node of `C` re-pairs one pair of `C` with one pair of `C'`. Two circuits often select
  each other; for example, if only two circuits remain, each one's only neighbour is the other. Then
  two merges are performed on the same pair of circuits. The second re-pairing acts on two pairs
  that by then lie on *one* circuit, and that can split it again. Take `K_{2,4}` (`x, y` adjacent
  to `2, 3, 4, 5`) with circuits `C₁ = x2y3x` and `C₂ = x4y5x`. Merging at `x` (the node
  designated by `C₂`) gives one Eulerian circuit. Merging at `y` as well (the node designated by
  `C₁`, re-pairing as in Lemma 4) gives two circuits again, `x2y5x` and `x3y4x`. Whether this
  happens depends on how the pairs are labelled, which the sketch leaves open ("w.l.o.g."). So the
  sketch does not show that the number of circuits halves, or even decreases. Our repair: the
  circuit with the larger ID in a mutually selecting pair does not merge. Then the merge links
  form a forest, every link joins two different circuits, and each merged tree contains at least
  two old circuits and is led by its root, the largest ID in it. We prove that the number of
  circuits at least halves per phase, so there are at most `log₂ n` phases. (The protocol must
  then also tell `C` whether `C'` selected `C`; we do not formalize that.)
  (`DoubleMerge.double_merge_splits`; repaired: `phaseStep_spec`, `lemma5`)
* **Lemma 5, OR protocol: the leader's own input (under-specified).** The leader `ℓ_C` starts
  a clockwise pulse that "the first node with input 1 reflects"; if the pulse completes the cycle,
  the leader forwards it once more and every node outputs 0. The sketch does not say how the
  leader's own input enters. If "the first node with input 1" excludes the initiating leader, the
  protocol outputs 0 when only the leader borders another circuit, and the algorithm would stop
  with several circuits: for every ring size, all executions of this reading give output 0 when
  only the leader has input 1. The evident fix, which we adopt: if its pulse completes the cycle
  and its own input is 1, the leader acts as the reflector. We verify the fixed protocol in
  the asynchronous content-oblivious ring model for every schedule: it terminates quiescently, every
  node outputs the OR, and at most `2|C|` pulses are sent. Also, nodes with input 1 that come after
  the first reflector receive a counter-clockwise pulse first and must behave like nodes with
  input 0, which the paper's sentence "receive a counterclockwise pulse without a clockwise one"
  covers. (`OrProtocol.literal_wrong`; fixed: `OrProtocol.orProc_final`, `orProc_totalSent_le`)
* **Minor.**
  - The intro says the "maximum-ID node on the merged circuit becomes its new leader". It is the
    maximum among the merged *leaders* (the root of the merge tree; `id_le_id_top_of_top_eq`).
    This need not be the maximum-ID node of the circuit: in Lemma 3 a node may only relay
    passively on a circuit and then does not take part in its election.
  - The max-ID step of Lemma 5 (bitwise ORs over "prefix-free" encodings) needs an
    *order-preserving* prefix-free code. Otherwise it returns the lexicographically largest code,
    not the largest ID. Not formalized.
  - Lemma 3's sketch relies on properties of the ring election black box that are not stated:
    passive relays must recognise when an election has finished, and pulses must be bounded per
    edge (`O(IDmax)` on every edge) so that relays do not multiply the cost. Not formalized.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* A network is a finite simple graph `G` (Mathlib `SimpleGraph`), connected for Lemma 5 and
  Theorem 1. "Eulerian" means every degree is even, as in the paper. The ports of `v` are the darts
  `(v, w)`, and a port numbering is a bijection with `Fin (deg v)`.
* A port pairing (`Pairing G`) is a fixed-point-free, node-preserving involution on darts. Its
  circuits are the classes of the relation generated by "paired" and "reverse" (`Pairing.Circ`).
  Each class is realised by a Mathlib circuit `circuitWalk d` that follows the pairing.
* Lemmas 4 and 5 and Theorem 1 are formalized at the **circuit level**. A state is a pairing with a
  leader map; two darts lie on one circuit iff their circuits have the same leader, and the leader
  is a node of its circuit (`LeaderInv`).
  - Lemma 3, the per-circuit ring elections, is a black box: an arbitrary map `elect`, constant on
    circuits, that picks a node of each circuit.
  - A merging phase (`PhaseStep`) quantifies over every order of the merges and every choice of
    the common nodes where they happen.
  - Asynchrony, pulses and IDs inside the protocols are not modelled at this level. Theorem 1's
    pulse count is an arithmetic consequence of the black-box costs.
* The OR protocol is modelled in CSLib's content-oblivious model
  (`Cslib/Computability/Distributed/ContentOblivious/`): an oriented asynchronous ring of `n ≥ 1`
  nodes, pulses without content, an adversarial scheduler, no failures, deterministic nodes and a
  single leader.

**Main results in Lean.** (namespace `Podc.ContentObliviousEulerian`)

| Paper | Lean | File |
|---|---|---|
| §2.1 "pairing exists iff Eulerian" (Kotzig L1, pairing form) | `nonempty_pairing_iff` | `Pairing.lean` |
| §2.1 "every pairing induces a unique circuit decomposition" (Kotzig L4) | `Pairing.pairing_circuit_decomposition` | `Decomposition.lean` |
| Lemma 2 | `lemma2` | `Decomposition.lean` |
| Lemma 4 | `Pairing.lemma4`, `lemma4_edges`, `lemma4_other`, `repair_pair_of_fst_ne` | `Repair.lean` |
| Lemma 5 (circuit level: halving, `≤ log₂ n` phases, end = Eulerian circuit) | `lemma5`, `phaseStep_spec`, `exists_phaseStep`, `single_circuit_eulerian` | `Merging.lean` |
| Lemma 5 sketch: merge links form a forest, root = max ID, halving | `Pointer.not_linkRel_of_nodup`, `linkRel_iff_top`, `id_le_id_top_of_top_eq`, `two_mul_card_image_top_le` | `PointerForest.lean` |
| Lemma 5 sketch: double merge of a mutual pair can split (gap) | `DoubleMerge.double_merge_splits` | `DoubleMerge.lean` |
| Lemma 5 sketch: OR protocol (fixed) / literal version wrong | `OrProtocol.orProc_final`, `orProc_totalSent_le`, `orProc_observations`, `literal_wrong` | `OrProtocol.lean` |
| §2 step 3: Lemma 4 at every node ⇒ distinct leaders | `stage3_leaderInv`, `exists_stage3` | `Theorem1.lean` |
| Theorem 1 (circuit level, black-box Lemma 3) | `theorem1_circuit_level` | `Theorem1.lean` |
| Theorem 1 pulse count `O(|E|·IDmax)` (black-box costs) | `theorem1_pulses` | `Theorem1.lean` |

**Not formalized.** Lemma 3, i.e. the activation of virtual nodes running the ring election of
Chalopin et al. as a black box. The pulse-level implementation of Lemma 5: orientation agreement,
max-ID computation, and synchronising merges between circuits. Theorem 1 as a statement about a
content-oblivious algorithm on general graphs.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity checks:
* `theorem1_K24` (`Examples.lean`): the hypotheses of `theorem1_circuit_level` hold on `K_{2,4}`.
* `exists_elect`: election outcomes exist.
* `orProc_exists_final`: the OR protocol has final configurations.

CSLib modules used: `ContentOblivious.{Model, Prog, Compose}`, `Foundations.Data.ZMod.Cyclic`.

**CSLib candidates.**
* `Pairing.lean`, `Decomposition.lean`, `Repair.lean`: port pairings (Kotzig transition systems)
  on `SimpleGraph`, the circuit decompositions they induce, and merging circuits by re-pairing.
* `PointerForest.lean`: forests of max-neighbour pointers, for GHS/Borůvka-style merging.
