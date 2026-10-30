# Differences between the formalization and the paper

Paper: F. Frei, R. Gelles, A. Ghazy, A. Nolin, *Brief Announcement: Toward Uniform Content-Oblivious
Leader Election on General Graphs*, PODC 2026 (4 pages, proof sketches only).

## Gaps in the paper's proofs (statements true)

1. **Lemma 5: mutually selecting circuits.** The sketch says "every circuit `C` selects one
   neighboring circuit `C'` and merges into it", by a designated node of `C` that "locally chains
   its port pairing". When `C` and `C'` select each other (always the case with two circuits
   left), two re-pairings are applied to the same pair of circuits. The second one re-pairs two
   pairs of a single circuit, which can split it (`DoubleMerge.double_merge_splits` on `K_{2,4}`:
   merging `x2y3x` and `x4y5x` at `x` and then again at `y` gives `x2y5x` and `x3y4x`). The sketch
   therefore does not establish that the number of circuits halves. *Repair:* the larger circuit
   of a mutually selecting pair (`Pointer.IsRoot`) does not merge. Then the links form a forest
   (`Pointer.not_linkRel_of_nodup`) and every class has at least two circuits
   (`Pointer.two_mul_card_image_top_le`). Each class is led by its root, the maximum ID
   (`Pointer.id_le_id_top_of_top_eq`). Implementing the rule requires `C` to learn whether `C'`
   selected `C` (one more broadcast per phase); this is not formalized. *Verdict rule:* the
   description is part of the proof sketch of an existential lemma ("There is an algorithm …"),
   and a repaired algorithm exists (R1, R5), so this is a proof repair (🛠️). Borderline: if one
   reads the §2.2 prose as a correctness claim about a specific algorithm, the algorithm is
   under-specified rather than wrong. Whether the double merge splits depends on the labelling of
   the pairs, which the paper leaves "w.l.o.g." (R3/R4 would give ⚠️ at most).
2. **Lemma 5: OR protocol, the leader's input is not specified.** As described, the leader
   initiates and forwards its pulse; if the pulse completes the cycle, everyone outputs 0. Read
   literally (the leader is never "the first node with input 1"), this is wrong when only the
   leader has input 1 (`OrProtocol.literal_wrong`, every ring size). Counting the leader as a
   possible reflector is the evident intent; the gap is an under-specification of the sketch.
   Fixed (the leader reflects
   its own pulse when its input is 1), the protocol is verified for all asynchronous schedules:
   quiescent termination, correct OR at every node, at most `2|C|` pulses, and the stated
   observation patterns (`OrProtocol.orProc_final`, `orProc_totalSent_le`,
   `orProc_observations`). A claim inside a proof (R1): at most 🛠️, close to a routine detail.
3. **Lemma 3 (not formalized; unverified assumptions on the black box).** The sketch needs the
   ring election of Chalopin et al. to satisfy properties that the paper does not state:
   - passive relays can recognise that an election on their circuit has finished ("observed the
     pulse pattern of a complete ring leader-election algorithm");
   - an election on a circuit sends pulses over every edge of it (otherwise a later-activated
     virtual node could start a second election on an already finished circuit);
   - the pulse count is `O(IDmax)` per edge, not only `O(n·IDmax)` in total (relays stretch
     virtual links, so a bound in terms of the number of participants does not transfer to `|C|`);
   - a participant may start arbitrarily late, as long as it has not received a pulse.
4. **Max-ID by ORs (not formalized).** "Encodes this identifier in prefix-free form … sequence of
   OR protocols applied to the bits": this computes the lexicographically largest codeword. It is
   the largest ID only for an order-preserving prefix-free code (e.g. unary length, then binary).

## Imprecisions

5. The introduction says "the maximum-ID node on the merged circuit becomes its new leader"; it is
   the maximum among the *leaders* of the merged circuits (§2.2's "last one of this chain").
   These differ in general even if the ring election elects its maximum participant: in Lemma 3
   a node may only relay passively on a circuit and then does not take part in its election.
6. "Eulerian network" is defined as "all nodes have even degree"; connectivity is implicit. We
   assume `G.Connected` for Lemma 5 and Theorem 1 (needed: a disconnected graph cannot end with a
   single circuit).
7. Lemma 5 claims `O(log n)` phases without saying why the initial number of circuits is
   polynomial in `n`. After step 3 distinct circuits have distinct leaders, so there are at most
   `n` circuits, hence at most `⌊log₂ n⌋` phases (`lemma5`).

## Modelling choices

8. **Lemma 2.** Ports are numbered `0, …, deg v − 1` and paired `(0,1), (2,3), …` (the paper:
   `1, …, deg v` and `(1,2), (3,4), …`). A port numbering is arbitrary (`PortNumbering G`). "Circuit
   decomposition" = the partition of `E` into the edge sets of circuits (closed trails, Mathlib
   `Walk.IsCircuit`) that follow the pairing, including the transition at the closing node.
   Uniqueness = every circuit that follows the pairing has one of these edge sets
   (`edges_of_follows`). We prove "pairing exists ⇔ all degrees even" (`nonempty_pairing_iff`) but
   not the other direction of Kotzig's Lemma 1 for arbitrary decompositions ("decomposition ⇒
   even degrees"), which the paper only cites.
9. **Lemma 4.** Stated for any `k + 1 ≥ 1` pairs at one node on pairwise distinct circuits. The
   pairs can be any pairs of the node on those circuits, not necessarily the ones on which the
   node ran the election. The merging statement is the equivalence
   `newCirc d d' ↔ oldCirc d d' ∨ (d, d' both on C₀ ∪ … ∪ C_k)`, plus the edge-set union
   (`lemma4_edges`), the unchanged circuits (`lemma4_other`) and locality
   (`repair_pair_of_fst_ne`). "In which `v` is the leader" is bookkeeping (`stage3_leaderInv`).
   "Concatenation" is shown as edge-set union; that the merged circuit is a single closed trail is
   `circuitWalk` of the new pairing.
10. **Step 3 (Lemma 4 at all nodes).** Nodes are processed one after the other (`Stage3`, in any
    order). The re-pairings of different nodes involve disjoint sets of circuits, so this is
    equivalent to doing them simultaneously.
11. **Lemma 5 at circuit level.** Merges are executed one after another (`execLinks`), in any
    order and at any node common to the two circuits. Each merge re-pairs one pair of the current
    circuit containing `C` with one pair of the current circuit containing `C'`, i.e. Lemma 4 with
    two pairs. Simultaneous local re-pairings at different nodes commute, so any concurrent
    execution corresponds to some order. Phase synchronisation, orientation agreement and the
    OR/max-ID protocols are abstracted away; a phase is a relation `PhaseStep` that quantifies over
    all these choices.
12. **Theorem 1.** Formalized only as (a) the circuit-level composition of the four steps with
    Lemma 3 as a black box `elect` (`theorem1_circuit_level`): termination after `≤ log₂ n`
    phases with a single Eulerian circuit and a single leader; and (b) the pulse arithmetic
    (`theorem1_pulses`). The latter assumes per-circuit black-box costs `c₁|C|·IDmax` for the
    elections and `c₂|C|(log₂ IDmax + 1)` per phase, and derives
    `≤ (c₁ + 4c₂)|E|(IDmax + 1)`, using `n ≤ IDmax + 1` and `(log₂ m + 1)² ≤ 4m`. "Uniform" and
    "deterministic" are properties of the unformalized pulse-level algorithm.
13. **OR protocol.** On an oriented ring (the paper first agrees on an orientation) with the
    leader at node `0`; inputs are per virtual node. The paper's "first node with input 1 reflects
    it" is implemented as: a node with input 1 reflects the first *clockwise* pulse it receives.
