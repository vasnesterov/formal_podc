# Byzantine Agreement with Unknown Participants and Failures — PODC 2020

Pankaj Khanchandani, Roger Wattenhofer. *Brief Announcement: Byzantine Agreement with Unknown
Participants and Failures.* PODC 2020. DOI
[10.1145/3382734.3405740](https://doi.org/10.1145/3382734.3405740). Formalized version: the BA, with
the proofs and Algorithm 3 of the full version, arXiv
[2102.10442](https://arxiv.org/abs/2102.10442) v1. BA Lemmas 1–4 / Theorem 1 are full-version
Lemmas 2, 4, 6, 7 / Theorem 2.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** **Lemma 4 and Theorem 1 (the rotor-coordinator, one of the two algorithms
the abstract presents) are false.** With
`n > 3f`, every correct node can terminate without any good round, and without ever accepting the
opinion of a correct coordinator. Smallest instances: `n = 7, f = 2` for Lemma 4 and `n = 4, f = 1`
for Theorem 1.

The headline results survive in repaired form, though. With a corrected termination rule, the rotor-coordinator
works with `n > 3f` in `O(n)` rounds, with a good round among the first `f + 1` iterations. A
repaired version of the consensus algorithm solves consensus with `n > 3f` in `3f + 7` rounds.
The full version's consensus algorithm (Algorithm 3) is under-specified; under the natural
reading of its "fill rule" it violates agreement.

## Mistakes in the paper

* **Lemma 4 is false: a correct node can terminate without witnessing a good round.** Take `n = 7`
  with correct nodes `2,…,6` and Byzantine nodes `0, 1`. Both Byzantine nodes make themselves
  known to everybody in round 1, so the thresholds are 3 and 5 copies. They then play their
  `init`/`echo` messages so that:
  - in iteration 0, only node `2` gets 5 copies of `echo(1)`; so node `2` selects `1` and the
    others select `2`;
  - in iteration 1, the others add `1` and node `2` adds `0`. Node `2` now has
    `C_2 = {0,…,6}` and selects `C_2[1] = 1` again; the others have `C = {1,…,6}` and select
    `C[1] = 2` again.

  Everybody "reselects" and breaks in iteration 1, and no iteration was ever good. The proof's last
  step treats `C_v` as fixed ("a reselected node is in `{C_v[r mod |C_v|] : r < r_c}`"). But `C_v`
  is kept sorted, and inserting a smaller identifier shifts the index back onto the previous
  coordinator. (`Cex.lemma4_false`, `Cex.no_good`)
* **Theorem 1 is false: there need not be a round in which every correct node accepts the opinion
  of a common correct coordinator.** In the run above no correct node ever accepts any opinion. A
  second, independent gap shows up already for `n = 4, f = 1`. Iteration 1 there *is* a good round,
  but two correct nodes reselect in that very iteration and break. The coordinator's opinion would
  only be accepted in the next iteration, so they never accept it. The termination half of
  Theorem 1 does hold: everybody breaks within `n` iterations. (`Cex.theorem1_false`,
  `Cex4.theorem1_false`, `paper_terminates`)
  *Repair:* break once `2r > n_v` instead of on reselection. Since `n_v ≥ g > 2f`, nobody stops
  before iteration `f + 1`. We prove that some iteration `r ≤ f` is good, and that in iteration
  `r + 1` every correct node accepts exactly the coordinator's opinion. Every node stops by
  iteration `⌊n/2⌋ + 1`. The bound `r ≤ f` is tight in a bounded search. (`rotor_fixed`)
* **Full version, Algorithm 3: the fill rule is under-specified, and its natural reading breaks
  agreement.** The rule says that a node `v`
  that sends nothing is assumed to have sent what the receiver itself sent in the previous round.
  It is meant for terminated nodes. But correct nodes are also silent when they miss a threshold,
  and their silence then counts as support for the receiver's value. With `n = 4, f = 1` and inputs
  `0, 0, 1`:
  - node `1` alone sends `prefer(0)`;
  - it counts the two silent correct nodes as `prefer(0)` and then as `strongprefer(0)`, and
    decides `0`;
  - the others adopt the Byzantine coordinator's `1`, and in the next phase one of them decides
    `1` by the same mechanism.

  The Lean witness adds the fill rule to our (otherwise verified) phase layout, so this is an
  under-specified algorithm rather than a refutation of Algorithm 3 verbatim.
  (`FillCex.fill_rule_breaks_agreement`; the same adversary is harmless without the rule:
  `FillCex.without_fill`)
* **Full version, Theorem 3: proof gaps; statement true.** The proof relies on the false
  Theorem 2. The coordinator's opinion is taken from the previous phase, but Lemma 11 needs the
  current one. A rotor `break` inside the consensus is not specified. We verify a repaired
  Algorithm 3: the coordinator broadcasts its current opinion in the same phase, there is no fill
  rule, and decided nodes keep participating. It satisfies agreement, validity, and termination
  within `3f + 7` rounds, which confirms both the BA's `O(n)` and the full version's `O(f)`.
  (`consensus_correct`, `consensus_validity_bool`)
* **Small slips.**
  - The inequality chain in the proof of Lemma 1 is garbled. What is needed is `g > 2f_v'`.
  - Lemma 3 (relay) silently assumes that no correct node has terminated yet.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`, paper-local, CSLib candidate)
* Synchronous lock-step rounds. A protocol is a single state machine that knows only its own id
  and input, so `n` and `f` are unknown by construction. Identifiers come from any type (`ℕ` in the
  counterexamples) and need not be consecutive.
* Correct nodes broadcast a finite *set* of messages per round, to everybody including themselves.
  Receivers see `(true sender, message)` pairs, and duplicates collapse.
* Static Byzantine set `F`, `G ∩ F = ∅`. Byzantine nodes send arbitrary per-receiver message sets
  (possibly none), may mention non-existent identifiers, and are adaptive (any function of the
  round, sender and receiver). Since protocols are deterministic, this covers adaptive adversaries.
  There is no Sybil behaviour and no forging of the direct sender, as in the paper.
* Resilience hypothesis: `2|F| < |G|`, i.e. `n > 3f` with `f = |F|`.
* The candidate-set mechanism (lines 1–13 of the rotor) is a shared layer (`withRotor`). The rotor
  (`rotor rule`) and the consensus (`cons`) are extensions of it. Coordinator selection follows
  line 14, `C_v[r mod |C_v|]` (as the proof of Lemma 4 does), not the prose's "next larger
  identifier", which is a different rule. `n_v` counts the senders heard
  from so far, including the current round.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (BA) / 2 (full) | `lemma1` (`lemma1_arith`) | `Layer.lean`, `Model.lean` |
| Lemma 2 (BA) / 4 (full) | `lemma2` (`lemma2_arith`) | `Layer.lean`, `Model.lean` |
| Lemma 9 (full) | `lemma9` | `Layer.lean` |
| Lemma 3 (BA) / 6 (full), relay | `relay` | `Layer.lean` |
| RB correctness / unforgeability for the layer | `G_sub_C`, `C_origin`, `C_real` | `Layer.lean` |
| Lemma 4 (BA) / 7 (full) — **false** | `Cex.lemma4_false` | `Counterexample.lean` |
| Theorem 1 (BA) / 2 (full) — **false** | `Cex.theorem1_false`, `Cex4.theorem1_false` | `Counterexample.lean` |
| Theorem 1, termination half | `paper_terminates` | `RotorFixed.lean` |
| Lemma 4, repaired (abstract) | `exists_good_round`, `layer_good` | `GoodRound.lean`, `Layer.lean` |
| Theorem 1, repaired | `rotor_fixed` | `RotorFixed.lean` |
| Lemmas 8, 10, 11 (full) | `unanimous`, `lock`, `good_phase` | `Consensus.lean` |
| Section 5 (BA) / Theorem 3 (full), repaired algorithm | `consensus_correct`, `consensus_validity_bool` | `Consensus.lean` |
| Algorithm 3's fill rule — **breaks agreement** | `FillCex.fill_rule_breaks_agreement` | `FillRule.lean` |

**Not formalized.**
* Reliable broadcast with payloads (full version, Section V). Its mechanism is the verified
  candidate layer.
* Approximate agreement, the asynchronous / semi-synchronous impossibility results, parallel
  consensus and dynamic networks (full version, Sections VIII–XI).
* Halting of the consensus algorithm after deciding.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The counterexamples are concrete runs checked by `decide +kernel`. The repaired
results are non-vacuous: the hypotheses are only `n > 3f`, and `FillCex.without_fill` runs the
verified consensus on a concrete instance. The abstract searches over rotor schedules are in
`modelcheck/`: they found the `n = 7` instance and the tight bound `r ≤ f`. Paper-local
infrastructure, CSLib candidates: the id-only model (`Model.lean`) and the candidate-set layer
(`Rotor.lean`, `Layer.lean`, `GoodRound.lean`). Shared infrastructure: `cnt` is `Finset.countEq`
(`Cslib/Foundations/Data/Finset/Quorum.lean`); the king step of Lemma 11 (`good_phase`) is the generic phase-king
lemma `Cslib.Byzantine.kingPhase_agreement` (`Cslib/Computability/Distributed/Byzantine/KingPhase.lean`).
