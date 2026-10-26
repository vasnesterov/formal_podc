# Self-Stabilizing Leader Election in Regular Graphs — PODC 2020

Hsueh-Ping Chen, Ho-Lin Chen. *Self-Stabilizing Leader Election in Regular Graphs.* PODC 2020. DOI
[10.1145/3382734.3405733](https://doi.org/10.1145/3382734.3405733). Formalized version: the
proceedings version (no arXiv version exists); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** Both protocols, as printed, fail. **SS-Tree (Theorem 4.3) is false**:
there is a configuration in which every node is a root, hence a leader, forever; no detector
ever fires. **SS-EulerCycle (Theorem 3.3) as printed is false as well**: no configuration is
output-stable, because the coherence check rejects every interaction in which the scheduler makes
the head of a virtual edge the initiator. This second error has a natural one-line repair: use the
virtual edge in either role. With the repair, we prove Theorem 3.3 on every connected `2k`-regular
graph, assuming (as the paper does) that the Ring-Protocol of [11] solves SSLE on directed rings.

## Mistakes in the paper

* **Theorem 4.3 / Lemma 4.2 are false: SS-Tree does not detect multiple roots.**
  MultipleRootDetector only moves coins between a parent and its child. A root tosses only when
  its coin is `0`, and a root's coin never returns to `0` (only a *child* is reset), so the
  re-tossing that the proof relies on ("there must be a time when two roots toss different coin
  values") never happens. Counterexample: let every node be a root whose `parentColor` is the colour
  of none of its neighbours, with all coins `+1`, counters `0`, ring states and copies non-leaders,
  and SS-TwoHop memory consistent. Then there is no parent–child pair. No coin ever moves. The ghost
  parents are never checked, because roots do not count. CycleDetector never runs the ring protocol
  and only copies non-leader states. Every node stays a leader forever. This works for every
  `k ≥ 2`, every graph of maximum degree `≤ k` (e.g. `K_{k+1}`), every neighbourhood-injective
  `k²`-colouring and every ring protocol. Severity: false statement; the detector needs a redesign.
  (`ssTree_all_roots_forever`, `ssTree_not_solvesSSLE`, `ssTree_fails_on_complete`,
  `ssTree_prob_zero`)
* **Theorem 3.3 / Lemma 3.1 are false for Protocol 1 as printed.** The coherence check accepts an
  interaction only if there is a virtual edge *from the initiator to the responder*; otherwise
  `u.errFlag ← True`. An Euler cycle traverses each edge in one direction, but both nodes of an edge
  get to initiate. We show that from **every** configuration an error is reachable. Either some
  ordered pair of neighbours has no forward virtual edge (one interaction suffices). Or all of them
  have one; then a node has `2k` neighbours but only `k` successor slots, so two neighbours share a
  colour, and the paper's own sequence `(A,B),(A,C),(A,B)` makes SS-TwoHop recolour and break a
  virtual edge. The erroneous initiator then takes a random state, so its output changes. Hence no
  configuration is output-stable on any `2k`-regular graph (`k ≥ 1`), whatever the ring protocol.
  Severity: false statement, but fixable. **Repair:** if there is no virtual edge `u → v` but there
  is one `v → u`, run the Ring-Protocol and SS-Token on it with `v`'s virtual node as the ring
  initiator. With this repair we prove Theorem 3.3. (`literal_not_solvesSSLE`,
  `literal_fails_on_complete`; repaired: `repaired_solvesSSLE`)
* **Lemma 4.1's proof does not cover CycleDetector's dynamics** (proof gap; not formalized, not
  refuted). The proof cuts a chain out of a stable ring of [11]: such a chain never creates a
  leader. But nodes unmark at random and leave stale `loopChild`/`loopParent` flags. A re-marked
  parent then copies a fresh `ringState` and runs the ring protocol with a child whose copy has
  already evolved. These mixed configurations are not reachable on the static chain. Whether a
  leader can appear depends on the internals of [11].
* **Lemmas 2.1, 3.2 and 4.2 are sketches.** Lemma 2.1 omits two hypotheses that the paper states
  only in the prose: a valid output-stable configuration exists, and error-detected configurations
  can reach it. Lemma 4.2 forgets the invalid configurations that already have one leader. For
  the repaired SS-EulerCycle we prove everything Lemma 3.2 uses: the slot-counting argument making
  coherent configurations a permutation of virtual nodes, two virtual rings sharing a node,
  convergence of SS-Token, and "an error-detected configuration reaches every configuration"
  (`derc_lemma`, `vperm`, `multi_reach`, `TokenRing.run_legit`, `err_reach_all`).
* Minor: the SS-TwoHop guard is garbled (we use Sudo et al.'s "matching colours, different bits").
  "2-hop colouring" must mean "the neighbours of each node have distinct colours"; for that, `4k²`
  colours suffice. The indentation of Protocols 5–6 is lost. The state counts are right: exactly
  `(64ck⁴)^k·64k⁴` and `320c²k⁶(k²+1)²(k+1)²`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Population protocols on a graph `G` (`GProtocol`). An interaction is an ordered pair of adjacent
  nodes (initiator, responder); both orders are scheduled. There are no IDs and no orientation.
* Randomized transitions are modelled by their **support**: `δ p q` is the set of possible outcomes.
  This includes the paper's `RandState`, random bits and random colours.
* Self-stabilization follows the paper. **Global fairness** is the standard notion of Angluin et
  al. `SolvesSSLE`: from any initial configuration, every globally fair execution reaches a valid
  output-stable configuration. We prove this is equivalent to reachability (`solvesSSLE_iff`) and to
  stabilization with probability 1 under any random scheduler supported on the steps
  (`Cslib.TransitionSystem.tendsto_compl_of_reach`, `prob_eq_zero_of_not_reach`).
* The Ring-Protocol of [11] is an arbitrary nondeterministic protocol with a leader output. For the
  repaired theorem it must satisfy `RingSpec`: SSLE on every directed ring of size ≥ 3, with the
  initiator being the predecessor, as in Protocol 1. The negative results need only a leader state
  and a non-leader state.
* SS-Tree (`ssTree`) and SS-EulerCycle (`ssEuler false` as printed, `ssEuler true` repaired) are
  transcribed sub-protocol by sub-protocol.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (detect-error-and-random-change) | `GProtocol.derc_lemma`, `derc_lemma'` | `Model.lean` |
| Thm 3.3 / Lemma 3.1, as printed: false | `literal_not_outputStable`, `literal_not_solvesSSLE`, `literal_fails_on_complete` | `EulerLiteral.lean`, `Main.lean` |
| Lemma 3.1, repaired (existence + stability) | `exists_good`, `good_validStable` | `GoodExists.lean`, `EulerMain.lean` |
| Lemma 3.2, repaired | `error_or_coherent`, `single_reach`, `multi_reach`, `err_reach_all` | `EulerErrors.lean`, `EulerMain.lean`, `ErrorReach.lean` |
| Thm 3.3, repaired | `repaired_solvesSSLE`, `repaired_selfStab`, `repaired_prob_one` | `EulerMain.lean`, `Main.lean` |
| Thm 4.3 / Lemma 4.2: false | `ssTree_all_roots_forever`, `ssTree_not_solvesSSLE`, `ssTree_fails_on_complete`, `ssTree_prob_zero` | `SSTree.lean`, `Main.lean` |
| State counts (Sec. 3.4, 4.4) | `card_estate`, `card_tstate` | `StateCount.lean` |
| SS-Token convergence ([5]) | `TokenRing.run_legit`, `TokenRing.Legit.step` | `TokenRing.lean` |
| Euler's theorem (used in Lemma 3.1) | `exists_isEulerian_of_even_degree`, `exists_euler_cyclic_seq` | `Euler.lean` |

**Not formalized.** We do not formalize the Ring-Protocol of [11] itself; `RingSpec` is assumed.
Also not formalized: the odd-degree and general-graph extensions (Section 3.5), and a repair of
SS-Tree.

**Trust.** No `sorry`. All listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity:
* globally fair executions exist (`Cslib.TransitionSystem.exists_globallyFair`), so the negative
  results are not vacuous;
* the counterexamples are explicit configurations on `K_{k+1}` / `K_{2k+1}`;
* the hypotheses of the repaired theorem are met by every connected `2k`-regular graph, given a
  ring protocol satisfying `RingSpec`. That such a ring protocol exists is the result of [11], which
  we do not formalize.

Built on the shared library: `GProtocol` is the nondeterministic population-protocol model
`Cslib.PopulationProtocol.NProtocol` with interactions along `G.Adj`
(`Cslib/Computability/Distributed/PopulationProtocols/Nondet.lean`); runs, global fairness, the existence of globally fair runs,
the fairness/reachability equivalence and the generic Lemma 2.1 (`exists_reach_of_err`) are in
`Cslib/Computability/Distributed/SelfStabilization/TransitionSystem.lean`, the probability-1 bridge in `Cslib/Computability/Distributed/SelfStabilization/Markov.lean`.

CSLib candidates:
* Euler's theorem (`Euler.lean`);
* greedy colouring of a conflict relation (`exists_coloring_of_card_lt`, `GoodExists.lean`).
