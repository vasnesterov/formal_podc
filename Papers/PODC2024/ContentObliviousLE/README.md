# Content-Oblivious Leader Election on Rings — PODC 2024

Fabian Frei, Ran Gelles, Ahmed Ghazy, Alexandre Nolin. *Brief Announcement: Content-Oblivious Leader
Election on Rings.* PODC 2024. DOI [10.1145/3662158.3662785](https://doi.org/10.1145/3662158.3662785).
Formalized version: the full paper, arXiv [2405.03646](https://arxiv.org/abs/2405.03646) v1 (the only
version); numbering follows it (BA Theorems 1 and 3 = full Theorems 1 and 3).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The algorithms are correct exactly as claimed. Algorithm 2 is a
quiescently terminating leader election on oriented rings with exactly `n(2·IDmax+1)` pulses, the
leader terminating last. Algorithm 3 elects and orients non-oriented rings quiescently with
`n(2·IDmax+1)` pulses (Theorem 2) or `n(4·IDmax−1)` pulses (Proposition 14). The lower bound holds
only as a worst case over ID assignments (as Theorem 17 of the full version says), not per
instance; the statement of Theorem 3 leaves this quantifier implicit. Its proof
has a repairable gap. IDs must be positive.

## Mistakes in the paper

* **Theorem 3 holds only as a worst case over ID assignments (imprecise statement).** "Any …
  algorithm sends at least `n⌊log₂(IDmax/n)⌋` messages" is false if read for each ring and ID
  assignment. Run Algorithm 2 on IDs relabelled by the swap `1 ↔ 16`. This is still a correct
  quiescently terminating leader election. On the single-node ring with ID 16 it sends at most 3
  pulses in every execution, while `1·⌊log₂ 16⌋ = 4`. What Theorem 17 proves, and what we prove, is
  the worst case: for `n ≤ M`, some assignment of distinct IDs from `{1,…,M}` has an execution with
  at least `n⌊log₂(M/n)⌋ ≥ n⌊log₂(IDmax/n)⌋` pulses. The full version's Theorem 17 states this
  quantifier explicitly ("for some assignment of IDs") and derives Theorem 3 from it, so the
  intended reading is clear from the full paper; only the standalone statement is imprecise.
  (`theorem_3_per_instance_false`, `theorem_3`)
* **Lemma 19 / Theorem 17: proof gap, statement true.** The lockstep argument says that nodes with
  equal solitude patterns "send their first pulse in the same direction … receive and send exactly
  the pattern", and that one pulse is sent per time step. Patterns record *received* pulses, so two
  IDs with equal patterns may still send in different batches (two pulses at start versus one at
  start and one after the first reception). Then "one pulse per time step" and "send exactly the
  pattern" are not literally true, and the synchronized scheduler needs to be made precise. Fix:
  schedule by rounds of receptions. In round `k`, every node consumes the pulse at the port given
  by the `k`-th symbol of the common prefix. It is available because the sender sent it after the
  same `k−1` receptions in its own solitude run. Count received pulses (`n·s`), which bound sent
  pulses from below. (`Cslib.ContentOblivious.reach_sync`, `lemma_19`, `theorem_17`)
* **IDs must be positive (under-specified definition).** The paper writes `ID_v ∈ ℕ` without saying whether `0`
  is allowed. A node with ID `0` relays every pulse, so on the 1-node ring Algorithm 2 runs forever. The proofs (Lemma 5's base
  case, the pigeonhole in Lemma 22) silently use `ID ≥ 1`. (`infinite_execution_id_zero`)
* **Minor.** The lower bound needs correctness on rings with 1 node (a self-loop) and 2 nodes (a
  double link). The paper uses these explicitly, but its definition of a ring ("connected graph with
  all degrees 2") does not literally include them. Several cross-references are wrong: "Lemma 1–5"
  in Lemmas 6–8 and Appendix A mean the items of Lemma 5 and Lemma 24, "Algorithms 2–2" means line
  ranges, and Lemma 11's proof has `ID_v` for `ID_b`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Cslib/Computability/Distributed/ContentOblivious/Model.lean`).
* Two-port nodes on a ring `ZMod n` (any `n ≥ 1`). The oriented ring links `Port1` of `v` to
  `Port0` of `v+1`. A non-oriented ring additionally flips the ports of an arbitrary set of nodes.
* Pulses carry no content, so each channel is a counter. Pulses are never lost or created.
  Asynchronous: at each step an adversary delivers any pulse in transit to a node that is ready to
  read the port it arrives at. Readiness models the pseudo-code's polling. Unread pulses stay in
  transit.
* Deterministic, event-driven nodes that know only their own ID (uniform: no knowledge of `n`). All
  nodes act at time 0. Terminated nodes never act again.
* "Terminates / stabilizes" is stated finitely. The number of pulses is bounded on every execution,
  so all executions are finite. All *final* configurations (no step possible) are correct. This
  implies the paper's statements under any fairness assumption.
* IDs are distinct and positive; for Algorithm 1 they only need to be positive.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 1 is a quiescently stabilizing LE; Lemmas 5–13, Corollary 12; Lemma 15 (non-unique IDs) | `Alg1.algorithm_1`, `Ring.Profile.*` | `Alg1.lean`, `RingCounting.lean` |
| Lemma 22 (CCW instance lags behind CW) | `Alg2.Counters.rccw_lt` | `Alg2.lean` |
| Lemma 24 (the event `ρcw = ID = ρccw`) | `Alg2.Counters.trigger` | `Alg2.lean` |
| **Theorem 1** (termination, unique leader, quiescence, exactly `n(2·IDmax+1)` pulses) | `Alg2.theorem_1` | `Theorem1.lean` |
| §1.1: nothing is sent to a terminated node; the leader terminates last | `Alg2.terminated_spec`, `Alg2.leader_last` | `Theorem1.lean` |
| Proposition 14 (`n(4·IDmax−1)`) | `Alg3.proposition_14` | `Theorem2.lean` |
| Lemma 15 for both directions of Algorithm 3 | `Alg3.final_counts` | `Alg3.lean` |
| **Theorem 2** (non-oriented: LE + orientation, `n(2·IDmax+1)`) | `Alg3.theorem_2` | `Theorem2.lean` |
| Lemma 19 (patterns are unique) | `LowerBound.lemma_19` | `LowerBound.lean` |
| Lemma 20, Corollary 21 | `LowerBound.lemma_20`, `LowerBound.corollary_21` | `LowerBound.lean` |
| Theorem 17; unbounded even for `n = 1` | `LowerBound.theorem_17`, `LowerBound.unbounded_single_node` | `LowerBound.lean` |
| **Theorem 3** (worst-case form) | `LowerBound.theorem_3` | `LowerBound.lean` |
| Theorem 3 per instance: **false** | `LowerBound.theorem_3_per_instance_false` | `LowerBound.lean` |
| IDs must be positive | `Alg2.infinite_execution_id_zero` | `IdZero.lean` |

The lower bound is proved for a larger class than the paper's. It covers every deterministic
algorithm in the model, including ones that poll only some ports. It assumes only that maximal
executions on 1- and 2-node rings end with all nodes terminated and exactly one leader. The
lockstep/indistinguishability lemma (`reach_sync`) and the solitude characterization (`reach_one`)
are in `Cslib/Computability/Distributed/ContentOblivious/Lockstep.lean`.

**Not formalized.** Corollary 2 (simulation via the external compiler of Censor-Hillel et al.) and
Appendix B (anonymous rings, randomized ID sampling).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: Algorithm 2 satisfies the lower bound's hypothesis for every ring size
(`LowerBound.alg2_solves`), and every execution of Algorithms 1–3 can be completed to a final
configuration (`exists_final`). Before the proofs, a bounded exhaustive check of all schedules
(`modelcheck/mc.py`: all schedules and all port assignments for `n ≤ 3` and IDs ≤ 4, plus spot
checks for `n = 4`) found no counterexample to Theorems 1, 2 or Proposition 14.
The 2026 paper *Efficient Counting and Simulation in Content-Oblivious Rings* (Chalopin, Chang,
Di Luna, Zhou) cites this paper only as prior work and claims no correction. It mentions a later
*terminating* algorithm for non-oriented rings by Chalopin et al., which answers the open question
of §6.
