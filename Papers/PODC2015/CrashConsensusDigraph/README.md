# Crash-Tolerant Consensus in Directed Graphs — PODC 2015

Lewis Tseng, Nitin H. Vaidya. *Fault-Tolerant Consensus in Directed Graphs.* PODC 2015. DOI
[10.1145/2767386.2767399](https://doi.org/10.1145/2767386.2767399). Formalized version: arXiv
[1412.8532](https://arxiv.org/abs/1412.8532) v2 (*Crash-Tolerant Consensus in Directed Graphs*, same
authors); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The headline synchronous result holds: crash consensus with at most
`f` crashes is solvable on a digraph iff every reduced graph `G_F` (`|F| ≤ f`) has a node reaching all
of it (Theorems 1–4, binary and multi-valued). The asynchronous necessity (Theorem 6) holds.
Its sufficiency (Theorem 7, only sketched) fails for Algorithm WA if phase-`p` messages are handled
as soon as they arrive (the pseudocode does not say what happens to early messages): then a node can
deadlock. It holds for the evident fix, which we verify.
The proof of Theorem 5 (no fixed iterative algorithm) works only if outputs are "eventual"; with
outputs at a fixed iteration — as Min-Max does — the paper's counterexample graph admits a fixed
iterative algorithm.

## Mistakes in the paper

* **Theorem 5: the counterexample fails for fixed-iteration outputs (proof wrong under that
  reading).** Section 3 never says when an iterative algorithm outputs. The proof claims that a fixed
  transition function `Z` must map all-0 (all-1) collections to 0 (1) and that the source's value
  never changes. If the output is the value after a fixed iteration `T`, as for Algorithm Min-Max,
  this is false. For `f = 1`, `Z(R) = ¬max R` with output after iteration 4 solves binary crash
  consensus on the paper's own graph (source, clique of `f + 1 = 2` nodes, leaf), against every crash
  pattern with one crash, including mid-round crashes with partial delivery. The values alternate
  between "true" and "negated", so `¬max` simulates alternating Max and Min rounds. Python search also
  confirms this for `f = 2`; for `f = 3` the same `Z` fails at `T = 4`. With "eventual" outputs (from
  some iteration on, the fault-free values agree and are inputs) the paper's argument is sound, and we
  prove Theorem 5 for every `f`. The paper's executions crash a clique node, which is impossible for
  `f = 0`; our proof also covers that case. Whether Theorem 5 holds with fixed-iteration outputs for
  some other graph is open. (`notMax_solvesAt`; `theorem5`)
* **Algorithm WA (Theorem 7) can deadlock (under-specified handling of early messages).** The
  pseudocode does not say what happens to a phase-`p` message that arrives before `i` enters phase `p`.
  If the handler runs on arrival, as its wording suggests, then "on entering phase `p`" resets
  `Rᵢ[p]` and `heardᵢ[p]`, but phase-`p` messages can arrive and be marked as seen while `i` is still in
  phase `p − 1`. They are then lost: later copies are not "received for the first time". In a
  failure-free run on 5 nodes with `f = 1` (edges `0→1,2,3; 1→0,2,4; 2→0,1,3,4; 3→4`, which satisfies
  the condition of Theorem 6), node 4 gets the phase-2 messages of nodes 1 and 2 before finishing
  phase 1. In phase 2 it then waits forever: Condition WAIT would need `reach₄(F) ⊆ {0, 3, 4}` with
  `|F| ≤ 1`, but `reach₄({1}) ∋ 2` and `reach₄({2}) ∋ 1`. The run was found by simulating the
  pseudocode. If early messages are instead buffered until `i` enters phase `p` (and nodes keep
  relaying), simulation finds no deadlock. The fix is to keep early messages and re-check WAIT when entering a phase. The proof of
  Theorem 7 is only a sketch ("the rest of the proof is standard"). We prove the fixed algorithm correct, including the liveness and the
  `1 − 1/n` contraction per phase that the sketch omits (`theorem7`).
* **Algorithm MVC needs integer inputs.** "Inputs in the range `[0, K]`" must mean integers, because the
  OUTER-LOOP tests `tᵢ = l` for integers `l`. With all inputs equal to `1/2` and `K = 1`, everybody
  outputs `1`, which is nobody's input. We prove Theorem 4 for inputs in `{0, …, K}` (`theorem4`).
* **Minor proof gaps (statements true).**
  * Theorem 1 uses without proof that "no single root" means "some pair `i, j` without a common
    ancestor" (`ctConn_iff_oneReach`). Its validity step is made precise by indistinguishability with
    the all-0 execution.
  * The proof of Theorem 3 does not say that agreement persists after the clean pair of phases.
  * In Lemma 4, the case "nobody exits the OUTER-LOOP, output `K`" in fact never occurs for inputs in
    `[0, K]`.
  * Claim 3's "iff" holds only in the "only if" direction, which is the one used.
* **Typos.** Step 4 of MVC: `|min{b | …}| > 0` should be "`{b | …}` is non-empty". The induction step
  of Lemma 3 says "`l ≥ r`" for "`l ≤ r`". Claim 8 speaks of "sets of `2f + 1` values" of size
  `f + 1`; Claim 8 is not needed for the case analysis.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Synchronous* (`SyncModel.lean`). Static digraph `G` on a finite node set. Deterministic algorithms
  know `G` and the node identities. In lock-step rounds a node sends an optional message to each
  out-neighbour and updates its state from the messages received. Crash faults: a node crashing in
  round `c` behaves correctly before, reaches an adversarial subset of its out-neighbours in round
  `c`, and is silent afterwards. At most `f` crashes, chosen adversarially (they may depend on the
  inputs). Consensus = termination, agreement and validity (output = some node's input) for
  fault-free nodes. Theorem 1 holds against every algorithm in this model and uses only crashes before
  the start.
* *Iterative algorithms* (`Iterative.lean`). Binary values. A fixed transition function
  `Z : Multiset Bool → Bool` is applied to the own value plus the received values, in the same crash
  model. Two output conventions: eventual (`SolvesEventually`) and fixed iteration `T` (`SolvesAt`).
* *Asynchronous* (`Async.lean`). The event-driven model on digraphs of the PODC 2020 formalization
  (`Podc/ApproxConsensus/Async/Model.lean`, shared with the PODC 2020 paper): reliable FIFO links with adversarial
  finite delays and fairness on links between correct nodes. For Theorem 6 the faulty nodes are
  initially dead, which makes the impossibility stronger. For Theorem 7 (`AsyncCrash.lean`) nodes
  crash at arbitrary times: a crashed node takes no more steps, and its messages still in transit may
  or may not be delivered, which models a crash in the middle of a broadcast. Initially dead nodes are
  a special case (`crashSolvesOn_of_gen`). Validity: output between two inputs of any nodes. The input
  range `[lo, hi]` is known, so that `p_end` can be chosen.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 2 (CT node connectivity) ⇔ 1-reach | `CTConn`, `ctConn_iff_oneReach` | `Graph.lean` |
| Fault-tolerant diameter `d`, `d ≤ n − 1` | `ftDiam`, `ftDiam_le_card` | `Graph.lean` |
| Theorem 1 (necessity) | `theorem1` | `Necessity.lean` |
| Theorem 3 (Min-Max correct, any phase length `D ≥ d`) | `theorem3` | `MinMax.lean` |
| Theorem 2 (binary consensus achievable) | `theorem2` | `MinMax.lean` |
| Tight condition, binary | `binary_consensus_iff` | `MinMax.lean` |
| Theorem 4 (MVC correct, inputs `0..K`), Claims 2, 5, 6, Lemma 3 | `theorem4`, `claim2`, `t_input`, `inv_iteration` | `MVC.lean` |
| Tight condition, multi-valued (`K ≥ 1`) | `consensus_iff` | `MVC.lean` |
| Theorem 5 (eventual outputs, every `f`) | `theorem5` | `Iterative.lean` |
| Theorem 5's graph with fixed-iteration outputs (`f = 1`): **solvable** | `notMax_solvesAt` | `IterativeCounterexample.lean` |
| Theorem 6 (necessity, async) | `theorem6`, `theorem6'` | `Async.lean` |
| Lemma 1 (graph part) | `lemma1` | `Async.lean` |
| Theorem 6 in the general crash model | `theorem6_gen` | `AsyncCrash.lean` |
| Theorem 7 (fixed Algorithm WA, `(1 − 1/n)^{p_end}(hi − lo) ≤ ε`) | `theorem7` | `WALive.lean` (`WA.lean`, `WASafety.lean`) |
| Tight condition, async (`0 < ε < hi − lo`) | `async_consensus_iff` | `WALive.lean` |

The agreement argument of Min-Max is proved once for any binary trajectory that follows the Min/Max
rule (`minmax_core`) and reused for MVC's INNER-LOOP. The clean pair of phases is found by
pigeonhole over the `f + 1` disjoint (Max, Min) pairs.

**Not formalized.** The literal (deadlocking) pseudocode of Algorithm WA; its deadlock was found and
checked only by simulation. Whether Theorem 5 holds with fixed-iteration outputs for some other graph
is not settled.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. `notMax_solvesAt` is checked by kernel evaluation (`decide +kernel`) over all delivery
patterns with at most one crash. Non-vacuity: the graph of Appendix B satisfies the condition, and
Min-Max and MVC run on it; `theorem7` exhibits an algorithm for the hypothesis of Theorem 6 (`consensus_on_pGraph`); two isolated nodes admit no consensus algorithm
(`no_consensus_disconnected`). The reach sets and 2-reach ⇔ CCA (`cca_iff_twoReach`) come from the shared library
`Podc/ApproxConsensus/DigraphConditions.lean` (bounded walks: CSLib's `Relation.RelatesWithinSteps`),
the asynchronous model and the two-phase replay lemma `exists_replay₂` from
`Podc/ApproxConsensus/Async/`. CSLib candidates:
`Graph.lean` (CT connectivity, fault-tolerant diameter), `SyncModel.lean`
(synchronous crash model on digraphs), `MinMaxCore.lean` (Min/Max agreement core), `AsyncCrash.lean`
(asynchronous crash model with crash schedules). The Python scripts
used for the bounded searches are not part of the Lean development.
