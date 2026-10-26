# Asynchronous Byzantine Approximate Consensus in Directed Networks — PODC 2020

Dimitris Sakavalas, Lewis Tseng, Nitin H. Vaidya. *Asynchronous Byzantine Approximate Consensus in
Directed Networks.* PODC 2020. DOI [10.1145/3382734.3405724](https://doi.org/10.1145/3382734.3405724).
Formalized version: arXiv [2004.09054](https://arxiv.org/abs/2004.09054) v1 (the only version);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main result (Theorem 4) holds. Asynchronous approximate
Byzantine consensus on a directed graph is solvable iff the graph satisfies 3-reach. We prove this
end to end in one asynchronous message-passing model with **FIFO links** (the paper does not assume
FIFO links): the paper's Algorithm BW + Filter-and-Average, implemented message by message, solves
the problem under 3-reach, and nothing solves it without 3-reach. Necessity in the FIFO model is the
stronger statement. Sufficiency, and hence the end-to-end theorem, is proved only for FIFO links.
This needs three fixes:
* the paper is inconsistent about whether a stored path ends at the receiver, and under either
  reading the algorithm never makes progress; we use the evident intent;
* the update rule `(max − min)/2` must be `(max + min)/2`;
* the known input range `[0, K]`, which Section 4.6 assumes explicitly, must be added to Definition 1
  and Theorem 4.

Several proof steps (Theorems 10, 11, 14, Lemma 8) also needed repairs.

## Mistakes in the paper

* **The message-set definitions are inconsistent, and under either reading the algorithm never makes
  progress (under-specified definition).**
  * *Paths stored by `v` end at `v`* (Definition 9). An `f`-cover (Definition 4) may contain any
    `≤ f` nodes, so `{v}` covers every message `v` holds. Then Algorithm 2 (`Completeness`) never
    holds: take `Fw` with `v ∈ Fu ∪ Fw`, so that `v ∉ S_{Fu,Fw}`. FIFO-Receive-All always includes
    `v`'s own `COMPLETE(Fv)`, so `Verify` fails in every thread forever. Algorithm 3 would trim
    everything.
  * *Paths end at the sender* (Appendix E). Then no stored path has `ter(p) = v`, so no message set
    is ever full for `(A, v)` (Definition 9), and Maximal-Consistency never fires.

  The intent is evident: a node never suspects itself. Thread sets satisfy `Fv ⊆ V \ {v}` (line 5),
  covers in Lemma 8 (Eq. (1)) avoid `v`, and footnote 5 says the same. We fix it accordingly: paths
  end at `v`, and `v` is never in a cover. The Lean counterexample for the first reading
  (`RoundExec.never_verifyLit`) is proved in the abstract round model `RoundExec` for every round
  execution, including the fault-free one on `K₄` with `f = 1`. It is not proved for an operational
  run of the literal algorithm. (`RoundExec.never_verifyLit`, `not_completenessLit`, `not_isFALit`)
* **Typo with real consequences: `(max − min)/2`.** It appears in Algorithm 3, line 5, in the proof of
  Lemma 15 and in Appendix G. `x_v[r+1] = (max O' − min O')/2` breaks validity: all inputs `1` give
  `0`. It must be `(max + min)/2`; the proofs' inequalities are those of `(max + min)/2`.
  (`minus_update_invalid`)
* **The known input range is missing from the statements.** Section 4.6 states explicitly that the
  inputs lie in `[0, K]` with `K` known to all nodes, and the termination argument needs this. The
  assumption is missing only from Definition 1 and Theorem 4. We prove
  Theorem 4 in that setting with `0 < ε < K`; for `K ≤ ε` the problem is trivial. The necessity
  also holds for arbitrary real inputs. With unbounded inputs and no known bound, the sufficiency
  stays open, as in the paper. (`theorem4`, `threeReach_of_solves`)
* **Proof gaps, statements true.**
  * *Theorems 10, 11 and 14* use the common values `R_{F_lo}` for the trimming cover `F_lo`, but
    `R_W` is defined only for `W ≠ F_t`, and `F_lo = F_t` is possible. For `f = 0` the index set
    is empty. When the cover is `F_t`, any other `W` works. (`theorem10`)
  * *Theorem 10* needs FIFO order along the specific path `c → v`. Appendix F defines
    FIFO-receive by receipt along any path, under which a forged copy on a Byzantine path would
    satisfy the condition. We use per-path FIFO-receive with counters.
  * *Lemma 8, Case II* claims the `f+1` paths into `z` "trivially" have no `f`-cover outside `S`.
    `{z}` covers them; the argument works only because the relevant `F'` avoids `z`. Lemma 8
    also holds without its extra hypotheses. (`completeness_eventually`)
  * *Theorem 14* handles duplicate values informally. We bypass Lemma 13 and Theorem 14: Theorem 12
    directly gives a value `x_q` with `min O'_v ≤ x_q ≤ max O'_u`, which is all Lemma 15 needs.
    (`pair_le`)
  * *Theorem 18* uses inputs `0` and `ε`, which are still "within `ε`"; inputs `0` and `2ε` (any
    two more than `ε` apart) fix this. Its executions are not fully specified; we construct the
    replay explicitly. (`threeReach_of_solvesOn`)
* **Minor slips.**
  * In a clique, 1-reach always holds, not "iff `n > f`". 2- and 3-reach also hold for `n = 1`.
  * `U[r+1] − μ[r+1] ≤ (U[0] − μ[0])/2^r` should be `/2^{r+1}`; the stated bound is still true.
  * Theorems 5 and 12 do not need their disjointness hypotheses.
  * Nodes must keep relaying after they output; the paper does not say so.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A finite node set with a known directed graph `G` (Mathlib `Digraph`; self-loops ignored).
* Deterministic event-driven algorithms, reliable FIFO links with arbitrary finite delays.
* A static set of `≤ f` Byzantine nodes that may deliver arbitrary messages to their out-neighbours
  at any time (full-information adversary).
* Fairness: every non-empty link between correct nodes is eventually served.
* Specification (`SolvesOn I`): for inputs in `I`, decisions of correct nodes are within `ε` and
  between two correct inputs at every time (all event sequences), and in fair runs every correct
  node decides.
* Links are FIFO in Lean but not in the paper. For necessity this is a strengthening: impossibility
  with FIFO links implies impossibility without them. For sufficiency it is a restriction:
  `bw_solves` and `theorem4` are proved only for FIFO links. FIFO-receive does use counters as in
  Appendix F, but the delivery argument (`chan_inv`, `eventually_received`) is stated for FIFO
  channels. We have not proved that the algorithm also works over non-FIFO links.
* The algorithm is implemented as a full-information state machine (input + history). Every
  "upon …"/"for the first time" condition of Algorithm 1 is evaluated on prefixes of the history,
  and a node runs `outRound K ε` rounds.

**Structure of the sufficiency proof.**
* `RoundModel.lean` describes one round by what correct nodes have received over time, plus the
  guarantees of RedundantFlood and FIFO-Flood (`RoundExec`). The paper's Lemmas 6–15 and
  Theorem 16 are proved at this level.
* `Operational/` proves that every fair run of the real algorithm yields such rounds (`mkRound`).
  No field of `RoundExec` is assumed.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4 (iff, end to end, inputs in `[0,K]`, `0 < ε < K`) | `theorem4` | `Operational/Theorem4.lean` |
| Theorem 4, sufficiency: BW + FA works | `BWOp.bw_solves` | `Operational/Theorem4.lean` |
| Theorem 18 (necessity) | `threeReach_of_solvesOn`, `threeReach_of_solves` | `Necessity.lean` |
| Definition 3 (1/2/3-reach), cliques | `OneReach`, `TwoReach`, `ThreeReach` (shared library); `threeReach_top_iff`, `twoReach_top_iff`, `oneReach_top` | `Cslib/Computability/Distributed/ApproxConsensus/DigraphConditions.lean`, `Graph.lean` |
| Theorem 5 (cover form) | `ThreeReach.theorem5` | `Graph.lean` |
| Theorem 12 | `ThreeReach.theorem12` | `Graph.lean` |
| Theorem 17 (a), (b), (c) | `theorem17a`, `theorem17b`, `theorem17c` | `Conditions.lean` |
| Lemma 6 | `RoundExec.sent_actual` | `BW.lean` |
| Lemma 7 | `RoundExec.lemma7` | `BW.lean` |
| Lemma 8 | `RoundExec.completeness_eventually` | `BW.lean` |
| Theorem 9 | `RoundExec.exists_executes` | `BW.lean` |
| Theorems 10 + 11 | `RoundExec.theorem10` (`leader_witnessed`, `follower_witnessed`) | `Round.lean` |
| Lemma 15 (via `pair_le`; replaces Lemma 13, Theorem 14) | `RoundExec.output_conv` | `Round.lean` |
| Theorem 16 (validity) | `RoundExec.output_valid`, `Exec.valid` | `Round.lean`, `Main.lean` |
| Section 4.6 (convergence, termination) | `Exec.spread_le`, `Exec.converges`, `Exec.termination` | `Main.lean` |
| Literal algorithm never progresses; `(max − min)/2` | `RoundExec.never_verifyLit`, `not_isFALit`, `minus_update_invalid` | `Literal.lean` |
| Comparison with iterative BC (PODC'12) | `threeReach_of_vtl`; strictness `exampleGraph_threeReach`, `exampleGraph_not_vtl` | `Conditions.lean` |

The PODC 2012 condition for *iterative* approximate BC (formalized in
`Papers/PODC2012/IterativeApproxBC`) implies 3-reach. The implication is strict: a 5-node digraph
with `f = 1` satisfies 3-reach but not the iterative condition.

**Not formalized.** Theorems 1–3 (cited results of Tseng–Vaidya), Menger's theorem for digraphs
(Theorem 5 is used in its equivalent cover form), the `k`-reach family (Definition 20), and
Theorem 14 as stated.

**Trust.** No `sorry`; `theorem4` and all listed theorems use only `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity:
* the fault-free round `RoundExec.faultFree` and whole execution `Exec.faultFree`;
* `threeReach_K4` (`K₄`, `f = 1`), so the theorems apply to actual instances;
* `theorem4` is itself non-vacuous: under 3-reach the algorithm exists, and the model admits fair
  runs (`exists_fair_extension`).

**Shared infrastructure.** The asynchronous model (`Algorithm`, `run`, `Fair`, `SolvesOn`) is
`Cslib/Computability/Distributed/ApproxConsensus/Async/Model.lean` and the replay machinery of Theorem 18 (`proj`, `sim_phase`,
the two-phase replay `exists_replay₂`, `roundRobin`) is `Cslib/Computability/Distributed/ApproxConsensus/Async/Replay.lean`;
both are also used by `Papers/PODC2015/CrashConsensusDigraph`. Reach sets (`Reaches` =
`Digraph.ReachableAvoiding`, `Cslib/Foundations/Combinatorics/Digraph/Walk.lean`), the 1/2/3-reach conditions, CCS/CCA/BCS,
`partCond_iff` and the iterative condition of PODC'12 with its implication to BCS are
`Cslib/Computability/Distributed/ApproxConsensus/DigraphConditions.lean`. The paper-specific parts (source components of
reduced graphs, paths, the algorithms and their proofs) live in this folder. No CSLib model fitted
directly: CSLib's asynchronous model is crash-only on complete graphs, and its iterative
approximate-consensus model is synchronous.
