# Asynchronous Byzantine Approximate Consensus in Directed Networks — PODC 2020

Dimitris Sakavalas, Lewis Tseng, Nitin H. Vaidya. *Asynchronous Byzantine Approximate Consensus in
Directed Networks.* PODC 2020. DOI [10.1145/3382734.3405724](https://doi.org/10.1145/3382734.3405724).
Formalized version: arXiv [2004.09054](https://arxiv.org/abs/2004.09054) v1 (the only version);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The main result (Theorem 4) holds: asynchronous approximate Byzantine consensus on a directed
graph is solvable iff the graph satisfies 3-reach, and the paper's Algorithm BW + Filter-and-Average, implemented
message by message, solves the problem under 3-reach, after local fixes to the message sets and covers (the paper is
inconsistent about whether a stored path ends at the receiver), to FIFO-Receive, to the update rule (`(max − min)/2`
must be `(max + min)/2`) and to several proof steps (Theorems 10, 11, 14, 18, Lemma 8). We prove this end to end in one
asynchronous message-passing model with **FIFO links**, with the known input range `[0, K]` that Section 4.6 assumes
added to Definition 1 and Theorem 4. The paper does not assume FIFO links: necessity in the FIFO model is the stronger
statement, but sufficiency over non-FIFO links, and hence the end-to-end theorem there, was not checked.

## Mistakes in the paper

### 🔧 Definitions 4, 9 and Appendix E (message sets; the algorithm never makes progress)
The paper is inconsistent about whether a stored path ends at the receiver, and under either reading Algorithm BW
never makes progress, e.g. with paths ending at `v` the set `{v}` is an `f`-cover of everything `v` holds, so
`Verify` fails in every thread forever (`RoundExec.never_verifyLit`).

**Impact.** Algorithms 2, 3 and Appendix E must change. With the fix below the algorithm works and Theorem 4 holds.

**Details.**
* *Paths stored by `v` end at `v`* (Definition 9). An `f`-cover (Definition 4) may contain any `≤ f` nodes, so
  `{v}` covers every message `v` holds. Then Algorithm 2 (`Completeness`) never holds: take `Fw` with
  `v ∈ Fu ∪ Fw`, so that `v ∉ S_{Fu,Fw}`. FIFO-Receive-All always includes `v`'s own `COMPLETE(Fv)`, so `Verify`
  fails in every thread forever. Algorithm 3 would trim everything.
* *Paths end at the sender* (Appendix E). Then no stored path has `ter(p) = v`, so no message set is ever full for
  `(A, v)` (Definition 9), and Maximal-Consistency never fires.

The intent is evident from the paper: thread sets satisfy `Fv ⊆ V \ {v}` (line 5), covers in Lemma 8 (Eq. (1))
avoid `v`, and footnote 5 says the same. The Lean counterexample for the first reading
(`RoundExec.never_verifyLit`) is proved in the abstract round model `RoundExec` for every round execution,
including the fault-free one on `K₄` with `f = 1`. It is not proved for an operational run of the literal
algorithm. (`RoundExec.never_verifyLit`, `not_completenessLit`, `not_isFALit`)

**Repair.** A node never suspects itself: paths end at `v`, and `v` is never in a cover.

### 🔧 Appendix F (FIFO-Receive)
Appendix F defines FIFO-receive by receipt along any path, under which a forged copy on a Byzantine path would satisfy
the condition, while Theorem 10 needs FIFO order along the specific path `c → v`.

**Impact.** The printed rule does not give what Theorem 10 uses. Theorem 10 is proved from the per-path guarantee
(`theorem10`).

**Repair.** We use per-path FIFO-receive with counters (`fifoCR`).

### ✏️ Slips
- **Algorithm 3, line 5.** The update `x_v[r+1] = (max O' − min O')/2` breaks validity: all inputs `1` give `0`
  (`minus_update_invalid`). It must be `(max + min)/2`, and the proofs' inequalities are those of `(max + min)/2`. It
  also appears in the proof of Lemma 15 and in Appendix G.
- **Definition 1 and Theorem 4 (known input range).** Section 4.6 states explicitly that the inputs lie in `[0, K]`
  with `K` known to all nodes, and the termination argument needs this, but the assumption is missing from Definition 1
  and Theorem 4. We prove Theorem 4 in that setting with `0 < ε < K`; for `K ≤ ε` the problem is trivial. The necessity
  also holds for arbitrary real inputs. (`theorem4`, `threeReach_of_solves`)
- **Cliques.** In a clique, 1-reach always holds, not "iff `n > f`". 2- and 3-reach also hold for `n = 1`.
- **`n = 1`.** 3-reach holds vacuously and source components may meet `F₁ ∪ F₂`, which the sufficiency proofs
  implicitly exclude. Consensus is trivial there (`trivAlg_solves`).
- **After output.** Nodes must keep relaying after they output; the paper does not say so.

### Typos
- `U[r+1] − μ[r+1] ≤ (U[0] − μ[0])/2^r` should be `/2^{r+1}`; the stated bound is still true.

## Proof gaps (statements true)

### 🔧 Theorems 10, 11 and 14 (common values for the trimming cover)
The proofs use the common values `R_{F_lo}` for the trimming cover `F_lo`, but `R_W` is defined only for
`W ≠ F_t`, and `F_lo = F_t` is possible.

**Impact.** Statements true; repaired (`theorem10`, `pair_le`).

**Details.** For `f = 0` the index set is empty. When the cover is `F_t`, any other `W` works. (`theorem10`)

### 🔧 Lemma 8, Case II
The proof claims the `f+1` paths into `z` "trivially" have no `f`-cover outside `S`, but `{z}` covers them.

**Impact.** Statement true: the argument works only because the relevant `F'` avoids `z`. Lemma 8 also holds
without its extra hypotheses. (`completeness_eventually`)

### 🔧 Theorem 18 (necessity)
The proof uses inputs `0` and `ε`, which are still "within `ε`", and its executions are not fully specified.

**Impact.** Statement true: inputs `0` and `2ε` (any two more than `ε` apart) fix this, and we construct the replay
explicitly. (`threeReach_of_solvesOn`)

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

Theorems 5 and 12 do not need their disjointness hypotheses.

**Not formalized.** Theorems 1–3 (cited results of Tseng–Vaidya), Menger's theorem for digraphs
(Theorem 5 is used in its equivalent cover form), the `k`-reach family (Definition 20), and
Lemma 13 and Theorem 14 as stated: Theorem 14 handles duplicate values informally, and we bypass both, since
Theorem 12 directly gives a value `x_q` with `min O'_v ≤ x_q ≤ max O'_u`, which is all Lemma 15 needs (`pair_le`).
Sufficiency over non-FIFO links is open here (see **Model**), and the round-level results (`RoundExec`) do not depend
on it. With unbounded inputs and no known bound, the sufficiency stays open, as in the paper.

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
