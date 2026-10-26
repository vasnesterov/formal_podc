# Distributed k-Core Decomposition — PODC 2011

Alberto Montresor, Francesco De Pellegrini, Daniele Miorandi. *Distributed k-core decomposition.*
PODC 2011 (brief announcement). DOI [10.1145/1993806.1993836](https://doi.org/10.1145/1993806.1993836).
Formalized version: arXiv [1103.5320](https://arxiv.org/abs/1103.5320) v2 (full version); numbering
follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The algorithm is correct. Estimates never increase, never drop
below the coreness, and converge to it, both in the one-node-per-host version (synchronous and
asynchronous) and in the many-nodes-per-host version. The bounds of Theorem 4 (`1 + Σ(d − k)`),
Theorem 5 (`N`) and Corollary 1 (`N − K + 1`) hold. Two quantitative claims are wrong. The "worst-case"
family of Fig. 3 needs `N − 2` rounds, not `N − 1` (a false side claim, not a typo; the theorems are unaffected). The message bound of Corollary 2 ignores the
initial broadcast. The proofs of Theorems 3 and 5 have gaps.

## Mistakes in the paper

* **The worst-case family needs N − 2 rounds, not N − 1 (§4.2, Fig. 3).** The paper claims a family
  (hub `N` joined to all nodes but `N − 3`, a path `1 – 2 – … – N − 1`, and the chord
  `(N − 3, N − 1)`) whose execution time is exactly `N − 1` for every `N ≥ 5`. In the paper's own
  synchronous model and with its own definition of execution time, it is `N − 2`. That accounting
  gives the 3 rounds of the Fig. 2 example. Round 1 broadcasts the degrees; already in that round
  node 2 drops to 2 and the hub to 3. Nodes 3, …, N − 4 then drop one per round, and two more
  rounds settle `N − 3, N` and then `N − 2, N − 1`. The paper counts the initial round twice. This
  is a false statement, off by one. The Introduction's claim that the family "requires exactly"
  the upper bound `N − K + 1` (`= N` here, since `K = 1`) is further off. An exhaustive search over
  all graphs with `N ≤ 8` nodes (computational, not formalized) finds a maximum execution time of
  `N − 2` for `4 ≤ N ≤ 8`. So the family is optimal there, and the bound `N` is never reached.
  (`worstGraph_execTime`)
* **Corollary 2 ignores the initial broadcast.** The bound `Σ_v d(v)² − 2M` counts only update
  messages. Algorithm 1 also sends every degree to every neighbour at initialization, which is
  `2M` messages. For a single edge the bound is `0`, but 2 messages are sent. This is an imprecise
  statement. We prove the bound for update messages, and `Σ_v d(v)²` for all messages.
  (`corollary_2_false`, `corollary_2_updates`, `total_messages_le`)
* **Theorem 5's proof is off by one and then incomplete; the statement is true.** The proof says
  "the execution time equals T + 1", where `T` is the first round in which all estimates are
  correct. In the model of §4.2 it equals `T`: in Fig. 2, `T = 3` and the time is 3. (With the
  indexing of the Fig. 2 narrative, `T + 1` is right, and the lost round is instead that the nodes
  of minimal degree are correct already before round 1.) To compensate, the proof
  adds an argument for `T ≤ N − 1` about the last two wrong nodes. That argument skips the case
  where they become correct in consecutive rounds. The real content is the progress claim: in each
  round some wrong node of minimal coreness becomes correct. With the correct accounting this gives
  `execTime ≤ N − K + 1 ≤ N` at once. The paper argues the progress claim only informally; we
  prove it. (`progress`, `corollary_1`, `theorem_5`)
* **Theorem 3's induction step has a gap; the statement is true.** The proof builds a cycle of
  stuck nodes of coreness `k` and assumes each of them has `k` neighbours of coreness `> k`
  ("the remaining f − 1 ≥ k neighbors of u₁ have coreness k + 1 or more"). Nothing guarantees
  this: such a node may have many neighbours of coreness exactly `k`. We use a fixpoint argument
  instead. A stable estimate vector `c` with `c(u) ≤ h-index of the neighbours' c` lies below the
  coreness, since `{v : c(v) ≥ c(u)}` induces minimum degree `≥ c(u)`. (`le_coreness_of_le_hIndex`,
  `theorem_3`)
* **Typos and small slips.** In Theorem 1's proof (⇐), "d_{G(U)}(v) ≥ k + 1" should be `≥ k`. In
  Theorem 2's proof, "|V₁| = k(u)" should be `k(u₁)`, and "⟨u₂, core(u₃)⟩" should be
  `⟨u₃, core(u₃)⟩`. Algorithm 2 returns `1`, not `0`, when no neighbour has estimate `≥ 1`; this is
  harmless, because it never happens in a run. The Fig. 3 family has diameter 2 (not 3) for
  `N = 5, 6`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A finite simple graph `G : SimpleGraph V`. Definitions 1–2 are formalized literally: `IsKCore` is
  the maximum induced subgraph of minimum degree `≥ k`, `kCore` is its unique witness, and
  `coreness` is the largest `k` with `u ∈ kCore k`. Estimates live in `ℕ∞`, with `⊤` = `+∞`.
* **Synchronous rounds (§4.2), Algorithm 1 at message level** (`Run.lean`). Round 1 broadcasts the
  degrees. In each later round a node processes the previous round's messages with Algorithm 1's
  handler, which calls Algorithm 2's `computeIndex` after every lowering of `est`. The messages are
  processed in an **arbitrary order**, and the node broadcasts iff `changed`. All results hold for
  every order. Execution time is the number of rounds in which some node broadcasts, as in the paper.
* **Asynchronous Algorithm 1** (`Async.lean`), used for Theorems 2–3 in the paper's general
  setting. Reliable channels with arbitrary delays and reordering, no crashes, and arbitrary
  scheduling of the periodic `repeat every δ` block. Liveness assumes fairness: every node ticks
  infinitely often and every message is eventually delivered.
* **One host, many nodes** (`MultiHost.lean`): Algorithms 3–4 in synchronous rounds with an
  arbitrary node-to-host assignment. Each host runs `improveEstimate` to a local fixpoint. The result
  is the greatest quiescent vector below the input, so it does not depend on the pass order, and
  processing messages one at a time gives the same state as processing them together. Hosts then
  broadcast the changed estimates of their own nodes. Messages are delivered to all other hosts,
  following the text of §3.2. Besides safety and liveness, we prove that after round `s + 1` the
  estimates are at most those of the one-to-one algorithm. So the one-to-many version needs at most
  as many rounds.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1, 2 | `IsKCore`, `isKCore_kCore`, `IsKCore.eq_kCore`, `coreness_eq_iff` | `Basic.lean` |
| Algorithm 2 (`computeIndex`) | `computeIndex`, `computeIndex_eq` | `Basic.lean` |
| Theorem 1 (locality) | `theorem_1`, `coreness_eq_hIndex` | `Basic.lean` |
| Run of Algorithm 1 = trajectory | `run_spec`, `execTime_eq` (`execTime = stab + 1`) | `Run.lean` |
| Theorem 2 (safety), synchronous | `theorem_2`, `core_succ_le` | `Run.lean` |
| Theorem 3 (liveness), synchronous | `theorem_3` | `Run.lean` |
| Theorems 2, 3, asynchronous | `Async.theorem_2`, `Async.theorem_3` (fairness `Async.Fair`; satisfiable: `Async.exists_fair`) | `Async.lean` |
| Theorem 4 (`≤ 1 + Σ(d − k)`) | `theorem_4` | `Run.lean` |
| Theorem 5 (`≤ N`) | `theorem_5` | `Run.lean` |
| Corollary 1 (`≤ N − K + 1`) | `corollary_1` (also `execTime_le_card_sub_correct`) | `Run.lean` |
| Progress claim in the proof of Thm 5 | `progress` | `Trajectory.lean` |
| Fig. 3 family: `N − 1` rounds (false) | `worstGraph_execTime` (`= N − 2`), `worstGraph_execTime_ne`; trajectory `traj_worstGraph`, `stab_worstGraph` | `Examples.lean`, `WorstCase.lean` |
| Linear chain: `⌈N/2⌉` rounds | `pathGraph_execTime` | `Examples.lean` |
| Fig. 2 example: 3 rounds, corenesses | `fig2_execTime`, `coreness_fig2` | `Examples.lean`, `WorstCase.lean` |
| Corollary 2 (messages) | `corollary_2_updates`, `total_messages_le`; literal reading false: `corollary_2_false` | `Run.lean` |
| §3.2 one host, many nodes: safety, liveness | `MultiHost.safety`, `MultiHost.liveness`, `MultiHost.theorem_3_multiHost` | `MultiHost.lean` |
| (new) one-to-many never slower than one-to-one | `MultiHost.ownEst_le_traj` | `MultiHost.lean` |
| Algorithm 4 terminates; result independent of order | `MultiHost.improveEstimate_isGreatest`, `MultiHost.run_succ_host_eq_receiveSeq` | `MultiHost.lean` |

**Not formalized.** Termination detection (§3.3), the point-to-point optimizations of §3.1.2 and
Algorithm 5 (the latter, as printed, resends all boundary estimates every round and so never becomes
silent), the host-assignment policy, and the experiments (§5).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The synchronous theorems are about an explicit, total run function, so they are not
vacuous. The Fig. 2 and Fig. 3 computations exercise them on concrete graphs. Everything is
self-contained over Mathlib's `SimpleGraph`. The k-core / coreness / locality API in `Basic.lean`
is a CSLib candidate.
