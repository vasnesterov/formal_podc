# formal_podc: Lean 4 formalizations of PODC papers

Machine-checked formalizations of papers from the ACM Symposium on Principles of Distributed Computing
(PODC), 2012–2026, in [Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4)
and [CSLib](https://github.com/vasnesterov/cslib).

The goal is to **verify the results and the proofs** of each paper. Every formalized paper has its own folder
`Papers/PODC<Year>/<ShortName>/` with

- the Lean files (no `sorry`, no extra axioms: the main theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`),
- `README.md`: the paper reference, the model (synchrony, failures, adversary, randomness), and a table
  mapping the paper's theorems to Lean names,
- `differencies.md`: **every** difference between the formalization and the paper — missing assumptions,
  false or imprecise statements, gaps in proofs, changed constants — with Lean counterexamples where a claim is
  false, and the repaired statements that we proved instead.

General infrastructure developed along the way (Byzantine round models, asynchronous shared memory and
linearizability, population protocols, the LOCAL model, self-stabilization, Menger's theorem, the Moore bound,
graph minors, spanners, Markov-chain absorption, social choice, …) lives in the CSLib fork
[`vasnesterov/cslib`](https://github.com/vasnesterov/cslib), branch `podc`.

The formalizations were produced by AI agents (Claude) under human direction. Each paper was then checked by an
independent reviewer agent for faithfulness of definitions and statements and for over-claimed errors.
The Lean kernel checks every proof; whether a Lean statement faithfully captures the paper is a judgment, and
the reasoning is recorded in each `differencies.md`.

## Building

```bash
# requires elan (https://github.com/leanprover/elan)
lake exe cache get   # Mathlib cache
lake build
```

The toolchain is pinned in `lean-toolchain` (it matches CSLib's).

## Formalized papers

Verdicts:
- ✅ **correct** — results hold as stated; at most typos, minor gaps or implicit conventions;
- ⚠️ **correct with fixes** — the main results hold, but the paper has genuine proof errors/gaps, statements that
  fail in edge cases, or under-specified definitions (all repaired in the formalization);
- ❌ **false claim** — some stated theorem, corollary or algorithm claim of the paper is false
  (counterexample in Lean); see [below](#papers-with-critical-mistakes).

Sorted by citation count (the maximum of the OpenAlex and Semantic Scholar counts, October 2026).

| Year | Citations | Paper | Folder | Verdict |
|---|---|---|---|---|
| 2012 | 221 | Vaidya, Tseng, Liang — *Iterative Approximate Byzantine Consensus in Arbitrary Directed Graphs* | [IterativeApproxBC](Papers/PODC2012/IterativeApproxBC) | ✅ Full characterization proved; a gap in the necessity proof repaired |
| 2018 | 79 | Barenboim, Elkin, Goldenberg — *Locally-Iterative Distributed (Δ+1)-Coloring below Szegedy–Vishwanathan Barrier* | [LocallyIterativeColoring](Papers/PODC2018/LocallyIterativeColoring) | ❌ Section 3 correct; **Corollaries 7.2–7.3 false** (3AG never terminates); §1.2 round claim false |
| 2016 | 68 | Censor-Hillel, Haramaty, Karnin — *Optimal Dynamic Distributed MIS* | [DynamicMIS](Papers/PODC2016/DynamicMIS) | ⚠️ Main results proved; Lemma 3 "= 1/\|P\|" false for edge changes (≤ holds) |
| 2021 | 49 | Kuznetsov, Tonkikh, Zhang — *Revisiting Optimal Resilience of Fast Byzantine Consensus* | [FastByzantineConsensus](Papers/PODC2021/FastByzantineConsensus) | ✅ Tight bound n ≥ 3f+2t−1 proved both ways; one proof gap repaired |
| 2018 | 35 | Függer, Nowak, Schwarz — *Tight Bounds for Asymptotic and Approximate Consensus* | [AsymptoticConsensus](Papers/PODC2018/AsymptoticConsensus) | ❌ Lower bounds proved and tight; **Theorem 4 (⇐) false** |
| 2020 | 31 | Dinitz, Robelle — *Efficient and Simple Algorithms for Fault-Tolerant Spanners* | [FaultTolerantSpanners](Papers/PODC2020/FaultTolerantSpanners) | ✅ Correct |
| 2019 | 31 | Bodwin, Patel — *A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners* | [VFTSpannersOptimal](Papers/PODC2019/VFTSpannersOptimal) | ⚠️ Theorem 1, Corollary 2 proved; Theorem 1 as stated degenerates for f > n/2; literal Algorithm 1 imprecise |
| 2021 | 29 | Ghaffari, Haeupler — *Low-Congestion Shortcuts for Graphs Excluding Dense Minors* | [LowCongestionShortcuts](Papers/PODC2021/LowCongestionShortcuts) | ⚠️ Main theorem proved (8δ+1 blocks; 8δ fails on the one-vertex graph); several proof errors (incl. a failing Lemma 3.2 construction); Observation 2.6 false as stated |
| 2019 | 29 | Khan, Naqvi, Vaidya — *Exact Byzantine Consensus on Undirected Graphs under Local Broadcast Model* | [LocalBroadcastBC](Papers/PODC2019/LocalBroadcastBC) | ⚠️ Characterization proved (Menger's theorem formalized); Thm 4.1 fails for a single node; sufficiency proof gaps repaired |
| 2016 | 25 | Ellen, Gelashvili, Shavit, Zhu — *A Complexity-Based Hierarchy for Multiprocessor Synchronization* | [ComplexityHierarchy](Papers/PODC2016/ComplexityHierarchy) | ⚠️ Space lower bounds and matching upper bounds proved; Lemma 9.1 proof gap; Lemma 7.1 proof wrong (statement true); Lemma 8.2 false in an edge case that is never used |
| 2021 | 24 | Emek, Keren — *A Thin Self-Stabilizing Asynchronous Unison Algorithm* | [ThinUnison](Papers/PODC2021/ThinUnison) | ❌ Theorem 1.1 proved (gaps repaired); **Corollary 1.2 false** for arbitrary tasks |
| 2023 | 22 | Civit, Gilbert, Guerraoui, Komatovic, Vidigueira — *On the Validity of Consensus* | [ValidityConsensus](Papers/PODC2023/ValidityConsensus) | ✅ Classification proved (with a verified vector-consensus protocol); minor gap in Lemma 3 for n < 2t |
| 2019 | 22 | Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel — *Optimal Memory-Anonymous Symmetric Deadlock-Free Mutual Exclusion* | [AnonymousMutex](Papers/PODC2019/AnonymousMutex) | ❌ **Theorem 2 false** (Algorithm 1 livelocks); the read/write characterization is only half proved |
| 2012 | 22 | Hirvonen, Suomela — *Distributed Maximal Matching: Greedy is Optimal* | [MaximalMatching](Papers/PODC2012/MaximalMatching) | ✅ Theorem 2 (k−1 rounds optimal) and Corollary 3 (Ω(Δ)) proved in both models; lower bounds extended to finite graphs |
| 2016 | 20 | Mostéfaoui, Raynal — *Two-Bit Messages are Sufficient to Implement Atomic Read/Write Registers in Crash-prone Systems* | [TwoBitRegisters](Papers/PODC2016/TwoBitRegisters) | ✅ Safety and liveness proved; non-FIFO channels suffice (as the paper claims); relies on atomic code blocks (implicit convention) |
| 2015 | 13 | Lenzen, Rybicki, Suomela — *Towards Optimal Synchronous Counting* | [SynchronousCounting](Papers/PODC2015/SynchronousCounting) | ⚠️ Theorems 1 and 3 proved; Theorem 1 false in the boundary case n = 1; Lemma 3 relies on a cited impossibility (proved here for n ≥ 3); Theorem 2's constant not established |
| 2024 | 12 | Civit, Gilbert, Guerraoui, Komatovic, Paramonov, Vidigueira — *All Byzantine Agreement Problems Are Expensive* | [AllBAExpensive](Papers/PODC2024/AllBAExpensive) | ⚠️ Proved; Lemma 10 / Theorem 4 (unauthenticated) false in the degenerate case n = 2, t = 1 |
| 2021 | 11 | Sela, Herlihy, Petrank — *Linearizability: A Typo* | [LinearizabilityTypo](Papers/PODC2021/LinearizabilityTypo) | ✅ Correct |
| 2024 | 10 | Tonkikh, Freitas — *Swiper: a new paradigm for efficient weighted distributed protocols* | [Swiper](Papers/PODC2024/Swiper) | ❌ Weight restriction/qualification proved; **Theorem 2.4 (weight separation) false** |
| 2022 | 9 | El-Hayek, Henzinger, Schmid — *Broadcasting Time in Dynamic Rooted Trees is Linear* | [DynamicRootedTrees](Papers/PODC2022/DynamicRootedTrees) | ✅ Upper and lower bounds proved; no errors |
| 2021 | 9 | Bodwin, Parter — *Restorable Shortest Path Tiebreaking for Edge-Faulty Graphs* | [RestorableTiebreaking](Papers/PODC2021/RestorableTiebreaking) | ⚠️ Theorem 2 (one scheme for every f) and the applications' correctness proved; Definition 17 omits connectivity after faults; Corollary 22's union bound miscounts fault sets (conclusion holds); proof gaps |
| 2022 | 8 | Rajsbaum, Raventós-Pujol — *A Distributed Combinatorial Topology Approach to Arrow's Impossibility Theorem* | [ArrowTopology](Papers/PODC2022/ArrowTopology) | ❌ Arrow's theorem and its topological proof verified; **Theorem 4.2 false** (corrected in the full version) |
| 2020 | 5 | Dolan — *The Only Undoable CRDTs are Counters* | [UndoableCRDTs](Papers/PODC2020/UndoableCRDTs) | ✅ Correct |
| 2025 | 4 | Constantinescu, Dufay, Ghinea, Wattenhofer — *Byzantine Stable Matching* | [ByzantineStableMatching](Papers/PODC2025/ByzantineStableMatching) | ⚠️ Characterizations proved for k ≥ 2; all "only if" directions false for k = 1; Lemma 13 reduction invalid |
| 2024 | 4 | Attiya, Bender, Farach-Colton, Oshman, Schiller — *History-Independent Concurrent Objects* | [HistoryIndependent](Papers/PODC2024/HistoryIndependent) | ⚠️ All results proved; impossibilities need ≥ 2 processes; Lemma 16 gap; Thm 32 for a fixed interleaving |
| 2024 | 3 | Chang, Mishra, Nguyen, Yang, Yeh — *A Tight Lower Bound for 3-Coloring Grids in the Online-LOCAL Model* | [OnlineLocalGrids](Papers/PODC2024/OnlineLocalGrids) | ⚠️ Theorems 1.1, 1.3 proved; Theorem 1.3 omits that √n must be odd |
| 2024 | 2 | Ovens — *Determining Recoverable Consensus Numbers* | [RecoverableConsensus](Papers/PODC2024/RecoverableConsensus) | ⚠️ Main theorem proved; proof errors in Lemmas 15 and 16 repaired |
| 2026 | 1 | Breitkopf, Dallot, El-Hayek, Schmid — *Ranking Opinions with Few States in Population Protocols* | [RankingOpinions](Papers/PODC2026/RankingOpinions) | ❌ Theorem 1.1 proved; **Theorem 4.1 false**; **the ranking protocol of Theorem 1.2 is incorrect** as written (fixed versions proved) |
| 2024 | 1 | Fuchs, Kuhn — *Simpler and More General Distributed Coloring Based on Simple List Defective Coloring Algorithms* | [ListDefectiveColoring](Papers/PODC2024/ListDefectiveColoring) | ⚠️ Theorems 1.1, 1.4 proved; Lemma 4.5 construction gap and Lemma A.1 proof error repaired |
| 2022 | 1 | Ovens — *The Space Complexity of Consensus from Swap* | [ConsensusFromSwap](Papers/PODC2022/ConsensusFromSwap) | ⚠️ All results proved for deterministic obstruction-free algorithms (Theorem 10 weaker than the paper's nondeterministic version); Lemma 16 and Theorem 10 proof gaps; valency definition ambiguous |
| 2026 | 0 | Attiya, Flam, Welch — *Why Canonical-Round Algorithms Fail for Optimal Byzantine Resilience* | [CanonicalRoundByzantine](Papers/PODC2026/CanonicalRoundByzantine) | ⚠️ Lower bounds proved (for 2f ≤ n ≤ 5f); Corollary 10's proof covers only part of the range (statement true); Theorem 14 implicitly uses the i = j case of gather agreement |
| 2026 | 0 | D'Archivio, AlMahmoud, Natale, Mallmann-Trenn — *Order Statistics in Population Protocols via Simple Dynamics* | [OrderStatisticsPP](Papers/PODC2026/OrderStatisticsPP) | ⚠️ Laws of the consensus value proved; both proofs of Proposition 6 invalid (statement true); Definition 4.2 under-specified |
| 2026 | 0 | Nolin — *Sinkless Orientation Made Trivial* | [SinklessOrientation](Papers/PODC2026/SinklessOrientation) | ✅ Correct (deterministic part); typos only |
| 2025 | 0 | Gafni, Losa, Raynal, Taubenfeld — *Stranger-Free Tasks* | [StrangerFreeTasks](Papers/PODC2025/StrangerFreeTasks) | ❌ Lower bound proved; **Algorithm 1 is not wait-free for k ≥ 2** |

## Papers with critical mistakes

Sorted by citation count. These papers contain a stated result that is **false** — not just a gap in a proof and not only in a degenerate
case. In each case the counterexample is checked by Lean; details, and the corrected statements we proved, are
in the paper's `differencies.md`.

- **Locally-Iterative Distributed (Δ+1)-Coloring** (PODC 2018, 79 citations) —
  [LocallyIterativeColoring](Papers/PODC2018/LocallyIterativeColoring). Algorithm 7 (3AG) never terminates:
  on a single edge with colours ⟨1,0,0⟩, ⟨1,0,1⟩ the two vertices keep equal b-values forever, for every p.
  Hence Corollaries 7.2 and 7.3 are false. The §1.2 claim that 2p+1 rounds suffice is also false (16-vertex
  tree, Δ = 4). The main Section 3 results are correct.
- **Tight Bounds for Asymptotic and Approximate Consensus** (PODC 2018, 35 citations) —
  [AsymptoticConsensus](Papers/PODC2018/AsymptoticConsensus). Theorem 4 (⇐), a characterization of when exact
  consensus is solvable via valencies, is false: a two-agent algorithm with a discontinuous limit function is a
  counterexample. The proof assumes the valency diameter vanishes, which needs continuity. We prove the theorem
  under that extra hypothesis. The lower bounds (the paper's main results) are correct and tight.
- **A Thin Self-Stabilizing Asynchronous Unison Algorithm** (PODC 2021, 24 citations) — [ThinUnison](Papers/PODC2021/ThinUnison).
  Corollary 1.2 (a synchronizer for arbitrary tasks) is false: a task solvable synchronously on complete graphs is
  solvable by no deterministic asynchronous algorithm already on K₂. It holds for static tasks (proved). The main Theorem 1.1
  is correct.
- **Optimal Memory-Anonymous Symmetric Deadlock-Free Mutual Exclusion** (PODC 2019, 22 citations) —
  [AnonymousMutex](Papers/PODC2019/AnonymousMutex). Theorem 2 claims that Algorithm 1 (read/write registers plus
  atomic snapshots) is deadlock-free whenever the number of registers m lies in M(n). It is not: for n = 4,
  m = 5 there is a fair, periodic 28-step execution in which processes keep competing and nobody ever enters the
  critical section (`theorem_2_false`). The proof ignores writes based on stale snapshots. Consequently the
  paper's tight characterization for read/write registers is unproven; only its necessity half holds (proved).
  The characterization for read-modify-write registers is correct.
- **Swiper** (PODC 2024, 10 citations) — [Swiper](Papers/PODC2024/Swiper). Theorem 2.4 (the upper bound
  (α+β)(1−α)/(β−α)·n on the number of tickets for weight separation) is false: a 21-party instance needs 63
  tickets against a bound of 59.85, and on a family of instances the optimum exceeds the bound by an unbounded
  factor. Swiper's own construction violates the bound already for 3 parties, and the proof of Appendix A.2 is
  wrong. We prove a corrected bound. The authors' public solver hard-codes the false bound and, outside the
  parameters used in the paper's experiments, silently returns invalid ticket assignments (e.g. weights
  (2, 14) with α = 1/20, β = 1/10).
- **A Distributed Combinatorial Topology Approach to Arrow's Impossibility Theorem** (PODC 2022, 8 citations) —
  [ArrowTopology](Papers/PODC2022/ArrowTopology). Theorem 4.2 (which domains obtained by removing two profiles
  still force a dictator) is false in 12 of the 30 cases; the corrected theorem of the full version is verified.
  Arrow's theorem itself and the paper's topological proof are verified.
- **Ranking Opinions with Few States in Population Protocols** (PODC 2026, 1 citation) —
  [RankingOpinions](Papers/PODC2026/RankingOpinions). Theorem 4.1 (tie reporting) is false: with four agents
  and a unique majority, an agent can be left outputting "tie" forever. The ranking protocol of Theorem 1.2 is
  incorrect as written: an agent holding the token of its own colour never updates its own rank. We prove fixed
  protocols correct. The core Theorem 1.1 is correct.
- **Stranger-Free Tasks** (PODC 2025, 0 citations) — [StrangerFreeTasks](Papers/PODC2025/StrangerFreeTasks). Algorithm 1 is
  not wait-free for any k ≥ 2: two processes can invalidate each other's double collects forever
  (`alg1_not_waitFree`). So the claimed wait-free upper bound with k+1 registers, and the wait-free hierarchy,
  are unproven for k ≥ 2. The algorithm is safe and obstruction-free (proved), and wait-free for k = 1.

As of October 2026 we found no erratum or later version that addresses the mistakes in Swiper, in
Barenboim–Elkin–Goldenberg (including its J. ACM version), or in Függer–Nowak–Schwarz (including its J. ACM
version).

## Layout

- `Papers/PODC<Year>/<ShortName>/` — one folder per paper (Lean library `Papers`).
- `Podc/` — small project-local helpers (Lean library `Podc`); everything general lives in CSLib.
- `lakefile.toml` — depends on CSLib (`vasnesterov/cslib`, branch `podc`), which pins Mathlib.
