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
| 2019 | 1368 | Yin, Malkhi, Reiter, Golan Gueta, Abraham — *HotStuff: BFT Consensus with Linearity and Responsiveness* | [HotStuff](Papers/PODC2019/HotStuff) | ❌ **Theorem 5 (Chained HotStuff safety) false** for Algorithm 3 as written — missing height check; conflicting commits with round-robin leaders, one Byzantine replica (n=4, f=1), synchrony; fixed protocol proved safe; Basic HotStuff safety (Thm 2) true, proof gap; liveness proved; pacemaker claim unsupported |
| 2018 | 556 | Herlihy — *Atomic Cross-Chain Swaps* | [AtomicCrossChainSwaps](Papers/PODC2018/AtomicCrossChainSwaps) | ❌ §3 theory correct (atomic iff reachability symmetric); **Theorem 4.9 (safety) false** for the protocol as specified — no deadline guard on secret release, 2-party coalition on the §1 example; **Theorem 4.7 (liveness) off by one Δ**; repaired protocol proved safe, live, atomic |
| 2021 | 330 | Keidar, Kokoris-Kogias, Naor, Spiegelman — *All You Need is DAG* | [AllYouNeedIsDAG](Papers/PODC2021/AllYouNeedIsDAG) | ⚠️ DAG-Rider BAB properties proved (abstract RBC; liveness assuming good waves); Lemma 1 false for recursively committed leaders (n=4 counterexample) — total order still holds; chain quality depends on unspecified order; several proof gaps |
| 2012 | 221 | Vaidya, Tseng, Liang — *Iterative Approximate Byzantine Consensus in Arbitrary Directed Graphs* | [IterativeApproxBC](Papers/PODC2012/IterativeApproxBC) | ✅ Full characterization proved; a gap in the necessity proof repaired |
| 2021 | 137 | Abraham, Nayak, Ren, Xiang — *Good-case Latency of Byzantine Broadcast: a Complete Categorization* | [GoodCaseLatencyBB](Papers/PODC2021/GoodCaseLatencyBB) | ⚠️ All lower bounds of Table 1 proved in their intended ranges; Theorem 10 false for n = 3 and Theorems 4, 8, 9 for n = 2 (degenerate); Theorem 10's executions violate unforgeability (proof gap); Theorem 19's proof one Δ weaker than stated |
| 2011 | 125 | Kuhn, Moses, Oshman — *Coordinated Consensus in Dynamic Networks* | [CoordinatedConsensusDynamic](Papers/PODC2011/CoordinatedConsensusDynamic) | ⚠️ Simultaneous-consensus bounds, Thms 5.1, 6.1, 6.7, 6.8 proved; Thm 4.1 false as literally quantified (per-n version proved); dynamic-diameter protocol running-time claim false (6-node counterexample), final bound holds; Def 3 and Lemma 6.5 misstated |
| 2011 | 108 | Dinitz, Krauthgamer — *Fault-Tolerant Spanners: Better and Simpler* | [FaultTolerantSpanners](Papers/PODC2011/FaultTolerantSpanners) | ⚠️ Thm 2.1 (explicit probability), Cor 2.2, Thm 3.3 proved; Lemma 3.8 (distributed) misstated — LP(C) misdefined, 4-vertex counterexample, Thm 3.9 unaffected; implicit assumptions (loopless, α ≥ 4, r ≤ 2n) |
| 2013 | 100 | Vaidya, Garg — *Byzantine Vector Consensus in Complete Graphs* | [ByzantineVectorConsensus](Papers/PODC2013/ByzantineVectorConsensus) | ⚠️ Exact BVC solvable iff n ≥ max(3f+1, (d+1)f+1) and the approximate-BVC impossibility proved; Tverberg's theorem proved; Thm 6 (restricted algorithms, secondary) false as literally stated — under-specified definition; async algorithm under-specified; minor gaps |
| 2019 | 88 | Abraham, Chan, Dolev, Nayak, Pass, Ren, Shi — *Communication Complexity of Byzantine Agreement, Revisited* | [CommComplexityBA](Papers/PODC2019/CommComplexityBA) | ⚠️ Ω(f²) lower bound (Theorem 4/1) proved after repairing a probabilistic proof gap; Theorem 13 (no-setup broadcast) false for n = 2 (degenerate), proved for n ≥ C+2; upper bounds not formalized |
| 2018 | 79 | Barenboim, Elkin, Goldenberg — *Locally-Iterative Distributed (Δ+1)-Coloring below Szegedy–Vishwanathan Barrier* | [LocallyIterativeColoring](Papers/PODC2018/LocallyIterativeColoring) | ❌ Section 3 correct; **Corollaries 7.2–7.3 false** (3AG never terminates); §1.2 round claim false |
| 2019 | 71 | Brandt — *An Automatic Speedup Theorem for Distributed Problems* | [AutomaticSpeedup](Papers/PODC2019/AutomaticSpeedup) | ❌ Forward direction of Theorem 1, Theorem 2 and the sinkless-orientation/colouring lower bounds proved; **converse of Theorem 1 and Corollary 1 false** without edge symmetry breaking (input-free Δ-regular graphs whose port numbering is an edge colouring; K₂); repaired converse proved |
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
| 2010 | 14 | Suomela — *Distributed Algorithms for Edge Dominating Sets* | [EdgeDominatingSets](Papers/PODC2010/EdgeDominatingSets) | ✅ All approximation lower bounds (stronger than stated) and matching port-numbering algorithms proved; typos only |
| 2015 | 13 | Lenzen, Rybicki, Suomela — *Towards Optimal Synchronous Counting* | [SynchronousCounting](Papers/PODC2015/SynchronousCounting) | ⚠️ Theorems 1 and 3 proved; Theorem 1 false in the boundary case n = 1; Lemma 3 relies on a cited impossibility (proved here for n ≥ 3); Theorem 2's constant not established |
| 2024 | 12 | Civit, Gilbert, Guerraoui, Komatovic, Paramonov, Vidigueira — *All Byzantine Agreement Problems Are Expensive* | [AllBAExpensive](Papers/PODC2024/AllBAExpensive) | ⚠️ Proved; Lemma 10 / Theorem 4 (unauthenticated) false in the degenerate case n = 2, t = 1 |
| 2021 | 11 | Sela, Herlihy, Petrank — *Linearizability: A Typo* | [LinearizabilityTypo](Papers/PODC2021/LinearizabilityTypo) | ✅ Correct |
| 2024 | 10 | Tonkikh, Freitas — *Swiper: a new paradigm for efficient weighted distributed protocols* | [Swiper](Papers/PODC2024/Swiper) | ❌ Weight restriction/qualification proved; **Theorem 2.4 (weight separation) false** |
| 2020 | 10 | Madsen, Debois — *On the Subject of Non-Equivocation: Defining Non-Equivocation in Synchronous Agreement Systems* | [NonEquivocation](Papers/PODC2020/NonEquivocation) | ⚠️ Interactive consistency under weak non-equivocation needs exactly t+1 rounds (proved, Algorithm 2 correct); Theorem 6.1 false for n ≤ 3; Lemmas 4.7/4.8 false when ⊥ counts as a value; §7.2 model imprecise |
| 2022 | 9 | El-Hayek, Henzinger, Schmid — *Broadcasting Time in Dynamic Rooted Trees is Linear* | [DynamicRootedTrees](Papers/PODC2022/DynamicRootedTrees) | ✅ Upper and lower bounds proved; no errors |
| 2021 | 9 | Bodwin, Parter — *Restorable Shortest Path Tiebreaking for Edge-Faulty Graphs* | [RestorableTiebreaking](Papers/PODC2021/RestorableTiebreaking) | ⚠️ Theorem 2 (one scheme for every f) and the applications' correctness proved; Definition 17 omits connectivity after faults; Corollary 22's union bound miscounts fault sets (conclusion holds); proof gaps |
| 2018 | 9 | Goren, Moses — *Silence* | [Silence](Papers/PODC2018/Silence) | ⚠️ Silent Choir Theorem, message lower bounds and the AC protocols proved (all admissible runs); black-box consensus proof gap; protocols under-specified; Lemma 2 false if the receiver crashed (degenerate); D = 1 case missing from the characterization (added) |
| 2022 | 8 | Rajsbaum, Raventós-Pujol — *A Distributed Combinatorial Topology Approach to Arrow's Impossibility Theorem* | [ArrowTopology](Papers/PODC2022/ArrowTopology) | ❌ Arrow's theorem and its topological proof verified; **Theorem 4.2 false** (corrected in the full version) |
| 2021 | 7 | Altisen, Devismes, Durand, Johnen, Petit — *On Implementing Stabilizing Leader Election with Weak Assumptions on Network Dynamics* | [StabilizingLEDynamic](Papers/PODC2021/StabilizingLEDynamic) | ⚠️ All results proved (class hierarchy, impossibilities, pseudo-stabilizing LE in 6Δ+1 rounds); identifier set must have more than n elements (implicit); Lemma 7 false as stated (harmless); proof gaps in Lemmas 12, 16 |
| 2020 | 5 | Dolan — *The Only Undoable CRDTs are Counters* | [UndoableCRDTs](Papers/PODC2020/UndoableCRDTs) | ✅ Correct |
| 2020 | 5 | Khanchandani, Wattenhofer — *Byzantine Agreement with Unknown Participants and Failures* | [UnknownParticipantsBA](Papers/PODC2020/UnknownParticipantsBA) | ❌ **Lemma 4 and Theorem 1 (rotor-coordinator) false** under the pseudocode's selection rule (n=7, f=2; n=4, f=1): all correct nodes can terminate with no good round; repaired rotor and consensus (3f+7 rounds) proved; full version's fill rule under-specified |
| 2019 | 5 | Hussak, Trehan — *On Termination of a Flooding Process* | [FloodingTermination](Papers/PODC2019/FloodingTermination) | ⚠️ Termination and exact bounds proved (terminates at e iff bipartite; e < T ≤ e+d+1); Theorem 3.5 proof gap; Lemmas 3.3/3.4 need connectivity; abstract's "adversary can always prevent termination" false on forests |
| 2017 | 5 | Dolev, Erdmann, Lutz, Schapira, Zair — *Stateless Computation* | [StatelessComputation](Papers/PODC2017/StatelessComputation) | ⚠️ Theorem 3.1 true but its proof's step after Lemma 3.4 fails (repaired); Corollary 6.3 false for odd n (degenerate); Theorem 6.2's extra hypotheses unused and violated by Corollary 6.3; Theorem 5.10 proof gaps |
| 2025 | 4 | Constantinescu, Dufay, Ghinea, Wattenhofer — *Byzantine Stable Matching* | [ByzantineStableMatching](Papers/PODC2025/ByzantineStableMatching) | ⚠️ Characterizations proved for k ≥ 2; all "only if" directions false for k = 1; Lemma 13 reduction invalid |
| 2024 | 4 | Attiya, Bender, Farach-Colton, Oshman, Schiller — *History-Independent Concurrent Objects* | [HistoryIndependent](Papers/PODC2024/HistoryIndependent) | ⚠️ All results proved; impossibilities need ≥ 2 processes; Lemma 16 gap; Thm 32 for a fixed interleaving |
| 2024 | 3 | Chang, Mishra, Nguyen, Yang, Yeh — *A Tight Lower Bound for 3-Coloring Grids in the Online-LOCAL Model* | [OnlineLocalGrids](Papers/PODC2024/OnlineLocalGrids) | ⚠️ Theorems 1.1, 1.3 proved; Theorem 1.3 omits that √n must be odd |
| 2022 | 3 | Dory, Ghaffari, Ilchi — *Near-Optimal Distributed Dominating Set in Bounded Arboricity Graphs* | [DominatingSetArboricity](Papers/PODC2022/DominatingSetArboricity) | ⚠️ Theorems 1.1–1.3 proved (deterministic distributed algorithm, randomized bounds) and the Theorem 1.4 reduction; Theorem 1.3's proof arithmetic fails for small Δ (statement rescued); missing justifications and degenerate slips |
| 2024 | 2 | Ovens — *Determining Recoverable Consensus Numbers* | [RecoverableConsensus](Papers/PODC2024/RecoverableConsensus) | ⚠️ Main theorem proved; proof errors in Lemmas 15 and 16 repaired |
| 2022 | 2 | Fraigniaud, Paz, Rajsbaum — *A Speedup Theorem for Asynchronous Computation with Applications to Consensus and Approximate Agreement* | [AsyncSpeedup](Papers/PODC2022/AsyncSpeedup) | ✅ Speedup theorem, consensus fixed points and all approximate-agreement lower bounds proved for n processes (Cor. 3 shown tight); abstract overstates what Theorem 4 covers; implicit model assumptions made explicit |
| 2026 | 1 | Breitkopf, Dallot, El-Hayek, Schmid — *Ranking Opinions with Few States in Population Protocols* | [RankingOpinions](Papers/PODC2026/RankingOpinions) | ❌ Theorem 1.1 proved; **Theorem 4.1 false**; **the ranking protocol of Theorem 1.2 is incorrect** as written (fixed versions proved) |
| 2024 | 1 | Fuchs, Kuhn — *Simpler and More General Distributed Coloring Based on Simple List Defective Coloring Algorithms* | [ListDefectiveColoring](Papers/PODC2024/ListDefectiveColoring) | ⚠️ Theorems 1.1, 1.4 proved; Lemma 4.5 construction gap and Lemma A.1 proof error repaired |
| 2022 | 1 | Ovens — *The Space Complexity of Consensus from Swap* | [ConsensusFromSwap](Papers/PODC2022/ConsensusFromSwap) | ⚠️ All results proved for deterministic obstruction-free algorithms (Theorem 10 weaker than the paper's nondeterministic version); Lemma 16 and Theorem 10 proof gaps; valency definition ambiguous |
| 2026 | 0 | Attiya, Flam, Welch — *Why Canonical-Round Algorithms Fail for Optimal Byzantine Resilience* | [CanonicalRoundByzantine](Papers/PODC2026/CanonicalRoundByzantine) | ⚠️ Lower bounds proved (for 2f ≤ n ≤ 5f); Corollary 10's proof covers only part of the range (statement true); Theorem 14 implicitly uses the i = j case of gather agreement |
| 2026 | 0 | D'Archivio, AlMahmoud, Natale, Mallmann-Trenn — *Order Statistics in Population Protocols via Simple Dynamics* | [OrderStatisticsPP](Papers/PODC2026/OrderStatisticsPP) | ⚠️ Laws of the consensus value proved; both proofs of Proposition 6 invalid (statement true); Definition 4.2 under-specified |
| 2026 | 0 | Nolin — *Sinkless Orientation Made Trivial* | [SinklessOrientation](Papers/PODC2026/SinklessOrientation) | ✅ Correct (deterministic part); typos only |
| 2025 | 0 | Gafni, Losa, Raynal, Taubenfeld — *Stranger-Free Tasks* | [StrangerFreeTasks](Papers/PODC2025/StrangerFreeTasks) | ❌ Lower bound proved; **Algorithm 1 is not wait-free for k ≥ 2** |
| 2025 | 0 | Anoprenko, Kuznetsov, Aksenov — *Optimal Construction of Unique Identifiers from Bounded Registers* | [UniqueIDsBoundedRegisters](Papers/PODC2025/UniqueIDsBoundedRegisters) | ⚠️ Algorithm 1's bound (tight) and the lower bound (Theorem 4.1) proved, pinning the optimum; "poised" definition under-specified; Claim 1 proof gap; Algorithm 2's wait-freedom holds only for bounded calls |
| 2025 | 0 | Ryabinin, Gotsman, Sutra — *Brief Announcement: Revisiting Lower Bounds for Two-Step Consensus* | [TwoStepConsensusLB](Papers/PODC2025/TwoStepConsensusLB) | ⚠️ Both bounds proved as iff (task: n ≥ max{2e+f, 2f+1}; object: n ≥ max{2e+f−1, 2f+1}); the object protocol of Fig. 1 is not wait-free (1B omits initial values) — fixed protocol given; Lemma 4/5 and §B proof gaps |
| 2024 | 0 | Altisen, Cournier, Defalque, Devismes — *On Self-stabilizing Leader Election in Directed Networks* | [SSLeaderElectionDirected](Papers/PODC2024/SSLeaderElectionDirected) | ❌ Leader election (Thms 1–4) and necessity results proved; **Theorem 5 (synchronous unison) false**: the input I_E gives distance 0 to more than the leader, so U(K) is not self-stabilizing on any network with n ≥ 2 (for some ID assignment); fixed input proved, Cor. 5 holds |
| 2024 | 0 | Frei, Gelles, Ghazy, Nolin — *Content-Oblivious Leader Election on Rings* | [ContentObliviousLE](Papers/PODC2024/ContentObliviousLE) | ⚠️ Theorems 1–2 (oriented and non-oriented rings, exactly n(2·IDmax+1) pulses, quiescent termination) proved for all n ≥ 1; Theorem 3 lower bound holds as a worst case over ID assignments (per-instance reading false); Lemma 19 proof gap repaired; IDs must be positive |

## Papers with critical mistakes

Sorted by citation count. These papers contain a stated result that is **false** — not just a gap in a proof and not only in a degenerate
case. In each case the counterexample is checked by Lean; details, and the corrected statements we proved, are
in the paper's `differencies.md`.

- **HotStuff: BFT Consensus with Linearity and Responsiveness** (PODC 2019, 1368 citations) —
  [HotStuff](Papers/PODC2019/HotStuff). Theorem 5 (safety of Chained HotStuff) is false for Algorithm 3 as
  written: replicas never check that a proposed node's height equals the current view, and the lock update is
  unconditional. With round-robin leaders, n = 4, f = 1, a single Byzantine replica (leading views 2, 6, 10) and a
  synchronous network, a correct replica commits two conflicting nodes. The paper's proof relies on the missing
  check. With the height check added, safety is proved for all n > 3f. Basic HotStuff (Theorem 2) is safe;
  its proof has a gap. Checked against arXiv 1803.05069 v4–v6, whose Algorithm 3 is identical.
- **Atomic Cross-Chain Swaps** (PODC 2018, 556 citations) —
  [AtomicCrossChainSwaps](Papers/PODC2018/AtomicCrossChainSwaps). The hashed-timelock protocol of §4.5, as
  specified, violates its safety theorem (Theorem 4.9): on the paper's own three-party example, a coalition of
  two parties leaves a conforming leader Underwater, because a leader may still release its secret after its own
  hashkey has expired (the proof of Lemma 4.8 overlooks this). With the stated timeouts the protocol also
  violates its liveness theorem (Theorem 4.7): nothing is triggered even when everyone conforms. Both fixes are
  small (a deadline guard on secret release; one extra Δ in the timeouts), and the repaired protocol is proved
  safe, live and atomic. The theory of §3 is correct.
- **Locally-Iterative Distributed (Δ+1)-Coloring** (PODC 2018, 79 citations) —
  [LocallyIterativeColoring](Papers/PODC2018/LocallyIterativeColoring). Algorithm 7 (3AG) never terminates:
  on a single edge with colours ⟨1,0,0⟩, ⟨1,0,1⟩ the two vertices keep equal b-values forever, for every p.
  Hence Corollaries 7.2 and 7.3 are false. The §1.2 claim that 2p+1 rounds suffice is also false (16-vertex
  tree, Δ = 4). The main Section 3 results are correct.
- **An Automatic Speedup Theorem for Distributed Problems** (PODC 2019, 71 citations) —
  [AutomaticSpeedup](Papers/PODC2019/AutomaticSpeedup). The converse direction of Theorem 1 ("if Π_1 is
  solvable in t−1 rounds then Π is solvable in t rounds") and hence Corollary 1 are false in the paper's
  port-numbering model: the proof lets both endpoints of an edge choose from the same view, and when the edge
  looks the same from both sides they choose the same. Edge orientation on input-free Δ-regular high-girth graphs
  whose port numbering is a proper edge colouring is unsolvable, yet its Π_1 is solvable in 0 rounds (smallest
  case: K₂). This undermines the abstract's "reversible"/"exact complexity" claims; with edge symmetry breaking
  (orientations or IDs, as in all of the paper's applications) the converse holds, and the paper's lower bounds,
  which use only the forward direction, are unaffected.
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
- **Byzantine Agreement with Unknown Participants and Failures** (PODC 2020, 5 citations) —
  [UnknownParticipantsBA](Papers/PODC2020/UnknownParticipantsBA). Lemma 4 and Theorem 1 (the rotor-coordinator:
  within O(f) iterations some round is good and every correct node accepts a correct coordinator's opinion) are
  false for the algorithm's pseudocode (coordinator `C_v[r mod |C_v|]`): Byzantine nodes can insert ids into the
  sorted candidate lists so that indices shift back onto the previous coordinator, and every correct node
  terminates without a good round (n = 7, f = 2) or before accepting the good round's opinion (n = 4, f = 1).
  The proof treats the candidate list as fixed. (The prose describes a "next larger identifier" rule, under which
  these runs are not counterexamples; the proof of Lemma 4 uses the pseudocode's rule.) A repaired rotor and the
  consensus algorithm (3f+7 rounds) are proved.
- **Stranger-Free Tasks** (PODC 2025, 0 citations) — [StrangerFreeTasks](Papers/PODC2025/StrangerFreeTasks). Algorithm 1 is
  not wait-free for any k ≥ 2: two processes can invalidate each other's double collects forever
  (`alg1_not_waitFree`). So the claimed wait-free upper bound with k+1 registers, and the wait-free hierarchy,
  are unproven for k ≥ 2. The algorithm is safe and obstruction-free (proved), and wait-free for k = 1.
- **On Self-stabilizing Leader Election in Directed Networks** (PODC 2024, 0 citations) —
  [SSLeaderElectionDirected](Papers/PODC2024/SSLeaderElectionDirected). Theorem 5 (the synchronous unison
  algorithm U(K) = U-DAG ∘ PEL is self-stabilizing) is false. Its proof assumes that only the leader gets
  distance 0, but with the paper's input I_E(p) = (¬A.M, MI.M) every process whose ancestors all have
  identifiers ≥ the minimum gets distance 0 and runs its own clock. So U(K) is not self-stabilizing on any
  network with n ≥ 2 for a suitable ID assignment — already on the 2-cycle and the directed path 0 → 1.
  The definition is stated three times and matches Figure 5, so it is not a typo. With I_E(p) = (¬A.M, p.Id)
  Theorem 5 and Corollary 5 are proved. The leader-election results are correct.

As of October 2026 we found no erratum or later version that addresses the mistakes in Swiper, in
Barenboim–Elkin–Goldenberg (including its J. ACM version), or in Függer–Nowak–Schwarz (including its J. ACM
version).

## Layout

- `Papers/PODC<Year>/<ShortName>/` — one folder per paper (Lean library `Papers`).
- `Podc/` — small project-local helpers (Lean library `Podc`); everything general lives in CSLib.
- `lakefile.toml` — depends on CSLib (`vasnesterov/cslib`, branch `podc`), which pins Mathlib.
