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
[`vasnesterov/cslib`](https://github.com/vasnesterov/cslib), branch `podc` (see [Layout](#layout)).

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
| 2019 | 233 | Abraham, Malkhi, Spiegelman — *Asymptotically Optimal Validated Asynchronous Byzantine Agreement* | [VABA](Papers/PODC2019/VABA) | ❌ Agreement, external validity and the expected-constant-views bound proved for all n > 3f with n−f thresholds; **with the paper's 2f+1 thresholds, agreement (Lemma 13) and Lemma 3 are false for n > 3f+1** (n=5, f=1), although the paper allows any f < n/3; termination needs a halting rule; Algorithm 6 typo stalls view 1 |
| 2012 | 221 | Vaidya, Tseng, Liang — *Iterative Approximate Byzantine Consensus in Arbitrary Directed Graphs* | [IterativeApproxBC](Papers/PODC2012/IterativeApproxBC) | ✅ Full characterization proved; a gap in the necessity proof repaired |
| 2013 | 178 | Lenzen — *Optimal Deterministic Routing and Sorting on the Congested Clique* | [CongestedCliqueRouting](Papers/PODC2013/CongestedCliqueRouting) | ⚠️ Routing in 16 rounds (Thm 3.7) and sorting in 37 rounds (Thm 4.5) proved for every n; the non-square reduction of §3 fails (n = 3 drops a message; size/load conditions fail at n = 7, 8), proved instead via virtual nodes; missing routing information, a global-count step and bundling arguments repaired at constant cost |
| 2011 | 159 | Montresor, De Pellegrini, Miorandi — *Distributed k-Core Decomposition* | [KCoreDecomposition](Papers/PODC2011/KCoreDecomposition) | ⚠️ Safety and liveness (sync, async with fairness, one-host-many-nodes) and the time bounds (Theorems 4, 5, Cor. 1) proved; the Fig. 3 'worst-case' family needs N−2 rounds, not N−1; Cor. 2 message bound ignores the initial broadcast; proof gaps in Theorems 3, 5 |
| 2021 | 137 | Abraham, Nayak, Ren, Xiang — *Good-case Latency of Byzantine Broadcast: a Complete Categorization* | [GoodCaseLatencyBB](Papers/PODC2021/GoodCaseLatencyBB) | ⚠️ All lower bounds of Table 1 proved in their intended ranges; Theorem 10 false for n = 3 and Theorems 4, 8, 9 for n = 2 (degenerate); Theorem 10's executions violate unforgeability (proof gap); Theorem 19's proof one Δ weaker than stated |
| 2011 | 125 | Kuhn, Moses, Oshman — *Coordinated Consensus in Dynamic Networks* | [CoordinatedConsensusDynamic](Papers/PODC2011/CoordinatedConsensusDynamic) | ⚠️ Simultaneous-consensus bounds, Thms 5.1, 6.1, 6.7, 6.8 proved; Thm 4.1 false as literally quantified (per-n version proved); dynamic-diameter protocol running-time claim false (6-node counterexample), final bound holds; Def 3 and Lemma 6.5 misstated |
| 2011 | 108 | Dinitz, Krauthgamer — *Fault-Tolerant Spanners: Better and Simpler* | [FaultTolerantSpanners](Papers/PODC2011/FaultTolerantSpanners) | ⚠️ Thm 2.1 (explicit probability), Cor 2.2, Thm 3.3 proved; Lemma 3.8 (distributed) misstated — LP(C) misdefined, 4-vertex counterexample, Thm 3.9 unaffected; implicit assumptions (loopless, α ≥ 4, r ≤ 2n) |
| 2013 | 100 | Vaidya, Garg — *Byzantine Vector Consensus in Complete Graphs* | [ByzantineVectorConsensus](Papers/PODC2013/ByzantineVectorConsensus) | ⚠️ Exact BVC solvable iff n ≥ max(3f+1, (d+1)f+1) and the approximate-BVC impossibility proved; Tverberg's theorem proved; Thm 6 (restricted algorithms, secondary) false as literally stated — under-specified definition; async algorithm under-specified; minor gaps |
| 2019 | 88 | Abraham, Chan, Dolev, Nayak, Pass, Ren, Shi — *Communication Complexity of Byzantine Agreement, Revisited* | [CommComplexityBA](Papers/PODC2019/CommComplexityBA) | ⚠️ Ω(f²) lower bound (Theorem 4/1) proved after repairing a probabilistic proof gap; Theorem 13 (no-setup broadcast) false for n = 2 (degenerate), proved for n ≥ C+2; upper bounds not formalized |
| 2019 | 81 | Guerraoui, Kuznetsov, Monti, Pavlovič, Seredinschi — *The Consensus Number of a Cryptocurrency* | [CryptoConsensusNumber](Papers/PODC2019/CryptoConsensusNumber) | ❌ Theorem 2 (k-shared asset transfer has consensus number k) and Corollary 1 proved; **Lemma 3 and the liveness of Theorem 3 false** for the message-passing algorithm of Fig. 4 (a correct process spending money it just received blocks forever); Fig. 1 set-vs-sequence slip; Lemma 2 proof gaps |
| 2018 | 79 | Barenboim, Elkin, Goldenberg — *Locally-Iterative Distributed (Δ+1)-Coloring below Szegedy–Vishwanathan Barrier* | [LocallyIterativeColoring](Papers/PODC2018/LocallyIterativeColoring) | ❌ Section 3 correct; **Corollaries 7.2–7.3 false** (3AG never terminates); §1.2 round claim false |
| 2016 | 76 | Filtser, Solomon — *The Greedy Spanner is Existentially Optimal* | [GreedySpanner](Papers/PODC2016/GreedySpanner) | ✅ Lemma 3, Theorem 5 (existential optimality for size and lightness), Corollary 1 (size, via the Moore bound) and Section 4 (doubling metrics, Theorem 6) proved; cited bounds taken as hypotheses for the other corollaries; minor gaps in Lemma 6 and Observation 4 |
| 2019 | 71 | Brandt — *An Automatic Speedup Theorem for Distributed Problems* | [AutomaticSpeedup](Papers/PODC2019/AutomaticSpeedup) | ❌ Forward direction of Theorem 1, Theorem 2 and the sinkless-orientation/colouring lower bounds proved; **converse of Theorem 1 and Corollary 1 false** without edge symmetry breaking (input-free Δ-regular graphs whose port numbering is an edge colouring; K₂); repaired converse proved |
| 2016 | 68 | Censor-Hillel, Haramaty, Karnin — *Optimal Dynamic Distributed MIS* | [DynamicMIS](Papers/PODC2016/DynamicMIS) | ⚠️ Main results proved; Lemma 3 "= 1/\|P\|" false for edge changes (≤ holds) |
| 2010 | 67 | Barenboim, Elkin — *Deterministic Distributed Vertex Coloring in Polylogarithmic Time* | [ArbdefectiveColoring](Papers/PODC2010/ArbdefectiveColoring) | ⚠️ Sections 3–4 proved with explicit constants (Lemma 3.1, Thms 3.2, 3.5, Cors 3.4, 3.6, Lemmas 4.1, 4.2, Thm 4.3, Cor 4.4) in the LOCAL model, Kuhn's defective colouring and the (Δ+1)-colouring of [BE09] as satisfiable hypotheses; proof of Cor 4.4 has a gap (p = ⌊a^{μ'}/log n⌋ > a^{μ'/2} fails for superlogarithmic a = log² n, Algorithm 2 then never terminates) — statement true, repaired by a three-way case split; ceil/floor typo in Thm 4.3 |
| 2020 | 55 | Gupta, Vaidya — *Fault-Tolerance in Distributed Optimization: The Case of Redundancy* | [RedundantOptimization](Papers/PODC2020/RedundantOptimization) | ⚠️ Theorem 2 (CGC filter, ρ < 1, adaptive adversary) and existence-form sufficiency proved; Theorem 1 (2f-redundancy necessary) under-specified — vacuous literally, proved in its indistinguishability form, and needs exactly f faulty agents; degenerate n = f = 1 and W* = ℝ^d cases |
| 2015 | 50 | Tseng, Vaidya — *Fault-Tolerant Consensus in Directed Graphs* | [CrashConsensusDigraph](Papers/PODC2015/CrashConsensusDigraph) | ⚠️ Synchronous and asynchronous crash-consensus characterizations proved in both directions; Theorem 5's proof invalid when outputs come after a fixed iteration (statement open); Algorithm WA under-specified — deadlocks if early messages are dropped (fixed version proved); minor gaps |
| 2021 | 49 | Kuznetsov, Tonkikh, Zhang — *Revisiting Optimal Resilience of Fast Byzantine Consensus* | [FastByzantineConsensus](Papers/PODC2021/FastByzantineConsensus) | ✅ Tight bound n ≥ 3f+2t−1 proved both ways; one proof gap repaired |
| 2019 | 45 | Bachrach, Censor-Hillel, Dory, Efron, Leitersdorf, Paz — *Hardness of Distributed Optimization* | [HardnessOptimization](Papers/PODC2019/HardnessOptimization) | ⚠️ CONGEST lower bounds of Section 2 proved (MDS, directed Hamiltonian path/cycle, Steiner tree, max-cut) via the two-party simulation, deterministic ones unconditionally; gadget proofs repaired: Lemma 2.1 uses a false intermediate claim, Claim 2.8 fails for k = 1, max-cut proof only for k ≥ 128 (statement true for k ≥ 2), Hamiltonian-path gadget arcs only in the figure |
| 2012 | 45 | Feigenbaum, Godfrey, Panda, Schapira, Shenker, Singla — *Brief Announcement: On the Resilience of Routing Tables* | [ResilientRouting](Papers/PODC2012/ResilientRouting) | ⚠️ Theorem 3.1 (1-resilient forwarding pattern; connected networks) proved with a new spanning-tree construction, §3.2.1 algorithm too under-specified to verify; Theorem 4.3 (no perfectly resilient pattern on Figure 3) proved; Lemmas 4.1 and 4.2 false as stated (4-node counterexamples), and the proof of Thm 4.3 relies on the false Lemma 4.1 (repaired with three extra scenarios); Thm 3.1 false for disconnected networks (degenerate) |
| 2016 | 42 | Bar-Yehuda, Censor-Hillel, Schwartzman — *A Distributed (2+ε)-Approximation for Vertex Cover in O(log Δ/ε log log Δ) Rounds* | [VertexCoverLocalRatio](Papers/PODC2016/VertexCoverLocalRatio) | ✅ Local-ratio template, correctness, (2+ε)-approximation and the round bound (explicit constants, per-vertex) proved in the LOCAL model; Section 4 (CONGEST) rounding mildly under-specified; Section 5 arithmetic confirmed |
| 2017 | 39 | Bar-Yehuda, Censor-Hillel, Ghaffari, Schwartzman — *Distributed Approximation of Maximum Independent Set and Maximum Matching* | [MaxISLocalRatio](Papers/PODC2017/MaxISLocalRatio) | ⚠️ Section 2 (deterministic parts): local-ratio Thm 2.1, Lemma 2.2, Δ-approximation of Algorithm 1 for any choice of U, colouring-based Algorithm 3 (3k rounds after a k-colouring), Lemma A.1 layer bound and the deterministic 2-approximate matching of Thm 2.10 proved; needs closed neighbourhoods and Δ ≥ 1; Algorithm 1 line 11 read literally (overwrite instead of accumulate) is not a Δ-approximation (pseudocode slip); randomized results (Thm 2.3 probability, Section 3) not formalized |
| 2011 | 36 | Liang, Vaidya — *Error-Free Multi-Valued Consensus with Byzantine Failures* | [ErrorFreeMultivaluedBC](Papers/PODC2011/ErrorFreeMultivaluedBC) | ⚠️ Algorithm 1 (abstract MDS / Reed–Solomon code, broadcast as a spec) achieves L-bit consensus for 3t < n (Lemmas 1–5, Thm 1 correctness) and communication eqs. (1)–(3) proved; Thm 1's t(t+1) diagnosis bound and Lemma 4 are false for the pseudo-code as printed (an isolated faulty processor can announce Detected forever, n = 4, t = 1), proved after ignoring isolated processors as the prose intends; ⊥ handling in step 2(a) under-specified |
| 2020 | 35 | Brandt, Olivetti — *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants* | [TightBipartiteMatching](Papers/PODC2020/TightBipartiteMatching) | ⚠️ Theorem 1.2 (exact complexity T_Δ(x,y); 2Δ−1 for bipartite maximal matching, deterministic port numbering on Δ-regular trees) proved — lower bound via forward round elimination, upper bound as a CSLib algorithm; false for y = Δ (degenerate); §5 output rule needs two fixes (simulation counterexamples); empty-label proof gap |
| 2018 | 35 | Függer, Nowak, Schwarz — *Tight Bounds for Asymptotic and Approximate Consensus* | [AsymptoticConsensus](Papers/PODC2018/AsymptoticConsensus) | ❌ Lower bounds proved and tight; **Theorem 4 (⇐) false** |
| 2019 | 32 | Nowak, Schmid, Winkler — *Topological Characterization of Consensus under General Message Adversaries* | [TopologicalConsensus](Papers/PODC2019/TopologicalConsensus) | ❌ Topological characterization for fault-free lock-step message adversaries (v1 Thm 5.5) and the lossy-link examples proved; **the broadcastability characterization (v1 Cor. 5.6, Thms 5.11, 6.7 'if') is false** — a 3-process adversary with every component broadcastable and univalent where consensus is impossible; Cors 6.1, 6.5, 5.15 false; several more errors only in the 2024 extension (v3) |
| 2020 | 31 | Dinitz, Robelle — *Efficient and Simple Algorithms for Fault-Tolerant Spanners* | [FaultTolerantSpanners](Papers/PODC2020/FaultTolerantSpanners) | ✅ Correct |
| 2019 | 31 | Bodwin, Patel — *A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners* | [VFTSpannersOptimal](Papers/PODC2019/VFTSpannersOptimal) | ⚠️ Theorem 1, Corollary 2 proved; Theorem 1 as stated degenerates for f > n/2; literal Algorithm 1 imprecise |
| 2016 | 31 | Jayanti, Tarjan — *A Randomized Concurrent Algorithm for Disjoint Set Union* | [ConcurrentDSU](Papers/PODC2016/ConcurrentDSU) | ⚠️ Linearizability and wait-freedom (Thm 3.4, §6 early termination) proved for every id order; work bounds (§§4–5) not formalized — the authors later retracted the proof of the PODC one-try-splitting bound (open), and Lemma 4.2's h² exponent is unjustified (fixable by constants); minor gaps in Lemmas 3.1, 3.2 |
| 2021 | 29 | Ghaffari, Haeupler — *Low-Congestion Shortcuts for Graphs Excluding Dense Minors* | [LowCongestionShortcuts](Papers/PODC2021/LowCongestionShortcuts) | ⚠️ Main theorem proved (8δ+1 blocks; 8δ fails on the one-vertex graph); several proof errors (incl. a failing Lemma 3.2 construction); Observation 2.6 false as stated |
| 2019 | 29 | Khan, Naqvi, Vaidya — *Exact Byzantine Consensus on Undirected Graphs under Local Broadcast Model* | [LocalBroadcastBC](Papers/PODC2019/LocalBroadcastBC) | ⚠️ Characterization proved (Menger's theorem formalized); Thm 4.1 fails for a single node; sufficiency proof gaps repaired |
| 2011 | 28 | Imbs, Rajsbaum, Raynal — *The Universe of Symmetry Breaking Tasks* | [SymmetryBreakingTasks](Papers/PODC2011/SymmetryBreakingTasks) | ⚠️ GSB structure theory (feasibility, kernel sets, anchoring, hardest task, canonical form), universality of perfect renaming (Thm 8), no-communication characterization (Thm 9) and the slot-to-renaming algorithm (Thm 12) proved; Thm 4 false for ℓ = 0 without max(0, ·), Lemma 1 misses ℓ_v ≤ u_v; Thm 9 holds only for non-comparison-based algorithms, contradicting §2.3's standing assumption; Table 1 misses a row |
| 2022 | 26 | Ghinea, Liu-Zhang, Wattenhofer — *Optimal Synchronous Approximate Agreement with Asynchronous Fallback* | [HybridApproxAgreement](Papers/PODC2022/HybridApproxAgreement) | ❌ Impossibility (Thm 5.1, 2tₛ+tₐ ≥ n) proved for n ≥ 2; **Theorem 4.1 false** (Π_rBC inconsistent in synchrony when n ≤ 3tₛ: late Byzantine proposals) and hence **Theorem 3.1(1) false** (Π_AA outputs 0 and 1 with ε = 1/2; n=3, tₛ=1); Def 2.2 under-specified |
| 2016 | 25 | Ellen, Gelashvili, Shavit, Zhu — *A Complexity-Based Hierarchy for Multiprocessor Synchronization* | [ComplexityHierarchy](Papers/PODC2016/ComplexityHierarchy) | ⚠️ Space lower bounds and matching upper bounds proved; Lemma 9.1 proof gap; Lemma 7.1 proof wrong (statement true); Lemma 8.2 false in an edge case that is never used |
| 2021 | 24 | Emek, Keren — *A Thin Self-Stabilizing Asynchronous Unison Algorithm* | [ThinUnison](Papers/PODC2021/ThinUnison) | ❌ Theorem 1.1 proved (gaps repaired); **Corollary 1.2 false** for arbitrary tasks |
| 2014 | 24 | Newport — *Consensus with an Abstract MAC Layer* | [AbstractMACConsensus](Papers/PODC2014/AbstractMACConsensus) | ⚠️ Lower bounds proved: FLP-style impossibility with one crash (Thm 3.2, needs n ≥ 2), no anonymous consensus (Thm 3.3), no consensus without knowledge of n (Thm 3.9), ⌊D/2⌋·F_ack time bound (Thm 3.10); two-phase consensus (Thm 4.1) proved with the 2·F_ack bound, but Algorithm 1's line 23 (decided(0) looked up in R2 only) is a slip that breaks agreement if read literally (2 nodes); Claim 3.4 false for D = 4 (Network A has diameter 6), Thm 3.3 re-proved with a new gadget; Lemma 3.1 proof gaps |
| 2016 | 24 | Haeupler, Izumi, Zuzic — *Low-Congestion Shortcuts without Embedding* | [ShortcutsNoEmbedding](Papers/PODC2016/ShortcutsNoEmbedding) | ⚠️ Lemmas 1–3, 5, Theorem 2 (supergraph/superstep level) and the deterministic Theorem 1 proved; Lemma 1 false as literally stated (shortcut edges unrelated to the part; degenerate, proved for part vertices); Lemma 3 proof gap (unreached nodes) repaired; Lemma 2 broadcast "by symmetry" re-proved by time reversal; randomized CoreFast analysis not formalized |
| 2014 | 24 | Hilke, Lenzen, Suomela — *Brief Announcement: Local Approximability of Minimum Dominating Set on Planar Graphs* | [PlanarMDSLowerBound](Papers/PODC2014/PlanarMDSLowerBound) | ✅ No deterministic T-round LOCAL algorithm (identifiers {0..n−1}, may know n) gives a (7−ε)-approximation of MDS on planar graphs, proved with explicit grid sizes depending only on T, ε; Lemma 1 (repeated Ramsey on the triangulated grid) and D* from Figure 1 proved, finite hypergraph Ramsey and straight-line planarity of the grid formalized; Lemma 1's last step needs m − 2T ≥ 3 (paper fixes m ≫ T) |
| 2021 | 23 | Fitzi, Liu-Zhang, Loss — *A New Way to Achieve Round-Efficient Byzantine Agreement* | [RoundEfficientBA](Papers/PODC2021/RoundEfficientBA) | ❌ **t < n/3 Proxcensus expansion (Lemma 3.2, Cors. 3.3, 3.8) false for n ≥ 3t+2** (threshold n−2t assumes n = 3t+1; BA errs w.p. 3/8 instead of 1/8 at n=5, t=1), repaired with threshold t+1; **Cor. 3.8 for t < n/2 fails against the paper's adaptive strongly rushing adversary** (coin visible in round 3); t < n/2 Proxcensus and extraction (Lemmas 3.4–3.6, Thm 3.7) proved |
| 2016 | 23 | Halpern, Vilaça — *Rational Consensus* | [RationalConsensus](Papers/PODC2016/RationalConsensus) | ⚠️ Theorem 1 (no fair consensus protocol is an f-Nash equilibrium, f ≥ 1) proved for n ≥ 2 (false for n = 1, degenerate); Theorem 2 (σ_cons solves fair consensus, f+1 < n) proved for Algorithm 1 as written — the round-(f+1) forwarding step is under-specified (prose "received shares only" reading fails for n = f+2 and f = 0) and the proof's "first crash-free round seems clean" is false (n=4, f=2); Theorems 3–4 not formalized |
| 2023 | 22 | Civit, Gilbert, Guerraoui, Komatovic, Vidigueira — *On the Validity of Consensus* | [ValidityConsensus](Papers/PODC2023/ValidityConsensus) | ✅ Classification proved (with a verified vector-consensus protocol); minor gap in Lemma 3 for n < 2t |
| 2019 | 22 | Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel — *Optimal Memory-Anonymous Symmetric Deadlock-Free Mutual Exclusion* | [AnonymousMutex](Papers/PODC2019/AnonymousMutex) | ❌ **Theorem 2 false** (Algorithm 1 livelocks); the read/write characterization is only half proved |
| 2012 | 22 | Hirvonen, Suomela — *Distributed Maximal Matching: Greedy is Optimal* | [MaximalMatching](Papers/PODC2012/MaximalMatching) | ✅ Theorem 2 (k−1 rounds optimal) and Corollary 3 (Ω(Δ)) proved in both models; lower bounds extended to finite graphs |
| 2014 | 21 | Ghaffari, Kantor, Lynch, Newport — *Multi-Message Broadcast with Abstract MAC Layers and Unreliable Links* | [MultiMessageBroadcastMAC](Papers/PODC2014/MultiMessageBroadcastMAC) | ⚠️ BMMB results of §3 proved with explicit constants: correctness (Thm 3.4), (D+k)·F_ack for arbitrary G′ (Thm 3.1), D·F_prog + O(r k F_ack) for r-restricted G′ (Thms 3.2, 3.16, Lemmas 3.3–3.15); the times t_{d,ℓ} of the key lemma are never defined, Lemma 3.12 part 5 is false for every reading compatible with Thm 3.16 (r=1, ℓ=2, F_prog=1, F_ack=3; the proof needs only (ℓ−1)F_ack ≤ t_{0,ℓ}), Thm 3.16 needs G connected; lower-bound proof (Lemma 3.20) covers only one MMB message per broadcast; lower bounds and §4 not formalized |
| 2021 | 20 | Burman, Chen, Chen, Doty, Nowak, Severson, Xu — *Time-Optimal Self-Stabilizing Leader Election in Population Protocols* | [TimeOptimalSSLE](Papers/PODC2021/TimeOptimalSSLE) | ⚠️ n-state lower bound, Silent-n-state-SSR, and Optimal-Silent-SSR (with the guard fixed) proved self-stabilizing; as printed (v3–v5), Protocol 3's guard '< n' means rank n is never assigned, so the protocol never stabilizes — an evident typo (Fig. 1 uses ≤); Observation 2.6 tail bound false for n = 2, 3; time bounds not formalized |
| 2016 | 20 | Mostéfaoui, Raynal — *Two-Bit Messages are Sufficient to Implement Atomic Read/Write Registers in Crash-prone Systems* | [TwoBitRegisters](Papers/PODC2016/TwoBitRegisters) | ✅ Safety and liveness proved; non-FIFO channels suffice (as the paper claims); relies on atomic code blocks (implicit convention) |
| 2011 | 19 | Biely, Robinson, Schmid — *Easy Impossibility Proofs for k-Set Agreement in Message Passing Systems* | [KSetAgreement](Papers/PODC2011/KSetAgreement) | ⚠️ Generic reduction (Thm 1, with the implicit input-independence made explicit), async impossibility (Thm 2, Cor 5) and Theorem 8 (as an iff) proved via CSLib's FLP; Theorem 1 under-specified; Theorem 8 'only if' argued only for kn = (k+1)f; degenerate f = n; failure-detector results not formalized |
| 2020 | 18 | Chen, Chen — *Self-Stabilizing Leader Election in Regular Graphs* | [SSLERegular](Papers/PODC2020/SSLERegular) | ❌ **SS-Tree (Thm 4.3) is false**: from a configuration where every node is a root with a parent colour matching no neighbour, nothing ever changes the roots (on every graph, any k ≥ 2); SS-EulerCycle (Thm 3.3) false as printed due to a one-direction coherence check (evident slip; repaired version proved, ring protocol as black box); proof gaps in Lemmas 2.1, 3.2, 4.1, 4.2 |
| 2015 | 17 | Bouzid, Mostéfaoui, Raynal — *Minimal Synchrony for Byzantine Consensus* | [MinimalSynchronyBC](Papers/PODC2015/MinimalSynchronyBC) | ❌ CB-broadcast (Thm 1), adopt-commit (Thm 2), EA-Validity (Lemma 1) and consensus safety (Thm 4) proved; **EA-Termination (Lemma 2, Thm 3) and consensus termination (Thm 4) false** — a process returning at line 4 of Fig. 3 never sets its timer, so with a silent faulty coordinator nobody decides (n=7, t=2, one initial crash, synchronous run); Lemma 3's proof ignores line-4 returns; repair unblocks the run, its correctness open |
| 2020 | 16 | Ben-Baruch, Hendler, Rusanovsky — *Upper and Lower Bounds on the Space Complexity of Detectable Objects* | [DetectableSpace](Papers/PODC2020/DetectableSpace) | ❌ Lower bounds (Thm 1: ≥ N−1 bits; Thm 2: doubly-perturbing objects need auxiliary state), Lemmas 3–8 and Algorithm 3 proved; **the detectable CAS (Algorithm 2, Lemma 2) is not linearizable** for Cas(v,v) — crash-free run of two processes' first operations; fixed version proved; Algorithm 1's initialisation under-specified |
| 2018 | 16 | Aboulker, Bonamy, Bousquet, Esperet — *Distributed Coloring in Sparse Graphs with Fewer Colors* | [SparseColoringLB](Papers/PODC2018/SparseColoringLB) | ❌ Lower bounds of §2 proved: Theorem 2.5 (H_{2ℓ}, r < ℓ, exact bound; the paper's proof gives less), Theorem 1.5 (n ≥ 6r+10, explicit Fisk triangulation) and the Ω(√n) part of Theorem 2.6, with the cited Gallai/Fisk non-colourability proved for the graphs used; **Theorem 2.6 (no 3-colouring of the k×k grid in < k/2 rounds) false for every odd k** — (k−1)/2 rounds suffice, even for a 2-colouring; repaired bound 2r+3 ≤ k |
| 2019 | 15 | Skrzypczak, Schintke, Schütt — *Linearizable State Machine Replication of State-Based CRDTs without Logs* | [CRDTReplication](Papers/PODC2019/CRDTReplication) | ❌ **Algorithm 2 not linearizable; Theorem 3 (Consistency), Lemma 3 and Theorem 4 (Update Stability) false** — G-set, 5 processes, majority quorums, incremental prepares, no losses: acceptors outside the ACK quorum vote for a proposal that misses their payload; Theorems 1, 2, 5, Lemmas 1, 2, 4 and the §III-E reduction hold; repaired VOTE handler proved linearizable |
| 2016 | 15 | Spiegelman, Cassuto, Chockler, Keidar — *Space Bounds for Reliable Storage: Fundamental Limits of Coding* | [ReliableStorageSpace](Papers/PODC2016/ReliableStorageSpace) | ❌ **Algorithm 2 (safe erasure-coded register, §3.1) unsafe as written for k ≤ f**: line 16 may decode a stale timestamp (replication n=3, f=1); with the largest qualifying timestamp Cor 3 proved; **Theorem 1 (each write adds ≥ log₂\|U_s\| bits) false as stated** (rounding/padding; cumulative form proved) and does not justify the "each stored bit belongs to one write" model; main lower bound (Thm 2, Cor 2: unbounded storage or f+1 objects holding D bits of one write) proved in that model (black-box coding) after repairing gaps in Lemmas 3–4 and the fair-run step; Lemma 2's proof wrong (lemma trivial); Theorem 3's bound misstated (not formalized) |
| 2010 | 14 | Suomela — *Distributed Algorithms for Edge Dominating Sets* | [EdgeDominatingSets](Papers/PODC2010/EdgeDominatingSets) | ✅ All approximation lower bounds (stronger than stated) and matching port-numbering algorithms proved; typos only |
| 2022 | 13 | Lenzen, Sheikholeslami — *A Recursive Early-Stopping Phase King Protocol* | [RecursivePhaseKing](Papers/PODC2022/RecursivePhaseKing) | ❌ Theorem 2.9 (early-stopping Phase King, 6(f+1) rounds) and Theorem 1.1 (cited recursive protocol as hypothesis) proved; **Lemma 4.2 (voting barrier) false** (n=4, t=1: correct nodes time out with different values), so Theorem 1.2 not established; Lemma 3.1/Cor 3.2 off by one for f=2 |
| 2019 | 13 | Brandt, Maus, Uitto — *A Sharp Threshold Phenomenon for the Distributed Complexity of the Lovász Local Lemma* | [SharpThresholdLLL](Papers/PODC2019/SharpThresholdLLL) | ⚠️ Theorems 1.1 and 1.3 (the sequential fixing process succeeds under p·2^d < 1 for variables in ≤ 2 / ≤ 3 events) proved, plus schedule correctness of Corollaries 1.2/1.4 (round counts not formalized); the w.l.o.g. rank-3 reduction fails as written (repaired); Lemma 3.5 misprinted |
| 2015 | 13 | Lenzen, Rybicki, Suomela — *Towards Optimal Synchronous Counting* | [SynchronousCounting](Papers/PODC2015/SynchronousCounting) | ⚠️ Theorems 1 and 3 proved; Theorem 1 false in the boundary case n = 1; Lemma 3 relies on a cited impossibility (proved here for n ≥ 3); Theorem 2's constant not established |
| 2017 | 13 | Blondin, Esparza, Jaax, Meyer — *Towards Efficient Verification of Population Protocols* | [PPVerification](Papers/PODC2017/PPVerification) | ⚠️ Soundness of WS³ (Props 19, 20, StrongConsensus ⇒ Consensus), Lemmas 21–22 and P_thr ∈ WS³ (Props 17, 18) proved; Prop 18's proof relies on a false monotonicity step ("a₀ ≥ a₁ ≥ ⋯") and misses saturated transitions (repaired by a lexicographic ranking); P_thr under-specified; minor gaps and typos |
| 2024 | 12 | Civit, Gilbert, Guerraoui, Komatovic, Paramonov, Vidigueira — *All Byzantine Agreement Problems Are Expensive* | [AllBAExpensive](Papers/PODC2024/AllBAExpensive) | ⚠️ Proved; Lemma 10 / Theorem 4 (unauthenticated) false in the degenerate case n = 2, t = 1 |
| 2020 | 12 | Sakavalas, Tseng, Vaidya — *Asynchronous Byzantine Approximate Consensus in Directed Networks* | [AsyncApproxBCDirected](Papers/PODC2020/AsyncApproxBCDirected) | ⚠️ Theorem 4 (solvable iff 3-reach) proved end to end (sufficiency with FIFO links); f-cover definitions inconsistent — read literally, no node ever updates (intent evident); (max − min)/2 typo; known input range missing from Thm 4; several proof gaps |
| 2013 | 12 | Dubois, Guerraoui — *Introducing speculation in self-stabilization: an application to mutual exclusion* | [SpeculativeStabilization](Papers/PODC2013/SpeculativeStabilization) | ❌ SSME proved self-stabilizing under the unfair daemon (Thm 1) and stabilizing in ⌈diam/2⌉ synchronous steps (Thm 2), optimal for SSME; **Theorem 4 (⌈diam/2⌉ lower bound for every protocol, the abstract's optimality claim) false** under the paper's own spec (privileged may read neighbours): ⌈diam/2⌉−1 achievable on every graph of radius ⌈diam/2⌉ (trees, K_n, stars), true for own-state privilege; Lemma 4 off by one (C₅); island proofs (Lemmas 2–3) replaced |
| 2019 | 12 | Ovens, Woelfel — *Strongly Linearizable Implementations of Snapshots and Other Types* | [StrongLinSnapshots](Papers/PODC2019/StrongLinSnapshots) | ⚠️ Theorem 1 (lock-free strongly linearizable ABA-detecting register, Algorithm 2) and Observation 4 proved; the stated ABA-register spec wrongly forces every first DRead to return false (Algorithm 2 not even linearizable for it; fixed spec used); Theorem 25 and lock-freedom of the snapshot proved only with atomic S and R; Theorem 3 not formalized |
| 2024 | 11 | Yu, Losa, Wang — *TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus* | [TetraBFT](Papers/PODC2024/TetraBFT) | ❌ Agreement and validity proved in every run; **termination (Theorem 1) false**: the echo guard plus no retransmission allows a permanent post-GST view-change deadlock (n=7, f=2, reliable channels; n=4, f=1 with pre-GST loss); repaired echo rule proved to terminate; Lemma 7 proof claim false; proof gaps |
| 2021 | 11 | Sela, Herlihy, Petrank — *Linearizability: A Typo* | [LinearizabilityTypo](Papers/PODC2021/LinearizabilityTypo) | ✅ Correct |
| 2018 | 11 | Yifrach, Mansour — *Fair Leader Election for Rational Agents in Asynchronous Rings and Networks* | [FairLeaderElection](Papers/PODC2018/FairLeaderElection) | ⚠️ Attacks on A-LEADuni proved (Lemmas 3.3–3.5, 4.1 with honest origin, Thm 4.2 k ≥ √n, Cubic Attack Thm 4.3 k ≥ 2∛n, Cor 4.6) and Claim D.1 for k < n/2; **Theorem 7.2 (k-simulated trees) proved only for n = 2** — Lemma F.3/Cor F.4 and the coin-toss reduction have gaps, open for n ≥ 3; Lemma 4.1's attack deadlocks with an adversarial origin; Cor 4.6 / Thm 7.2 false at the boundary ε; Claim D.1 omits k < n/2; Thm 5.1 not formalized |
| 2025 | 10 | Vacus, Ziccardi — *Minimalist Leader Election Under Weak Communication* | [MinimalistLE](Papers/PODC2025/MinimalistLE) | ⚠️ Theorems 2 (a.s. unique leader; O(D² log n) rounds w.h.p., new martingale proof) and 3 (p = 1/(D+1), O(D log n)) proved with explicit constants; Lemma 19 false for small D (K₂, P₃); proof gaps in Lemmas 14, 17 and the 'almost surely' claim |
| 2024 | 10 | Tonkikh, Freitas — *Swiper: a new paradigm for efficient weighted distributed protocols* | [Swiper](Papers/PODC2024/Swiper) | ❌ Weight restriction/qualification proved; **Theorem 2.4 (weight separation) false** |
| 2020 | 10 | Madsen, Debois — *On the Subject of Non-Equivocation: Defining Non-Equivocation in Synchronous Agreement Systems* | [NonEquivocation](Papers/PODC2020/NonEquivocation) | ⚠️ Interactive consistency under weak non-equivocation needs exactly t+1 rounds (proved, Algorithm 2 correct); Theorem 6.1 false for n ≤ 3; Lemmas 4.7/4.8 false when ⊥ counts as a value; §7.2 model imprecise |
| 2015 | 10 | Aghazadeh, Woelfel — *On the Time and Space Complexity of ABA Prevention and Detection* | [ABADetection](Papers/PODC2015/ABADetection) | ⚠️ Lower bounds for linearizable ABA-detecting registers and LL/SC proved: Thm 1(b),(c), Cor 1 as stated, Thm 1(a) (m ≥ n−1 bounded registers) only for deterministic obstruction-free implementations (paper: nondeterministic solo-termination); the §2 WeakRead/WeakWrite condition is not implied by linearizability as claimed (literally even unsatisfiable), repaired via Observation 1 from linearizability; Lemma 2 Case 1 gap repaired |
| 2022 | 9 | El-Hayek, Henzinger, Schmid — *Broadcasting Time in Dynamic Rooted Trees is Linear* | [DynamicRootedTrees](Papers/PODC2022/DynamicRootedTrees) | ✅ Upper and lower bounds proved; no errors |
| 2021 | 9 | Bodwin, Parter — *Restorable Shortest Path Tiebreaking for Edge-Faulty Graphs* | [RestorableTiebreaking](Papers/PODC2021/RestorableTiebreaking) | ⚠️ Theorem 2 (one scheme for every f) and the applications' correctness proved; Definition 17 omits connectivity after faults; Corollary 22's union bound miscounts fault sets (conclusion holds); proof gaps |
| 2018 | 9 | Goren, Moses — *Silence* | [Silence](Papers/PODC2018/Silence) | ⚠️ Silent Choir Theorem, message lower bounds and the AC protocols proved (all admissible runs); black-box consensus proof gap; protocols under-specified; Lemma 2 false if the receiver crashed (degenerate); D = 1 case missing from the characterization (added) |
| 2023 | 8 | Castañeda, Rodríguez — *Asynchronous Wait-Free Runtime Verification and Enforcement of Linearizability* | [RuntimeVerification](Papers/PODC2023/RuntimeVerification) | ⚠️ Impossibility (Thm 5.1, with six object instances) and the positive results (Thms 8.1, 8.2) proved; Lemma 7.4 false in an edge case that the proofs of Lemmas 8.1/8.2 rely on (statements true, re-proved); minor slips in Claim 7.2 and Thm 8.2 |
| 2022 | 8 | Rajsbaum, Raventós-Pujol — *A Distributed Combinatorial Topology Approach to Arrow's Impossibility Theorem* | [ArrowTopology](Papers/PODC2022/ArrowTopology) | ❌ Arrow's theorem and its topological proof verified; **Theorem 4.2 false** (corrected in the full version) |
| 2021 | 8 | Hadzilacos, Hu, Toueg — *On Register Linearizability and Termination* | [RegisterLinTermination](Papers/PODC2021/RegisterLinTermination) | ⚠️ Theorems 6, 7, 10, 12, 13, 14 and Corollaries 8, 11 proved; the proof of Theorem 14 (Lemma 67) is wrong — dropping a trailing incomplete write breaks property (P) when a pending read follows it — new construction; Lemma 19 as stated does not yield Theorem 7 (conditional version proved: at most one coin sequence defeats a strong adversary); minor gaps in Appendices C–D |
| 2015 | 8 | Delporte-Gallet, Fauconnier, Kuznetsov, Ruppert — *On the Space Complexity of Set Agreement* | [SetAgreementSpace](Papers/PODC2015/SetAgreementSpace) | ❌ Lower bound n+m−k (Thm 2) proved, with the wait-free set-agreement impossibility as a hypothesis; **the algorithms of Figures 3 and 4 are safe but not even obstruction-free** — a process adopts the value of another process's duplicated pair, writes a different pair, and re-adopts forever (n=2, k=m=1); Lemma 5 is false; with a one-line repair, Fig. 3 and Thm 7 (snapshot version) are proved; the repaired Fig. 4 (Thm 8) is only model-checked |
| 2016 | 8 | Castañeda, Gonczarowski, Moses — *Unbeatable Set Consensus via Topological and Combinatorial Reasoning* | [UnbeatableSetConsensus](Papers/PODC2016/UnbeatableSetConsensus) | ⚠️ Prop. 1, Theorems 1–2 (Optmin[k] unbeatable, last-decider unbeatable, also against arbitrary deterministic protocols) and Theorem 3 (u-Pmin[k]) proved; Lemma 1 false as stated (Lean counterexample), repaired with an extra hypothesis that holds wherever the paper uses it; small gaps in Lemma 5 and Theorem 3 proofs |
| 2026 | 7 | Fuchs, Ghinea, Parsaeian, Rybicki — *Round and Resilience-Optimal Approximate Agreement on Trees and Block Graphs* | [TreeAA](Papers/PODC2026/TreeAA) | ⚠️ Tree and block-graph AA reductions (Theorems 3, 5, 8) and the 3-round gradecast proved; the authenticated RealAA protocol of Theorem 7 relies on the false Theorem 3.1 of Ghinea et al. (PODC 2022) and fails for n=3, t=1 (the existence claim survives with a fix); Theorem 2's bound fails for 1 < D/ε ≤ 2; wrong proofs of Lemmas 13, 15 |
| 2023 | 7 | Kutten, Robinson, Tan, Zhu — *Improved Tradeoffs for Leader Election* | [LeaderTradeoffs](Papers/PODC2023/LeaderTradeoffs) | ⚠️ Upper bounds (Thms 3.10, 3.15) and the lower bounds of Thm 3.11 and corrected Thm 3.8 (log n ≤ (⌈log f⌉+1)·T, giving Ω(n^{1+1/k})) proved; Thm 3.8 as stated off by one round (false for T = 1), so the Ω((n/2)^{1+1/(k−1)}) tradeoff is unproved; Def. 3.5 vacuous if read literally; Lemma 3.14 proof gaps |
| 2021 | 7 | Altisen, Devismes, Durand, Johnen, Petit — *On Implementing Stabilizing Leader Election with Weak Assumptions on Network Dynamics* | [StabilizingLEDynamic](Papers/PODC2021/StabilizingLEDynamic) | ⚠️ All results proved (class hierarchy, impossibilities, pseudo-stabilizing LE in 6Δ+1 rounds); identifier set must have more than n elements (implicit); Lemma 7 false as stated (harmless); proof gaps in Lemmas 12, 16 |
| 2011 | 7 | Helmi, Higham, Pacheco, Woelfel — *The Space Complexity of Long-Lived and One-Shot Timestamp Implementations* | [TimestampSpace](Papers/PODC2011/TimestampSpace) | ⚠️ Long-lived (m > n/6 − 1) and one-shot (m > √(2n) − log₂ n − 4) lower bounds and both upper-bound algorithms proved (lower bounds for deterministic implementations); genuine gaps in Theorem 1.2's final count and Lemma 6.5 repaired |
| 2020 | 7 | Dufoulon, Burman, Beauquier — *Can Uncoordinated Beeps tell Stories?* | [UncoordinatedBeeps](Papers/PODC2020/UncoordinatedBeeps) | ⚠️ Section 3 proved: the two USI-code definitions are equivalent (Thm 1, l ≥ 1), USI codes decode uncoordinated transmissions (Thm 2), and Sidon-set codes of length ≤ 8h²(k+1)² exist (Thms 3, 5, 7, Lemma 6, Cor. 8); Lemma 4 is false as stated (differences mod l; D = {0,1,3}, l = 4), but only the integer version is used; Definition 4 must count d + d; degenerate side conditions; a suspected gap in Section 4 is not checked in Lean |
| 2021 | 7 | Czerner, Esparza — *Lower Bounds on the State Complexity of Population Protocols* | [PPStateComplexity](Papers/PODC2021/PPStateComplexity) | ⚠️ Leaderless bound BB(n) ≤ 2^((2n+2)!) (Thm 5.9, arXiv v3 proof) and Thm 4.5 (ℓ leaders, η < F_{ℓ,ϑ}(n)) proved, Rackoff's bound included; Definition 1's BB_L omits a bound on the number of leaders (4 states with η leaders decide x ≥ η for every η), so the leader claims need the evidently intended fixed ℓ; gaps in Thm 4.5, Lemma 5.8 and Cor. 5.7 repaired |
| 2025 | 6 | Ben-David, Dzulfikar, Ellen, Gilbert — *Byzantine Agreement with Predictions* | [BAWithPredictions](Papers/PODC2025/BAWithPredictions) | ⚠️ Theorem 13 (round lower bound, unauthenticated) and Theorem 14 (n + t² ≤ 8·#msgs + 1) proved; Lemmas 1–6, Algorithms 3–7 with Theorems 5–6 proved; gaps in Theorem 14's w.l.o.g. step and Lemma 23 repaired; wrapper checked against sub-protocol specs |
| 2024 | 5 | Attiya, Castañeda, Enea — *Strong Linearizability using Primitives with Consensus Number 2* | [StrongLinCN2](Papers/PODC2024/StrongLinCN2) | ❌ Theorems 1, 2, 5, 6, 9 (strongly linearizable max register, snapshot, readable test&set, fetch&increment) proved; **the set algorithm of Theorem 10 (Algorithm 2) is not strongly linearizable** (3 processes); §5's witness sequences for k-out-of-order queues are wrong (claim holds with repaired witnesses); Lemma 12 proof gap (stack case unproved) |
| 2020 | 5 | Dolan — *The Only Undoable CRDTs are Counters* | [UndoableCRDTs](Papers/PODC2020/UndoableCRDTs) | ✅ Correct |
| 2020 | 5 | Khanchandani, Wattenhofer — *Byzantine Agreement with Unknown Participants and Failures* | [UnknownParticipantsBA](Papers/PODC2020/UnknownParticipantsBA) | ❌ **Lemma 4 and Theorem 1 (rotor-coordinator) false** under the pseudocode's selection rule (n=7, f=2; n=4, f=1): all correct nodes can terminate with no good round; repaired rotor and consensus (3f+7 rounds) proved; full version's fill rule under-specified |
| 2020 | 5 | Godard, Imbs, Raynal, Taubenfeld — *From Bezout's Identity to Space-Optimal Election in Anonymous Memory Systems* | [BezoutElection](Papers/PODC2020/BezoutElection) | ⚠️ All results proved: impossibility (Thm 1), one-register election (Thm 2), Algorithm 2 (Thm 4) and Corollaries 1–3 as iff characterizations; termination of Algorithms 1 and 2 and the safety Lemma 2 are only sketched in the paper, with genuine gaps (repaired); §4's v′ > 0 fails for m = 1 |
| 2019 | 5 | Hussak, Trehan — *On Termination of a Flooding Process* | [FloodingTermination](Papers/PODC2019/FloodingTermination) | ⚠️ Termination and exact bounds proved (terminates at e iff bipartite; e < T ≤ e+d+1); Theorem 3.5 proof gap; Lemmas 3.3/3.4 need connectivity; abstract's "adversary can always prevent termination" false on forests |
| 2017 | 5 | Dolev, Erdmann, Lutz, Schapira, Zair — *Stateless Computation* | [StatelessComputation](Papers/PODC2017/StatelessComputation) | ⚠️ Theorem 3.1 true but its proof's step after Lemma 3.4 fails (repaired); Corollary 6.3 false for odd n (degenerate); Theorem 6.2's extra hypotheses unused and violated by Corollary 6.3; Theorem 5.10 proof gaps |
| 2019 | 5 | Ben-Basat, Even, Kawarabayashi, Schwartzman — *Optimal Distributed Covering Algorithms* | [CoveringPrimalDual](Papers/PODC2019/CoveringPrimalDual) | ❌ (f+ε)-approximation of MWHVC (Cor 4.3) and the O(log_α Δ + f·z·α) iteration bound (Thm 4.8, 4.9) proved; **covering-ILP claim (Claim 5.7, abstract) false** — the reduction multiplies the rank by the number of bits (`x ≥ 2`: cost 3 vs optimum 2, for every ε); Cor 4.10's ε = 1/(nW) does not give an f-approximation; Prop 5.5, Claim 5.6, Lemmas 4.7, 5.2 misstated |
| 2019 | 5 | Miller, Patt-Shamir, Rosenbaum — *With Great Speed Come Small Buffers: Space-Bandwidth Tradeoffs for Routing* | [SmallBuffersAQT](Papers/PODC2019/SmallBuffersAQT) | ⚠️ **Lemma 4.8 false for HPTS as printed** (Algorithm 3 runs the levels of a phase in increasing order, the proof needs decreasing; m = ℓ = 3 counterexample); Theorem 4.1 (ℓn^{1/ℓ}+σ+1 for ρℓ ≤ 1) proved for HPTS with decreasing levels, open for the printed order; PTS/PPTS on paths and trees and the lower bound (Thm 5.1) proved after repairs; the abstract's O(ℓd^{1/ℓ}+σ) bound is never proved |
| 2025 | 4 | Constantinescu, Dufay, Ghinea, Wattenhofer — *Byzantine Stable Matching* | [ByzantineStableMatching](Papers/PODC2025/ByzantineStableMatching) | ⚠️ Characterizations proved for k ≥ 2; all "only if" directions false for k = 1; Lemma 13 reduction invalid |
| 2024 | 4 | Attiya, Bender, Farach-Colton, Oshman, Schiller — *History-Independent Concurrent Objects* | [HistoryIndependent](Papers/PODC2024/HistoryIndependent) | ⚠️ All results proved; impossibilities need ≥ 2 processes; Lemma 16 gap; Thm 32 for a fixed interleaving |
| 2021 | 4 | Ovens — *The Space Complexity of Scannable Binary Objects* | [ScannableBinaryObjects](Papers/PODC2021/ScannableBinaryObjects) | ⚠️ Lemma 6, Theorem 8, Corollary 9 and the Implementation 1 upper bound proved (under weaker hypotheses); headline bound of abstract/conclusion fails for k=1, n=3; Observation 3 false in an unused case; Cor. 9(c) partly unproved in the paper |
| 2020 | 4 | Huang, Huang, Wei — *Fine-grained Analysis on Fast Implementations of Distributed Multi-writer Atomic Registers* | [FastMWMRImpossibility](Papers/PODC2020/FastMWMRImpossibility) | ❌ Theorem 1 (no W1R2 MWMR atomic register, t ≥ 1, W, R ≥ 2) proved for all algorithms, but its §4 "sieve" argument is not a proof (replaced by a blind-first-round construction); **the W2R1 algorithm (Algorithms 1–2) is not atomic** — a read after a completed write returns the initial value (S = 4, t = 1, R = 1, W = 2), so MWA2 / Lemma 5 and the claimed sufficiency of R < S/t − 2 fail |
| 2024 | 3 | Chang, Mishra, Nguyen, Yang, Yeh — *A Tight Lower Bound for 3-Coloring Grids in the Online-LOCAL Model* | [OnlineLocalGrids](Papers/PODC2024/OnlineLocalGrids) | ⚠️ Theorems 1.1, 1.3 proved; Theorem 1.3 omits that √n must be odd |
| 2023 | 3 | Bashari, Jamadi, Woelfel — *Efficient Bounded Timestamping from Standard Synchronization Primitives* | [BoundedTimestamping](Papers/PODC2023/BoundedTimestamping) | ❌ **The LL/SC algorithm (Figs. 1–2) is not linearizable**: helper steps share the process's LL/SC link, so Lemma 6 (hence Lemmas 8, 9, Cor. 10) is false — sequential 438-operation counterexample (n=3); Theorem 1 not established; wait-freedom (≤ 2κ+107 steps) and Section 6 algorithm proved |
| 2022 | 3 | Dory, Ghaffari, Ilchi — *Near-Optimal Distributed Dominating Set in Bounded Arboricity Graphs* | [DominatingSetArboricity](Papers/PODC2022/DominatingSetArboricity) | ⚠️ Theorems 1.1–1.3 proved (deterministic distributed algorithm, randomized bounds) and the Theorem 1.4 reduction; Theorem 1.3's proof arithmetic fails for small Δ (statement rescued); missing justifications and degenerate slips |
| 2022 | 3 | Delporte-Gallet, Fatourou, Fauconnier, Ruppert — *When is Recoverable Consensus Harder Than Consensus?* | [RecoverableHarder](Papers/PODC2022/RecoverableHarder) | ⚠️ All of Section 3 proved (`n`-recording suffices for RC, `(n−1)`-recording is necessary, Thm 16, Cor 17, Thm 22, the types `T_n`, `S_n`); a false step in Prop 19's proof, a gap in Prop 21's, and Cor 20's unproved `cons(T_n) ≤ n` repaired |
| 2022 | 3 | Censor-Hillel, Cohen, Gelles, Sela — *Distributed Computations in Fully-Defective Networks* | [FullyDefective](Papers/PODC2022/FullyDefective) | ✅ Content-oblivious simple-cycle simulator (Alg. 1, Thm 4 correctness, Lemma 5) proved: safety, liveness under weak fairness, no starvation; Thm 3 (two-party impossibility) and Robbins-cycle existence proved; Alg. 3 safety and deadlock freedom only — its liveness, the Section 5 construction, binary encoding and complexity bounds not formalized |
| 2012 | 3 | Chakaravarthy, Roy, Sabharwal — *Distributed Algorithms for Scheduling on Line and Tree Networks* | [LineTreeScheduling](Papers/PODC2012/LineTreeScheduling) | ⚠️ All approximation guarantees of the arXiv v2 proved for every sequence of maximal independent sets (7/(1−ε) unit-height trees, 73/80 arbitrary heights, 4/23 lines, sequential 3; Lemmas 3.1, 6.1 even vs the LP optimum); tree-decomposition depth bounds fail in small cases (balancing decomposition: depth 3 > ⌈log 4⌉ on a 4-vertex path; ideal decomposition proved with depth 2⌊log₂ n⌋+1), degenerate cases of BuildIdealTD and the §7 length groups repaired |
| 2025 | 2 | Jayanti — *On Interplanetary and Relativistic Distributed Computing* | [RelativisticComputing](Papers/PODC2025/RelativisticComputing) | ⚠️ Central Theorem 6.7 (countably many processors), Theorem 6.8 (finite executions) and Lemmas 6.2–6.6 proved over abstract spacetimes; Lemma 6.3's proof assumes order type ω (ω+1 example), repaired via Cantor; Lemmas 6.3–6.5 and Thm 6.7 fail with uncountably many processors (degenerate); several definitions under-specified |
| 2025 | 2 | Castañeda, Rodríguez — *Asynchronous Fault-Tolerant Language Decidability for Runtime Verification of Distributed Systems* | [LanguageDecidability](Papers/PODC2025/LanguageDecidability) | ❌ Theorems 4.1, 5.1 (modified language), 5.2 and most lemmas proved; **Lemma 5.3 ('WEC is weakly decidable', Table 1) false for the paper's definition of WEC**; the monitor of Figs. 5/9 flags words in SEC (fixed and proved); Figure 4 construction wrong (Lemma 4.3 true); several proofs use words violating the definitions |
| 2024 | 2 | Ovens — *Determining Recoverable Consensus Numbers* | [RecoverableConsensus](Papers/PODC2024/RecoverableConsensus) | ⚠️ Main theorem proved; proof errors in Lemmas 15 and 16 repaired |
| 2022 | 2 | Fraigniaud, Paz, Rajsbaum — *A Speedup Theorem for Asynchronous Computation with Applications to Consensus and Approximate Agreement* | [AsyncSpeedup](Papers/PODC2022/AsyncSpeedup) | ✅ Speedup theorem, consensus fixed points and all approximate-agreement lower bounds proved for n processes (Cor. 3 shown tight); abstract overstates what Theorem 4 covers; implicit model assumptions made explicit |
| 2021 | 2 | Fraigniaud, Gelles, Lotker — *The Topology of Randomized Symmetry-Breaking Distributed Computing* | [RandomizedSymmetryTopology](Papers/PODC2021/RandomizedSymmetryTopology) | ⚠️ Thm 4.1 (blackboard: LE eventually solvable iff some nⱼ = 1), Lemmas 3.2, 3.5, 4.3 and both directions of Thm 4.2 (gcd = 1) proved in the standard port model; the paper's knowledge equation Eq. (2) drops the sender's port, and with it the "if" of Thm 4.2 fails (n₁ = 2, n₂ = 3); Lemma 3.2 proof misuses the zero–one law; typo in the Lemma 4.3 construction |
| 2023 | 2 | Cosson, Massoulié, Viennot — *Brief Announcement: Efficient Collaborative Tree Exploration with Breadth-First Depth-Next* | [TreeExplorationBFDN](Papers/PODC2023/TreeExplorationBFDN) | ⚠️ Theorem 2.1 (2n/k + D²(min{log Δ, log k}+2) rounds, any tie-breaking), Theorem 3.1 (urn game) and Prop. 4.2 (break-downs) proved; Cor. 3.2 false as worded (root robots call Reanchor every round), its per-depth content proved with +2 instead of +1 (full-version Lemma 2, whose urn-game reduction is only sketched — proved directly); Algorithm 1 loop condition is a pseudo-code slip; proof-internal Claim 1 false (D+1 → 2D, k = 3 counterexample), theorem unaffected |
| 2026 | 1 | Breitkopf, Dallot, El-Hayek, Schmid — *Ranking Opinions with Few States in Population Protocols* | [RankingOpinions](Papers/PODC2026/RankingOpinions) | ❌ Theorem 1.1 proved; **Theorem 4.1 false**; **the ranking protocol of Theorem 1.2 is incorrect** as written (fixed versions proved) |
| 2026 | 1 | Lenzen, Loss, Shi, Wagner — *Byzantine Consensus in the Partially Authenticated Setting* | [PartialAuthBC](Papers/PODC2026/PartialAuthBC) | ⚠️ Gradecast, broadcast (Thms 3.13, 3.14), lower bound (Thm 4.1, Cor 4.2) and Thm 5.1 proved (cited BA protocols as black boxes); Thm 4.1 omits the unregistered-sender hypothesis stated in the surrounding text; Figure 1 ambiguous (else-if reading breaks Thm 3.13); proof gaps |
| 2026 | 1 | Chalopin, Chang, Di Luna, Zhou — *Efficient Counting and Simulation in Content-Oblivious Rings* | [ContentObliviousCounting](Papers/PODC2026/ContentObliviousCounting) | ❌ Counting (≤ 12n⌊√n⌋+14n pulses), simulation (Thms 1, 5, 14, 22) and the n log n lower bound proved; **Lemma 16 / Theorem 17 false for a relay leader** (explicitly covered by the paper; 3-node composition outputs wrong bits); §5 distance formula off by one; fixes for Thm 1 preprocessing and Algorithm 10 |
| 2026 | 1 | Lewis-Pye — *Reaching Univalency with Subquadratic Communication* | [ReachingUnivalency](Papers/PODC2026/ReachingUnivalency) | ❌ **Lemma 6 false** and the Fig. 3 protocol does not solve ε-BA (n=38, ε=1/5, f=5, k=37: correct processors disagree although all samples are accurate and committees act as ideal BA); Theorem 1 proved for a corrected protocol (sampler existence, recursion, message recurrence); Theorem 7 and Appendix B proved; Prop. 4 proof gap |
| 2026 | 1 | Filtser, Fischer — *Near-Resolution of the Tradeoff Conjecture in Distributed PLS* | [PLSTradeoff](Papers/PODC2026/PLSTradeoff) | ⚠️ Theorem 1.2 (radius O(t log n), cost O(⌈p/t⌉), explicit constants; identifiers [n]), warm-up Cor. 4.7, Theorem 1.4 (padded decompositions assumed) and the lower bound Theorem 1.6 proved; Theorem 1.6 ball bound false for t=1 and Lemma 5.6 for tiny n (degenerate); Lemma 4.5 radius slip; minor Section 5 gaps |
| 2024 | 1 | Fuchs, Kuhn — *Simpler and More General Distributed Coloring Based on Simple List Defective Coloring Algorithms* | [ListDefectiveColoring](Papers/PODC2024/ListDefectiveColoring) | ⚠️ Theorems 1.1, 1.4 proved; Lemma 4.5 construction gap and Lemma A.1 proof error repaired |
| 2022 | 1 | Ovens — *The Space Complexity of Consensus from Swap* | [ConsensusFromSwap](Papers/PODC2022/ConsensusFromSwap) | ⚠️ All results proved for deterministic obstruction-free algorithms (Theorem 10 weaker than the paper's nondeterministic version); Lemma 16 and Theorem 10 proof gaps; valency definition ambiguous |
| 2018 | 1 | Attiya, Castañeda, Hendler, Perrin — *Separating Lock-Freedom from Wait-Freedom* | [LockFreeVsWaitFree](Papers/PODC2018/LockFreeVsWaitFree) | ✅ Theorem 11 (no wait-free linearizable n-LLAA from (n−1)-window registers) proved with Lemmas 8, 10 and Claim 9, for any window-like base objects and with progress/linearizability assumed only on the relevant executions; the lock-free algorithms (Thms 4, 7) not formalized |
| 2015 | 1 | Feuilloley — *Brief Announcement: Average Complexity for the LOCAL Model* | [RingColoringAverage](Papers/PODC2015/RingColoringAverage) | ⚠️ Theorem 1 (worst-case average radius Ω(log* n) for 3-colouring a ring without knowledge of n) proved with explicit constants, n(log* n − 3) ≤ 32 Σ r(v), Linial's bound proved from scratch; gaps repaired: "w.l.o.g. minimal algorithm" lacked an existence proof (Zorn + Tychonoff), Lemma 3's 3→4-colouring reduction does not follow (argument rerun for 4-colouring); §2 largest-ID bounds (linear worst case, O(log n) average) proved |
| 2024 | 1 | Delporte-Gallet, Fauconnier, Fraigniaud, Rajsbaum, Travers — *The Computational Power of Distributed Shared-Memory Models with Bounded-Size Registers* | [BoundedRegisterPower](Papers/PODC2024/BoundedRegisterPower) | ✅ Theorem 1.1 (bounded registers not universal for n/2 < t < n) proved, with FLP for read/write (Lemma 2.1) and wait-free ε-agreement (Lemma 2.2); Algorithm 1 proved; Theorem 1.2 proved from the cited Biran–Moran–Zaks characterization (assumed); only minor gaps and typos |
| 2021 | 1 | Czerner, Guttenberg, Helfrich, Esparza — *Decision Power of Weak Asynchronous Models of Distributed Computing* | [WeakAsyncDecisionPower](Papers/PODC2021/WeakAsyncDecisionPower) | ✅ All Section 3 limitation results (Lemmas 3.1–3.5, Corollaries 3.3, 3.6: no DAf/dAF automaton decides majority) proved for all three selection constraints; Lemma 3.5's explicit cutoff is unjustified (existence holds), exclusive selection handled only via [16] in the paper |
| 2026 | 0 | Attiya, Flam, Welch — *Why Canonical-Round Algorithms Fail for Optimal Byzantine Resilience* | [CanonicalRoundByzantine](Papers/PODC2026/CanonicalRoundByzantine) | ⚠️ Lower bounds proved (for 2f ≤ n ≤ 5f); Corollary 10's proof covers only part of the range (statement true); Theorem 14 implicitly uses the i = j case of gather agreement |
| 2026 | 0 | D'Archivio, AlMahmoud, Natale, Mallmann-Trenn — *Order Statistics in Population Protocols via Simple Dynamics* | [OrderStatisticsPP](Papers/PODC2026/OrderStatisticsPP) | ⚠️ Laws of the consensus value proved; both proofs of Proposition 6 invalid (statement true); Definition 4.2 under-specified |
| 2026 | 0 | Nolin — *Sinkless Orientation Made Trivial* | [SinklessOrientation](Papers/PODC2026/SinklessOrientation) | ✅ Correct (deterministic part); typos only |
| 2026 | 0 | Cruciani, Das, Equi, Lievonen, Luong-Le, Modanese, Suomela — *Brief Announcement: Is a LOCAL Algorithm Computable?* | [LocalComputable](Papers/PODC2026/LocalComputable) | ⚠️ Section 5 proved (Theorems 5.3, 5.4, Cor. 5.6, Lemma 5.2, Table 1 equivalences, instantiated for the concrete model); the headline separation Theorem 4.1 is not verified; 'maximally safe' under-specified (proof gap), Lemma 5.2's procedure and Lemma 5.5's witness wrong (statements true) |
| 2026 | 0 | Attiya, Castañeda, Enea — *Impossibility Results for Strong Linearizability: The Difficulty of Consistent Refereeing* | [ConsistentRefereeing](Papers/PODC2026/ConsistentRefereeing) | ⚠️ Impossibility theorems (1, 5, 25, 30), the contest algorithms (Thms 3, 4, Prop. 11) and Cor. 12 proved; Theorem 30's test&set case relies on a false memory-equality claim (new proof given); Theorem 5's stack case 4c only sketched; Section 5 under-specified in places |
| 2026 | 0 | David, Moses — *Brief Announcement: What is Agreement About if not Common Knowledge?* | [AgreementDCK](Papers/PODC2026/AgreementDCK) | ⚠️ Theorems 1.2, 1.5, 1.7 and Corollary 1.6 proved (the brief announcement has no proofs; all proofs ours); Theorem 1.7's 'decide v iff θ_v' fails in runs without nonfaulty processes (degenerate); the informal converse needs decisions to be remembered |
| 2026 | 0 | Lenzen, Loss — *Early-Stabilizing Counting* | [EarlyStabilizingCounting](Papers/PODC2026/EarlyStabilizingCounting) | ⚠️ Theorem 5.7 / Cor. 5.8 (early-stabilizing counter, O(f + log n) rounds) and §6.1 proved end to end; headline Theorem 1.1 (§7) not formalized; Algorithm 1 as printed never counts (input C_v+R should be C_v+R−1, as the paper's own Algorithm 7 has); Algorithm 8 achieves Lemma 2.3 only for X−1 rounds; gaps in Lemmas 5.5, 5.6 and Cor. 5.8 |
| 2025 | 0 | Gafni, Losa, Raynal, Taubenfeld — *Stranger-Free Tasks* | [StrangerFreeTasks](Papers/PODC2025/StrangerFreeTasks) | ❌ Lower bound proved; **Algorithm 1 is not wait-free for k ≥ 2** |
| 2025 | 0 | Anoprenko, Kuznetsov, Aksenov — *Optimal Construction of Unique Identifiers from Bounded Registers* | [UniqueIDsBoundedRegisters](Papers/PODC2025/UniqueIDsBoundedRegisters) | ⚠️ Algorithm 1's bound (tight) and the lower bound (Theorem 4.1) proved, pinning the optimum; "poised" definition under-specified; Claim 1 proof gap; Algorithm 2's wait-freedom holds only for bounded calls |
| 2025 | 0 | Ryabinin, Gotsman, Sutra — *Brief Announcement: Revisiting Lower Bounds for Two-Step Consensus* | [TwoStepConsensusLB](Papers/PODC2025/TwoStepConsensusLB) | ⚠️ Both bounds proved as iff (task: n ≥ max{2e+f, 2f+1}; object: n ≥ max{2e+f−1, 2f+1}); the object protocol of Fig. 1 is not wait-free (1B omits initial values) — fixed protocol given; Lemma 4/5 and §B proof gaps |
| 2025 | 0 | Nguyen, Sutra — *An Exact Characterization of the Two-shot Deterministic Objects Solving Two-process Consensus* | [TwoShotConsensusObjects](Papers/PODC2025/TwoShotConsensusObjects) | ⚠️ Characterization (C₁ ∨ C₁.₅ ∨ C₂ ⇔ solvable) proved in both directions; the AQ example (§4.2.5) is wrong (AQ ∉ C₁.₅, but AQ ∈ C₂); Algorithm 3 line-30 typo breaks agreement if read literally; several proof gaps filled |
| 2024 | 0 | Altisen, Cournier, Defalque, Devismes — *On Self-stabilizing Leader Election in Directed Networks* | [SSLeaderElectionDirected](Papers/PODC2024/SSLeaderElectionDirected) | ❌ Leader election (Thms 1–4) and necessity results proved; **Theorem 5 (synchronous unison) false**: the input I_E gives distance 0 to more than the leader, so U(K) is not self-stabilizing on any network with n ≥ 2 (for some ID assignment); fixed input proved, Cor. 5 holds |
| 2024 | 0 | Frei, Gelles, Ghazy, Nolin — *Content-Oblivious Leader Election on Rings* | [ContentObliviousLE](Papers/PODC2024/ContentObliviousLE) | ⚠️ Theorems 1–2 (oriented and non-oriented rings, exactly n(2·IDmax+1) pulses, quiescent termination) proved for all n ≥ 1; Theorem 3 lower bound holds as a worst case over ID assignments (per-instance reading false); Lemma 19 proof gap repaired; IDs must be positive |
| 2022 | 0 | Fraigniaud, Lambein-Monette, Rabie — *Brief Announcement: Fault Tolerant Coloring of the Asynchronous Cycle* | [AsyncCycleColoring](Papers/PODC2022/AsyncCycleColoring) | ❌ 6-colour Algorithm 1 (Thm 3.1, sharper bound) and correctness/palette of the 5-colour algorithms proved; **the 5-colour algorithms are not wait-free** (Thm 3.11, Thm 4.4 false): after one crash, two simultaneously activated neighbours livelock with period 2 on every C_n; Lemmas 3.3 (as written) and 3.13 false |
| 2025 | 0 | Hu, Toueg — *You can lie but not deny: SWMR registers with signature properties in systems with Byzantine processes* | [ByzantineSWMRRegisters](Papers/PODC2025/ByzantineSWMRRegisters) | ✅ Optimality result proved: no correct test-or-set (Thm 29), verifiable, authenticated or sticky register (Thm 31) from SWMR registers for 3 ≤ n ≤ 3f, Lemma 28 (sketch) in full, Observation 30; Thm 31 proved directly (paper's derivation tacitly uses composition of Byzantine linearizable implementations); multivalued domain made explicit; n > 3f algorithms not formalized |
| 2025 | 0 | Naser-Pastoriza, Chockler, Gotsman, Ryabinin — *Tight Bounds on Channel Reliability via Generalized Quorum Systems* | [GeneralizedQuorums](Papers/PODC2025/GeneralizedQuorums) | ⚠️ Lower bounds proved for all algorithms (Lemma 2; Theorem 2 for lattice agreement, registers, snapshots, consensus; Theorem 6 under partial synchrony) by a direct gluing argument replacing the unchecked reductions; Theorem 2 false for trivial value domains (chain lattice, one-value register); Prop. 1 holds with "strongly connected" read as mutual reachability in G∖f; U_f not determined by F; Figure 3 safety proved, upper bounds not formalized |
| 2024 | 0 | Alves Ferreira, Atre, Sherry, Sobrinho — *Impossibility Results for Data-Center Routing with Congestion Control and Unsplittable Flows* | [DataCenterRouting](Papers/PODC2024/DataCenterRouting) | ⚠️ Thms 3.4, 4.2, 4.3 (lex-max-min fair rate drops by a factor 1/n), the 2× bound of Thm 5.4 and all omitted "routine"/folklore lemmas (2.2, 3.2, 4.4, 4.6, 5.2) proved; Thm 5.4 tightness proved only for odd n (the "w.l.o.g. n odd" step is unjustified; even n gives only ε > 1/(n−2)); the Doom-Switch rates in the proof are wrong for n = 3; Lemma 4.6 Step 2 made rigorous via a leximin criterion |
| 2025 | 0 | Austin, Gadouleau, Mertzios, Trehan — *Brief Announcement: Amnesiac Flooding: Easy to Break, Difficult to Escape* | [AmnesiacFloodingFaults](Papers/PODC2025/AmnesiacFloodingFaults) | ❌ Termination dichotomy proved (Thm 5.1: terminates iff balanced, within 2\|E\| rounds; Thm 5.5; Thm 2.1 derived) with a new closed-walk proof replacing the sketchy Appendix A; Thm 5.6 and Thm 5.8 non-termination proved; Thm 5.7's first claim false for two-initiator sets and Thm 5.8's broadcast part false (path 0–1–2, I = {0,2}), proved for a single initiator / in corrected form; Prop. C.2 window argument wrong; Lemma 5.2 typo; PODC bound 2\|E\|−3 fails on degenerate graphs; Section 4 uniqueness not formalized |

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
- **Asymptotically Optimal Validated Asynchronous Byzantine Agreement** (PODC 2019, 233 citations) —
  [VABA](Papers/PODC2019/VABA). The paper allows any f < n/3 (§2, Theorem 1, abstract) but uses quorum thresholds
  of exactly 2f+1, which silently assumes n = 3f+1. For n > 3f+1 two such quorums can share only a Byzantine party,
  so agreement (Lemma 13) and PB-provability (Lemma 3) fail: with n = 5, f = 1 a static adversary makes honest
  parties decide `true` and `false` whenever the coin elects it (probability 1/5). The protocol is correct for
  n = 3f+1, and with n−f thresholds agreement, validity and the expected < 3/2 views bound are proved for all
  n > 3f. Termination is only argued vacuously (the protocol never halts).
- **The Consensus Number of a Cryptocurrency** (PODC 2019, 81 citations) —
  [CryptoConsensusNumber](Papers/PODC2019/CryptoConsensusNumber). Lemma 3 (the consensusless message-passing
  asset transfer of Figure 4 is live) is false as written: incoming transfers are added only to the sender's history,
  and the validity check (line 25) ignores the transfer's dependencies, so a correct process that spends money it just
  received is blocked forever — already with two correct processes and a perfect broadcast. Hence the liveness part of
  Theorem 3 fails for the algorithm as stated; validating against `hist[q] ∪ h` fixes it (proved). The main result,
  Theorem 2 (k-shared asset transfer has consensus number exactly k), and Corollary 1 hold. (arXiv v1 checked; the 2022
  journal version was not.)
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
- **Topological Characterization of Consensus under General Message Adversaries** (PODC 2019, 32 citations) —
  [TopologicalConsensus](Papers/PODC2019/TopologicalConsensus). The topological characterization itself (consensus
  solvable iff the admissible executions split into clopen decision sets) holds, but its broadcastability form —
  consensus is solvable if every connected component is broadcastable and contains at most one valence (arXiv v1
  Cor. 5.6, "if" of Thms 5.11 and 6.7) — is false: a 3-process message adversary (not limit-closed) has only such
  components, yet consensus is impossible. Cors. 6.1 and 6.5 are false as well. The 2024 journal-style version
  (arXiv v3) repairs this by requiring finitely many components; it has further errors of its own, listed separately.
- **Optimal Synchronous Approximate Agreement with Asynchronous Fallback** (PODC 2022, 26 citations) —
  [HybridApproxAgreement](Papers/PODC2022/HybridApproxAgreement). Theorem 4.1 (the reliable broadcast Π_rBC is
  consistent in a synchronous network) is false whenever n ≤ 3tₛ, i.e. in the paper's main regime tₛ ≥ n/3: a
  Byzantine sender delivers different proposals at time 2Δ, both honest parties vote before the conflicting forwards
  arrive, and the sender completes both quorums. Hence Theorem 3.1(1) (Π_AA is secure in synchrony) is false:
  with n = 3, tₛ = 1, tₐ = 0, ε = 1/2 the honest parties output 0 and 1 (checked end to end on a line-by-line
  encoding, no forged signatures). The full version (ePrint 2022/354) has the same pseudocode; the faulty step is
  in its Lemma 6.2. The impossibility result (Theorem 5.1) is correct for n ≥ 2.
- **A Thin Self-Stabilizing Asynchronous Unison Algorithm** (PODC 2021, 24 citations) — [ThinUnison](Papers/PODC2021/ThinUnison).
  Corollary 1.2 (a synchronizer for arbitrary tasks) is false: a task solvable synchronously on complete graphs is
  solvable by no deterministic asynchronous algorithm already on K₂. It holds for static tasks (proved). The main Theorem 1.1
  is correct.
- **A New Way to Achieve Round-Efficient Byzantine Agreement** (PODC 2021, 23 citations) —
  [RoundEfficientBA](Papers/PODC2021/RoundEfficientBA). Two independent failures. (i) The t < n/3 Proxcensus
  expansion uses the threshold n − 2t, which works only when n = 3t+1, although the paper claims all t < n/3: for
  every t ≥ 1 and n ≥ 3t+2 one expansion step can give grades that differ by more than one (Lemma 3.2 false), and the
  resulting BA with κ = 3 errs with probability 3/8 instead of 2^−κ = 1/8 (n = 5, t = 1). Threshold t+1 repairs it.
  (ii) For t < n/2, Corollary 3.8 runs the coin in parallel with round 3, so the paper's own strongly rushing adaptive
  adversary sees it and corrupts accordingly: one iteration fails with probability ≥ 1/2 instead of 1/4 (n = 5,
  t = 2). Against coin-independent corruption the bound holds.
- **Optimal Memory-Anonymous Symmetric Deadlock-Free Mutual Exclusion** (PODC 2019, 22 citations) —
  [AnonymousMutex](Papers/PODC2019/AnonymousMutex). Theorem 2 claims that Algorithm 1 (read/write registers plus
  atomic snapshots) is deadlock-free whenever the number of registers m lies in M(n). It is not: for n = 4,
  m = 5 there is a fair, periodic 28-step execution in which processes keep competing and nobody ever enters the
  critical section (`theorem_2_false`). The proof ignores writes based on stale snapshots. Consequently the
  paper's tight characterization for read/write registers is unproven; only its necessity half holds (proved).
  The characterization for read-modify-write registers is correct.
- **Self-Stabilizing Leader Election in Regular Graphs** (PODC 2020, 18 citations) —
  [SSLERegular](Papers/PODC2020/SSLERegular). The SS-Tree protocol (Theorem 4.3, for graphs of bounded degree) is not
  self-stabilizing: in a configuration where every node is a root whose parent colour matches none of its neighbours'
  colours, no parent–child pair exists, every error detector is guarded off, and each root's coin never returns to 0 —
  so all nodes stay leaders forever, on every graph and for every k ≥ 2 (with probability 1 under the random scheduler).
  The SS-EulerCycle protocol (Theorem 3.3) is also false as printed, because its coherence check accepts a virtual
  edge in only one direction; that is an evident slip, and the repaired protocol is proved correct.
- **Minimal Synchrony for Byzantine Consensus** (PODC 2015, 17 citations) —
  [MinimalSynchronyBC](Papers/PODC2015/MinimalSynchronyBC). Lemma 2 (EA-Termination), Theorem 3 and the
  termination part of Theorem 4 are false. In Figure 3 a correct process that returns at line 4 never sets its
  timer (line 5), so it relays only when it receives the coordinator's message. If the coordinator is faulty and
  silent, the other correct processes wait at line 6 forever for n − t relays. With n = 7, t = 2, two proposed
  values, the round-1 coordinator crashed at the start and a synchronous network (so every correct process is a
  ⟨t+1⟩bisource), no correct process ever decides. The proof of Lemma 3 also overlooks line-4 returns. Safety of
  the consensus algorithm (Theorem 4) and Theorems 1 and 2 are proved.
- **Upper and Lower Bounds on the Space Complexity of Detectable Objects** (PODC 2020, 16 citations) —
  [DetectableSpace](Papers/PODC2020/DetectableSpace). The detectable CAS of Algorithm 2 (Lemma 2) is not even
  linearizable: in a crash-free run where two processes each start with `Cas(v₀, v₀)`, one hardware CAS flips its bit
  and the other then fails and returns false although the value never changed. The paper never excludes old = new.
  Reading such a CAS without modifying memory fixes it (proved durably linearizable and detectable). The space lower
  bounds (Theorems 1 and 2) are correct.
- **Distributed Coloring in Sparse Graphs with Fewer Colors** (PODC 2018, 16 citations) —
  [SparseColoringLB](Papers/PODC2018/SparseColoringLB). Theorem 2.6 ("no distributed algorithm can 3-colour the
  k × k grid in less than k/2 rounds") is false for every odd k = 2t+1: after t rounds a node knows how many nodes
  are at distance exactly t, and in the (2t+1) × (2t+1) grid this number determines the parity of x + y, so
  t < k/2 rounds give a proper 2-colouring (for k = 3: colour by degree). The correct bound from the paper's method
  is 2r + 3 ≤ k (proved; tight for odd k). This is an off-by-one in an exact bound: the Ω(√n) lower bound for
  planar bipartite graphs, Theorem 2.5 (whose proof as written gives a weaker bound) and Theorem 1.5 hold.
- **Linearizable State Machine Replication of State-Based CRDTs without Logs** (PODC 2019, 15 citations) —
  [CRDTReplication](Papers/PODC2019/CRDTReplication). Algorithm 2 is not linearizable, and Theorem 3
  (Consistency), Lemma 3 and Theorem 4 (Update Stability) are false. An acceptor answers `VOTED` whenever it still
  holds the proposer's round, even if its payload is not below the proposed LUB. With five processes, majority
  quorums, a G-set, only incremental prepares and no lost messages, an earlier query makes an incremental prepare
  obtain the same round number at all acceptors. Acceptors that merged a completed update `u₁` before this
  `PREPARE` then vote for `{u₂}`, so one query learns `{u₁}` by consistent quorum and another learns
  `{u₂}` by vote, although `u₁` completed before `u₂` was invoked. The proofs apply the `ACK`-quorum condition to voters
  outside that quorum. With the repaired `VOTE` handler (vote only if the payload is `⊑` the proposal), Theorems
  1–5 and linearizability are proved. Checked against arXiv 1905.08733 v1 and v2, whose relevant lines are identical.
- **Space Bounds for Reliable Storage: Fundamental Limits of Coding** (PODC 2016, 15 citations) —
  [ReliableStorageSpace](Papers/PODC2016/ReliableStorageSpace). Algorithm 2 (the safe erasure-coded register of
  §3.1) is not safe as written when k ≤ f, a range the paper explicitly includes (k = 1 is "full replication"):
  line 16 lets a reader decode any timestamp with k pieces, so with n = 3, f = 1, k = 1 a read with no concurrent
  write can return the value of an overwritten write, contradicting Lemma 9. Decoding the largest such timestamp
  fixes it, and Corollary 3 is proved. Theorem 1 ("each write adds at least log₂|U_s| bits") is false as stated
  (|U₁| = 5, |U₂| = 3 with minimal encodings), and it does not justify the "each stored bit belongs to one write"
  storage model. The main lower bound (Theorem 2, Corollary 2) is proved in that model, the paper's own, after
  repairing proof gaps; whether it holds with coding across writes is open.
- **A Recursive Early-Stopping Phase King Protocol** (PODC 2022, 13 citations) —
  [RecursivePhaseKing](Papers/PODC2022/RecursivePhaseKing). Lemma 4.2 (the voting barrier of Algorithm 7, used by
  Corollary 4.4 for the asynchronous-start result) is false: with n = 4, t = 1, a good elector set and a correct
  consensus, a correct node returns after counting a faulty vote without having voted, and the other correct nodes
  stay at two votes and time out with different values. A one-line repair (keep sending pending votes for one more
  round) is proved. Algorithm 8 has a further gap, so Theorem 1.2 is not established. Lemma 3.1 / Corollary 3.2 are
  off by one iteration (f = 2). The headline early-stopping results (Theorems 1.1, 2.9) hold.
- **Introducing speculation in self-stabilization: an application to mutual exclusion** (PODC 2013, 12 citations) —
  [SpeculativeStabilization](Papers/PODC2013/SpeculativeStabilization). Theorem 4 (every self-stabilizing mutual
  exclusion protocol needs ⌈diam/2⌉ synchronous steps), which backs the abstract's optimality claim, is false
  under the paper's own Specification 1, where `privileged_v` may read the neighbours of `v`. The proof only
  matches the t-balls around two far-apart processes, while such a predicate needs the (t+1)-balls. On every graph
  whose radius is ⌈diam/2⌉ (every tree, complete graph, star), a clock broadcast from a centre along a BFS tree
  stabilizes in ⌈diam/2⌉−1 steps; on K_n a token-passing protocol needs 0 steps even under the unfair daemon.
  The bound is proved when `privileged_v` reads only v's own state, so SSME itself (Theorems 1, 2) is correct
  and optimal in that class. Lemma 4 is also false, off by one step (counterexample on C₅).
- **TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus** (PODC 2024, 11 citations) —
  [TetraBFT](Papers/PODC2024/TetraBFT). Termination (Theorem 1) is false for the protocol as specified. A node echoes a
  view-change only if it has not sent one "for v′ or any higher view", timers are set once per view and nothing is
  retransmitted; so after GST the correct nodes can stay split between two views forever (n = 7, f = 2, reliable
  channels, any timeout including 8δ+9; and n = 4, f = 1 in the paper's model with pre-GST message loss). The authors'
  TLA+/Apalache check covered n = 4 and omits one clause of Rule 3. Agreement and validity hold in every run, and a
  repaired echo rule is proved to terminate.
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
- **On the Space Complexity of Set Agreement** (PODC 2015, 8 citations) —
  [SetAgreementSpace](Papers/PODC2015/SetAgreementSpace). The upper-bound algorithms (Figure 3, one-shot; Figure 4,
  repeated) are not m-obstruction-free, and not even obstruction-free, for any 1 ≤ m ≤ k < n. A process adopts the
  value w of a duplicated pair (w, q), then writes (w, id), which is a different pair. The duplicate survives, so
  the process re-adopts w forever without advancing. Smallest case: n = 2, k = m = 1, r = 3. p₁ runs solo and
  decides, then p₀ runs solo forever without deciding. Lemma 5 (Case 2) is false, so the proofs of Theorems 7
  and 8 and of "exactly n registers for obstruction-free repeated consensus" are invalid. Adopting only a value
  different from pref repairs Figure 3. For the repair, Theorem 7 (snapshot version) is proved. The same repair of
  Figure 4 is only model-checked. The lower bound (Theorem 2) is correct; it is proved with the Borowsky–Gafni
  impossibility as a hypothesis. arXiv v2 (the latest version) and the authors' talk slides have the same rule.
- **Optimal Distributed Covering Algorithms** (PODC 2019, 5 citations) —
  [CoveringPrimalDual](Papers/PODC2019/CoveringPrimalDual). The abstract and Claim 5.7 promise an
  (f+ε)-approximate integral solution for covering ILPs, where f bounds the number of variables per constraint.
  The paper's algorithm (binary expansion of each variable, then the zero-one-to-hypergraph reduction, then
  MWHVC) does not achieve this. The reduction multiplies the rank by the number of bits, and MWHVC only
  guarantees that larger rank + ε. On `min x s.t. x ≥ 2` (f = 1) the algorithm outputs x = 3, cost 3 against
  an optimum of 2, for every ε and α. This also refutes the introduction's claim that ε = 1/(nWM) gives an
  f-approximation for ILPs. The true guarantee is f·⌈log₂ M + 1⌉ + ε. Corollary 4.10's choice ε = 1/(nW),
  with W = max w / min w, does not give an f-approximation either (weights 9, 10: cost 19 > 18); it works for
  ε < 1/(n·max w). The main result for hypergraph vertex cover is correct: the (f+ε)-approximation
  (Corollary 4.3) and the iteration bounds (Theorems 4.8, 4.9) are proved.
- **Fine-grained Analysis on Fast Implementations of Distributed Multi-writer Atomic Registers** (PODC 2020, 4 citations) —
  [FastMWMRImpossibility](Papers/PODC2020/FastMWMRImpossibility). The fast-read (W2R1) algorithm of §5.2 / Appendix A
  (Algorithms 1–2), which the paper gives as the sufficiency half of its "necessary and sufficient condition"
  R < S/t − 2, is not atomic. With S = 4, t = 1, one reader and two writers, `write(1)` completes on three servers,
  then a concurrent larger write `(1, w₂)` overwrites one of them; a read hearing the other three servers finds the
  completed value without the reader in its `updated` sets and returns the initial value. Lemma 5 (MWA2) wrongly
  counts servers only and ignores the `updated` sets. This holds for the literal line 20 and for the single-writer
  (Dutta et al.) reading of it; a third reading is refuted only by model checking. Theorem 1 (no fast-write
  W1R2 implementation for t ≥ 1, W, R ≥ 2) is true and proved for every algorithm in the round-trip model, but
  its §4 proof ("crucial-info model", sieving) is not valid; a simpler construction closes the gap.
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
- **Strong Linearizability using Primitives with Consensus Number 2** (PODC 2024, 5 citations) —
  [StrongLinCN2](Papers/PODC2024/StrongLinCN2). The set implementation of Algorithm 2, claimed strongly linearizable
  (Theorem 10), is not: with 3 processes there is an execution prefix in which a `take` must already be linearized as
  returning EMPTY before a completed `put`, while in one extension it returns an item. No reading of the
  never-incremented `taken_new` helps. Theorem 10 is therefore unproved. The other constructions (Theorems 1, 2, 5,
  6, 9) are proved strongly linearizable.
- **Efficient Bounded Timestamping from Standard Synchronization Primitives** (PODC 2023, 3 citations) —
  [BoundedTimestamping](Papers/PODC2023/BoundedTimestamping). The main algorithm (Figures 1–2) is not linearizable.
  The helping routine `helpMoveTS` runs a few steps at a time across later operations of the same process, while
  the process's own code performs `LL()` on the same objects; with the paper's LL/SC semantics (one link per process
  and object) these renew the link behind the helper's `VL()`/`SC()`. Lemma 6 is false, and with it Lemmas 8–9 and
  Corollary 10, so Theorem 1 is not established. Lean counterexample: a sequential execution (n = 3, κ = 4,
  438 operations) after which `isEarlier(1,0)` returns the wrong answer. Wait-freedom (≤ 2κ+107 steps per
  operation) and the Section 6 algorithm are correct; giving the helper its own link context looks like a fix
  (not proved).
- **Asynchronous Fault-Tolerant Language Decidability for Runtime Verification of Distributed Systems** (PODC 2025,
  2 citations) — [LanguageDecidability](Papers/PODC2025/LanguageDecidability). Lemma 5.3 (and Table 1's "WEC ∈ WD")
  is false for the paper's definition of weak eventual counters: property (3) of Definition 2.7 is a precise
  quiescent-convergence condition, under which no monitor weakly decides WEC (diagonal argument); under it even a
  linearizable counter history with infinitely many increments is not in WEC. The monitor of Figures 5 and 9 is also
  wrong — it raises its flag on words in SEC (e.g. p₀ reads 0, increments, then reads 1). With a modified language and a
  corrected monitor the lemma and Theorem 5.1 (SD ⊊ WD) are proved.
- **Efficient Counting and Simulation in Content-Oblivious Rings** (PODC 2026, 1 citations) —
  [ContentObliviousCounting](Papers/PODC2026/ContentObliviousCounting). Lemma 16 and Theorem 17 (bit sending with a
  composable ending) are false for a relay leader, a case the paper explicitly covers (Algorithm 8 has branches only
  for it): on a 3-node ring with two back-to-back counter-clockwise rounds, an execution ends quiescent with a
  process holding the wrong bits (`relay_leader_composition_wrong`). The §5 distance formula is off by one (for
  n = 2 the non-leader computes distance 0). The counting and simulation headline results (Theorems 1, 4/13, 5, 14,
  22) and the n log n lower bound hold.
- **Reaching Univalency with Subquadratic Communication** (PODC 2026, 1 citations) —
  [ReachingUnivalency](Papers/PODC2026/ReachingUnivalency). Lemma 6 is false inside its stated range, and so is the
  claim that the committee-based protocol (Figure 3) solves ε-BA with admissible samplers: with n = 38, ε = 1/5,
  f = 5, k = 37, every sample is accurate and the committees act as ideal Byzantine agreement, yet 14 correct
  processors output 1 and 19 output 0. The step-1 threshold k(2/3 − ε/2) leaves no margin for sample deviation,
  and "bad" processors do not bound the Byzantine members of a sample. With threshold k(2/3 − ε/4) and samplers that
  are also accurate on sets containing Byzantine processors, Theorem 1 is proved.
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
- **Fault Tolerant Coloring of the Asynchronous Cycle** (PODC 2022, 0 citations) —
  [AsyncCycleColoring](Papers/PODC2022/AsyncCycleColoring). The 5-colouring algorithms are not wait-free, so the
  headline claim — wait-free 5-colouring of the cycle in O(log* n) rounds (Theorem 4.4, and Theorem 3.11 for the
  simpler algorithm) — is not established. In the paper's own model (simultaneous rounds behave as immediate
  snapshots; crashed processes stop), on C₃ one process crashes after its first round and its two neighbours, always
  activated together, alternate between two states forever; the same happens on every Cₙ. Outputs, when produced,
  are proper 5-colourings, and the 6-colour algorithm is proved wait-free.

As of October 2026 we found no erratum or later version that addresses the mistakes in Swiper, in
Barenboim–Elkin–Goldenberg (including its J. ACM version), or in Függer–Nowak–Schwarz (including its J. ACM
version).
- **Brief Announcement: Amnesiac Flooding: Easy to Break, Difficult to Escape** (PODC 2025, 0 citations) —
  [AmnesiacFloodingFaults](Papers/PODC2025/AmnesiacFloodingFaults). Theorem 5.7 claims that for every initiator set
  I ⊊ V some single uni-directional link failure breaks broadcast or termination, and Theorem 5.8 that Byzantine
  nodes J can block broadcast iff J contains a cut vertex set. Both fail on the path 0 – 1 – 2 with I = {0, 2}
  (and J = {1}): node 1 is informed in round 1 whatever happens, and a tree cannot keep messages alive
  (`theorem_5_7_multi_false`, `theorem_5_8_broadcast_false`); the PODC version's "any Byzantine set with a non-leaf
  node can force failure, for any initial set" fails the same way. Proved instead: Theorem 5.7 for one initiator,
  and that the adversary can block an honest node iff some honest node is unreachable from every initiator in
  G − J. The main termination dichotomy (Theorem 5.1) is correct and fully proved.

## Layout

- `Papers/PODC<Year>/<ShortName>/` — one folder per paper (Lean library `Papers`): the Lean files, `README.md` and
  `differencies.md`.
- `Podc/` — Lean library `Podc`, now only `Podc/Basic.lean` (`import Cslib`). The shared library that used to live here
  (~19k lines) has been upstreamed to the CSLib fork; the papers import the CSLib modules directly.
- `lakefile.toml` — depends on CSLib (`vasnesterov/cslib`, branch `podc`), which pins Mathlib.

Shared infrastructure developed for these papers, by CSLib directory:

| CSLib directory | Contents | Papers using it |
|---|---|---|
| `Cslib/Foundations/Data/Finset/`, `Foundations/Combinatorics/Labelling.lean` | quorum intersection arithmetic, vote counting (threshold, majority, plurality), sums after a point update; labellings into groups of bounded size | 21, 8, 2 |
| `Cslib/Foundations/Data/{Nat,List}/` | eventually-constant ℕ-sequences (potential arguments), time-dependent iteration, greedy list scans | 15, 9 |
| `Cslib/Foundations/Data/{Nat,Real,Fin,ZMod}/`, `Data/List/BitEncoding` | ceiling division and residue counts, `log`/`clog`/`logb`/`log*` bounds for round counts, growth until saturation, cyclic indices and ring induction, self-delimiting bit encodings | 23 |
| `Cslib/Foundations/{Analysis,Algebra}/`, `Combinatorics/{Convex,Matrix}/`, `Cslib/Computability/{Partrec,Primrec}/` | first-order condition for convex functions, averages; colorful Carathéodory and Tverberg; König line colouring of ℕ-matrices; computable list combinators | 7, 1 |
| `Cslib/Probability/{Finite,CoinGame,Chernoff,CoinField}` | finite uniform / product / Bernoulli probability by counting; common coin against an adaptive adversary; Chernoff lower tail; i.i.d. coin fields | 9 |
| `Cslib/Foundations/Combinatorics/{SimpleGraph,Digraph}/` | closed balls, dominating sets, orientations, Moore bound, greedy and fault-tolerant greedy spanners; digraph reachability avoiding faults, bounded walks, source components | 13, 8 |
| `Cslib/Computability/Distributed/Local/` | locality of LOCAL algorithms, identifiers in locally-iterative algorithms | 7 |
| `Cslib/Computability/Distributed/{SelfStabilization,PopulationProtocols}/` | stabilization and global fairness of transition systems, probability-1 ⇔ reachability, daemons and rounds; nondeterministic population protocols, uniform random scheduler | 7, 3 |
| `Cslib/Computability/Distributed/{DynamicNetworks,Knowledge,SyncCrash}/` | journeys and temporal distance, full-information indistinguishability; knowledge and common knowledge in interpreted systems; the synchronous crash model as an interpreted system | 4, 3, — |
| `Cslib/Computability/Distributed/Byzantine/` | consensus, graded consensus, gradecast and Proxcensus specifications; king phase; threshold certificates | 8, 4 |
| `Cslib/Computability/Distributed/Byzantine/PartialSync/` | partially synchronous Byzantine model: decision/input maps, run classes, quiet and omission runs, simulators, gossip, two-step lower-bound executions, `n ≤ 3t` triviality, containment condition | 9 |
| `Cslib/Computability/Distributed/Byzantine/LockStep/` | synchronous lock-step Byzantine model: threshold adversaries, committees, sequential composition | 5 |
| `Cslib/Computability/Distributed/SharedMemory/` | asynchronous shared memory: run/history API, progress conditions and potentials, covering, linearization responses, nondeterministic specs, strong linearizability, object catalog and object classes, crash-recovery, anonymous memory | 16 |
| `Cslib/Computability/Distributed/ApproxConsensus/` | reach conditions for consensus on directed networks; asynchronous model on digraphs and replay | 3 |
| `Cslib/Computability/{CommunicationComplexity,Distributed/Congest}/` | CONGEST lower bounds from two-party communication complexity | 1 |
| `Cslib/Computability/Distributed/ContentOblivious/` | content-oblivious (pulse-only) rings: model, composable procedures, staged programs, splicing, mirroring | 2 |
| `Cslib/Computability/Distributed/IteratedModel/` | iterated immediate-snapshot style models, tasks and solvability | 1 |
