# Speculatively Stabilizing Mutual Exclusion — PODC 2013

Swan Dubois, Rachid Guerraoui. *Introducing speculation in self-stabilization: an application to mutual
exclusion.* PODC 2013. DOI [10.1145/2484239.2484246](https://doi.org/10.1145/2484239.2484246). Formalized
version: arXiv [1302.2217](https://arxiv.org/abs/1302.2217) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The protocol results hold. SSME is self-stabilizing for mutual exclusion
under the unfair distributed daemon (Theorem 1), and under the synchronous daemon it stabilizes within
`⌈diam/2⌉` steps (Theorem 2). This is optimal for SSME. The general lower bound is false: **Theorem 4**
(no protocol stabilizes in fewer than `⌈diam/2⌉` synchronous steps), which carries the abstract's
optimality claim, fails under the paper's own Specification 1, where `privileged_v` may read the
neighbours of `v`. On every graph whose radius is `⌈diam/2⌉` (every tree, complete graph, star, …), some
protocol needs only `⌈diam/2⌉ - 1` steps. The bound holds when `privileged_v` reads only `v`'s own state,
as in SSME. **Lemma 4** is off by one step. The island-based proofs of Lemmas 2–3 and Case 1 of
Theorem 2 rest on ill-defined notions; we replaced them with a new proof.

## Mistakes in the paper

* **Theorem 4 is false as stated.** Specification 1 lets `privileged_v` be "a predicate over variables
  of `v` and possibly of its neighbours". The proof of Theorem 4 only makes the `t`-balls around `u` and
  `v` agree with earlier configurations. A predicate that reads the neighbours needs the `(t+1)`-balls.
  Concretely: on the complete graph `K_n` (`n ≥ 2`, `diam = 1`), take registers in `ℤ_n`. Process `v`
  is privileged iff the sum of all registers is `v`, and a privileged process increments its register.
  Exactly one process is privileged in *every* configuration, and the privilege goes round-robin. So
  mutual exclusion holds from time 0 under the synchronous daemon, and even under the unfair one, while
  the theorem claims `≥ ⌈1/2⌉ = 1` steps (`theorem_4_false`). On every star `K_{1,n-1}` (`n ≥ 3`,
  `diam = 2`), a pointer held by the centre does the same under the synchronous daemon
  (`theorem_4_false_star`). The general construction: pick a centre `z` of eccentricity `R` and a BFS
  tree rooted at `z`. Process `z` increments a clock modulo `n`, every other process sets
  `c_v := c_parent(v) + 1`, and `privileged_v ≡ (c_parent(v) = id_v)`. After `R - 1` synchronous steps
  every clock within distance `R - 1` of `z` equals `c_z`, so mutual exclusion holds from time `R - 1`
  on (`theorem_4_false_centre`). Whenever the radius is `⌈diam/2⌉` (all trees, complete graphs, stars,
  odd square grids, …), this beats the claimed bound by one (`theorem_4_false_of_radius`). So the
  abstract's claim that `⌈diam/2⌉` is optimal "even if asynchronous stabilization is not required" is
  false in the paper's own model. What is true: if `privileged_v` reads the ball of radius `r` around
  `v`, the bound is `⌈diam/2⌉ - r` (`theorem_4_radius`). For `r = 0` this is the paper's bound
  (`theorem_4`). For `r = 1` it is tight on all graphs of radius `⌈diam/2⌉`. Optimality of SSME among
  protocols whose `privileged` reads only the own state is not affected, since SSME's `privileged` reads
  only `r_v` (`conv_time_ssme`). Lemma 5 also needs protocols given by local deterministic rules. Under
  the paper's formal definition (an arbitrary set of global actions) it is false. We state it for local
  rules (`lemma_5`).
* **Lemma 4 is false (off by one).** It claims that if `γ₀ ∉ Γ₁`, every register at time `D = diam`
  lies in `init ∪ {K-D, …, K-1} ∪ {0, …, 2D-1}`. Counterexample: `C₅` (`n = 5`, `D = 2`, `K = 29`) with
  registers `(10, 10, 10, 12, 11)`. The incorrect edge `2–3` resets at step 0 and its neighbours reset at
  step 1. Process 0 is at distance exactly `D` from the incorrect edge, keeps incrementing, and holds
  `12` at time `D = 2` (`lemma_4_false`). The proof assumes that the reset wave reaches a process at
  distance `i ≤ D` from the RA-enabled set by time `i`; it only acts there one step later. The proof
  also claims that some process is RA-enabled whenever `γ₀ ∉ Γ₁`, which fails when all registers are
  negative. Correct version: from time `D + 1` on, every register is `≤ t` or `≥ K - D - 1`
  (`lemma_4_corrected`). This still gives Case 2 of Theorem 2, because the only privileged value
  `≥ K - D - 1` is that of the process with identity `n - 1`.
* **Islands (Definition 5) and Lemmas 2–3 are ill-defined; the statements we need hold.** An island is
  "a maximal set `I ⊊ V` all of whose internal edges are correct". This requires neither connectivity
  nor registers in `stab`, and it excludes `I = V`, which leaves a process uncovered when all registers
  are in `stab` but a chord is incorrect. With the intended reading (components of the correct-edge
  graph), the proof of Lemma 2 still uses "same island and `dist(u, v) ≤ D` ⇒ `d_K(r_u, r_v) ≤ D`". This
  is false, because the path realising `dist(u, v)` may leave the island. Case 1 of Theorem 2 also
  mixes up island depth (a maximum over the island) with the depth of `u`. We prove Case 1 differently,
  with a *light cone* (`cone`): if `u` is privileged at time `i ≤ D`, every process within distance
  `i-1-j` of `u` is `allCorrect` at time `j`, and the registers in the cone differ from `r_u` by at most
  the distance, as integers. The equality case `i = D` needs one extra observation that the paper does
  not make: a process that moves at step 0 is a local minimum (`no_two_priv_early`).
* **Black boxes replaced by proofs.** The paper uses the convergence of the Boulinier–Petit–Villain
  unison (PODC 2004, with conditions on `hole(g)` and `cyclo(g)`) and its synchronous bound
  `α + lcp(g) + D` (Algorithmica 2008). For `α = n` and `K > n` we prove both from scratch. Convergence
  under the unfair daemon uses chains of resets: with `α ≥ n`, a chain has fewer than `n` links. The
  synchronous bound becomes `Γ₁` from time `n + α = 2n` on (`legit_sync`).
* **Minor.** Lemma 1 also holds for `i = D` (we use this). Theorem 3 (`O(diam·n³)` steps under the unfair
  daemon) only quotes Devismes–Petit [7] and is not formalized. The claim that SSME is
  "sd-speculatively stabilizing" (Definition 4) depends on the asymptotic ratio of two convergence
  times and is not formalized.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Atomic-state model with CSLib's daemons (`Cslib/Computability/Distributed/SelfStabilization/Daemon.lean`).
  The protocol is the local rule `next : (V → ℤ) → V → ℤ` (rules NA, CA, RA with exclusive guards).
  *Unfair distributed daemon*: `IsUnfairRun` (any nonempty set of enabled processes moves; no fairness).
  *Synchronous daemon*: all enabled processes move.
* Executions are sequences `ω t = (configuration, activated set)`. `MutualExclusion` = Specification 1:
  at most one privileged process in every configuration, and every process is privileged *and* activated
  (executes its critical section) infinitely often.
* Graph: any connected simple graph with `n ≥ 2` processes. Identities: any injective
  `id : V → {0, …, n-1}`. Registers are integers restricted to the clock `cherry(n, K)` by `SValid`.
  Deterministic, no failures besides the arbitrary initial configuration.
* Self-stabilization (Definition 3) is CSLib's `IsLegitimate`/`SelfStabilizing`, with legitimate set `Γ₁`.
  `conv_time(π, sd) ≤ T` is `PseudoStabilizingWithin (syncExecs …) … T`.
* For the lower bound: any protocol given by local deterministic rules, over any product domain of
  configurations, with `privileged_v` reading the `r`-ball around `v`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| BPV unison converges under the unfair daemon (used in Thm 1) | `ResetUnison.exists_legit` | `Podc/…/ResetUnison/Unfair.lean` |
| unison liveness in `Γ₁` | `ResetUnison.live_of_legit`, `visits_of_legit` | `Podc/…/ResetUnison/Unfair.lean` |
| synchronous unison bound (used in Thm 2, Case 3) | `ResetUnison.legit_sync` | `Podc/…/ResetUnison/Sync.lean` |
| Theorem 1 | `theorem_1`, `theorem_1'` | `Theorem1.lean` |
| Lemma 1 | `lemma_1`, `lemma_1'` | `Theorem2.lean` |
| Lemmas 2–3 (replacement) | `cone`, `no_two_priv_early` | `Theorem2.lean` |
| Lemma 4 (false / corrected) | `lemma_4_false` / `lemma_4_corrected` | `Lemma4.lean` / `Theorem2.lean` |
| Theorem 2 | `theorem_2` | `Theorem2.lean` |
| Lemma 5 | `lemma_5` | `LowerBound.lean` |
| Theorem 4 (own-state `privileged`; radius `r`) | `theorem_4`, `theorem_4_radius` | `LowerBound.lean` |
| Theorem 4 false (neighbour-reading `privileged`) | `theorem_4_false` (`K_n`), `theorem_4_false_star` | `LowerBound.lean` |
| `conv_time(SSME, sd) = ⌈diam/2⌉` | `conv_time_ssme` | `LowerBound.lean` |
| `d_K`, `≤_l`, `φ` as in the paper | `correct_iff`, `locLe_iff`, `succK_eq_emod` | `Model.lean` |

**Not formalized.** Theorem 3 (it cites [7]); Definition 4 and the asymptotic "speculation" claims of
Section 3, including the examples (Dijkstra's ring, min+1 BFS, matching).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: Theorems 1 and 2 are instantiated on `C₅` (example in `Lemma4.lean`). The
counterexamples are concrete and checked by `decide` (`C₅`) or proved for whole families (`K_n`, stars).
Infrastructure: the Boulinier–Petit–Villain unison (`Podc/Computability/Distributed/SelfStabilization/ResetUnison/`,
CSLib candidate) over CSLib's `SelfStabilization/{Defs,Daemon}`.
