# Scheduling on Line and Tree Networks — PODC 2012

Venkatesan T. Chakaravarthy, Sambuddha Roy, Yogish Sabharwal. *Distributed Algorithms for Scheduling on
Line and Tree Networks.* PODC 2012. DOI [10.1145/2332432.2332503](https://doi.org/10.1145/2332432.2332503).
Formalized version: arXiv [1205.1924](https://arxiv.org/abs/1205.1924) v2 (Oct 2012). This version corrects the
conference version's ratios for arbitrary heights (20 → 80 on trees, 11 → 23 on lines); numbering follows it.

**Verdict: ⚠️ Correct with fixes.** All approximation guarantees of v2 are proved. They are Lemma 3.1, Lemma 5.1 /
Claim 5.2, Theorem 5.3 (`7/(1-ε)`), Lemma 6.1, Lemma 6.2 (`73/(1-ε)`), Theorem 6.3 (`80/(1-ε)`), Theorems 7.1 /
7.2 (`4/(1-ε)`, `23/(1-ε)`) and Appendix A (`3`). So are the tree-decomposition Lemmas 4.1–4.3 and Observation A.1.
The constants are right. The fixes concern depth/length bounds that fail in edge cases, degenerate cases of the
ideal-decomposition construction, and an imprecise length grouping for line networks.

## Mistakes in the paper

* **Depth bounds of the tree decompositions are off in small cases (statements fail in edge cases).**
  - BuildIdealTD is claimed to output depth `≤ 2⌈log|C|⌉`. For `|C| = 1` the depth is 1, not 0.
  - The induction "recursive inputs have size `≤ ⌊|C|/2⌋`, hence depth `≤ 2⌈log|C|⌉`" therefore breaks at its
    base. For `|C| = 2` it only gives `3`. The bound is true for `|C| ≥ 2`, but that needs the extra base case
    `f(2) = 2`.
  - The overall bound `2⌈log n⌉` is false for `n = 1`.
  - The balancing decomposition (§4.2) is claimed to have depth `≤ ⌈log n⌉`. It does not: on a path with 4
    vertices the balancer leaves pieces of sizes 2 and 1, so the depth is `3 > 2`. The correct bound is
    `⌊log₂ n⌋ + 1`.

  None of this affects the `O(log n)` claims. We prove depth `≤ 2⌊log₂ n⌋ + 1` for the ideal decomposition
  (`lemma_4_1`), and Lemma 4.3 with length `2⌊log₂ n⌋ + 1` (`lemma_4_3`). The balancing decomposition is not
  formalized.
* **Degenerate cases of BuildIdealTD are ignored (proof gap, statement true).**
  - Cases 1 and 2 assume that the node `u′ᵢ ∈ C` adjacent to the outside neighbour `uᵢ` lies in some component
    `Cᵢ`. But `u′ᵢ` may be the balancer `z` itself.
  - In Case 2(b) the claim "there exist three distinct components `C′₁, C′₂, C′₃`" fails when the junction `j`
    equals `u′₁` or `u′₂` (or both, if `u′₁ = u′₂`). It also fails when `z` is adjacent to `j`, since then `C′₁`
    is empty.
  - The equalities `Γ(C₁) = {u₁, z}` etc. are only inclusions.

  The construction works once empty or missing components are allowed. Our proof splits into "no component of
  `C∖{z}` touches two outside neighbours" (Cases 1, 2(a) and `u′ᵢ = z`) and the junction case. We define the
  junction as the median of `u′₁, u′₂, z`. (`IdealTD.exists_good`)
* **Line-network decomposition (Section 7) is imprecise (under-specified definition).**
  - The groups `Gᵢ = {d : 2^{i-1}L_min ≤ len(d) ≤ 2^i L_min}` overlap at the boundaries, so they do not form a
    partition.
  - `ℓ = ⌈log(L_max/L_min)⌉` is `0` when all lengths are equal, so then there are no groups at all.

  We use the half-open classes `grp d = ⌊log₂(len(d)/L_min)⌋` and `ℓ = ⌊log₂(L_max/L_min)⌋ + 1`, and we prove the
  layering property, which the paper leaves as "not difficult". It holds because `len(d₁) < 2 len(d₂)` within
  the order. (`LineInput.lineLayered`, `interval_hits`)
* **Terse steps.** Lemma 4.2, Cases 1–2, says "path(d₂) must include one of the wings". This needs the
  convexity of `path(d₁) ∩ path(d₂)` in a tree (`wings_inter_nonempty`). The appeal to property (ii) in Case 2
  is unnecessary: a path leaving any vertex set passes through its neighbourhood. So Lemma 4.2 holds for every
  rooted tree with the LCA property. Lemma 6.1's pigeonhole step is fine; we replace it by the equivalent
  double count `∑_{e∈π(d′)} ∑_{d∼e} h(d) = ∑_d h(d)|π(d′) ∩ path(d)|`.
* **Typos and stale text.**
  - The introduction of Section 6 still announces the conference ratios: `(20+ε)` overall and `(13+ε)` for
    narrow instances. Lemma 6.2 and Theorem 6.3 give `73` and `80`.
  - Theorem 7.2 says "tree-networks", and its round bound has `(1/h_min) log n` instead of
    `(1/h_min) log(L_max/L_min)`.
  - §4.2: "the path between `x` and `z`" should read "`x` and `y`".
  - "inference property" should read "interference property".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The problem after the reformulation of Section 2. There is a finite set `D` of demand instances, each owned
  by a demand `dem d` and using an edge set `path d`; edges of different networks are distinct. Feasible
  solutions:
  - unit heights: independent sets (no two instances of one demand, no two overlapping instances);
  - with heights: one instance per demand and capacity `1` on every edge.

  Tree networks (`TreeInput`) and line networks with windows (`LineInput`, a finite timeline) are concrete
  instances of this. Profits are positive.
* **Synchronous distributed algorithm abstracted to its steps.** Each step of the first phase computes a
  maximal independent set of the candidate set `U` in the conflict graph. An arbitrary, adversarial MIS
  oracle `mis : ℕ → Finset D → Finset D` supplies it (step-dependent, so it covers Luby's randomized algorithm
  and network decompositions alike). We count steps (= MIS calls), not communication rounds; message passing
  and `Time(MIS)` are not modelled.
* Each stage runs a fixed number `K` of steps with `p_max < 2^K p_min` (this is the paper's distributed
  implementation). Lemma 5.1 shows that `U = ∅` after `K` steps, so this coincides with "until `U = ∅`".
  There are `ℓ` epochs and `b` stages with `ξ^b ≤ ε`. The first phase thus has `ℓ·b·K` steps, matching the
  paper's `O(log n · log(1/ε) · log(p_max/p_min))` (with `1/h_min` and `L_max/L_min` where applicable).
  `exists_stages` and `exists_steps` give explicit `b`, `K`.
* All raises of a step use the dual values from the start of the step. In the second phase all members of a
  popped set are tested against the solution built so far; for independent sets this is the paper's
  one-by-one test.
* Results are stated as `(1-ε)·p(Opt) ≤ c·p(S)`, i.e. ratio `c/(1-ε)` (`= c + ε′` for `ε = ε′/(c+ε′)`). The
  framework lemmas and the unit and narrow algorithms are even proved against the LP optimum.

**Main results in Lean.** (namespace `Podc.LineTreeScheduling`)

| Paper | Lean | File |
|---|---|---|
| weak duality (§3.1, §6.1 LPs) | `Inst.weak_duality` | `Basic.lean` |
| Lemma 3.1 | `Inst.lemma_3_1`, `Inst.lemma_3_1_opt` | `Lemma31.lean` |
| charging argument (core of 3.1/6.1) | `Inst.sum_raise_le_profitOf`, `Inst.lam_mul_lpValue_le` | `Framework.lean` |
| Def. tree decomposition, layered decomposition (§4.1, §4.4) | `TreeDecomp`, `LayeredDecomp` | `TreeDecomp.lean` |
| Lemma 4.2 | `lemma_4_2` | `TreeDecomp.lean` |
| root-fixing decomposition, `θ = 1` (§4.2) | `rootFixing`, `card_nbhd_rootFixing_le` | `TreeDecomp.lean` |
| Lemma 4.1 (ideal tree decomposition) | `lemma_4_1` (via `IdealTD.exists_good`, balancer `exists_balancer`) | `IdealTD.lean` |
| Lemma 4.3 | `lemma_4_3` | `IdealTD.lean` |
| Claim 5.2, Lemma 5.1 | `Inst.claim_5_2`, `Inst.lemma_5_1`, `Inst.stage_complete`, `Inst.alg_sat` | `Algorithm.lean` |
| Theorem 5.3 | `TreeInput.theorem_5_3`, `TreeInput.theorem_5_3_lp` (generic: `Inst.unit_alg`) | `TreeNetworks.lean`, `Approx.lean` |
| Lemma 6.1 | `Inst.lemma_6_1`, `Inst.lemma_6_1_opt` | `Lemma61.lean` |
| Lemma 6.2 | `TreeInput.lemma_6_2` (generic: `Inst.narrow_alg`) | `TreeNetworks.lean`, `Approx.lean` |
| Theorem 6.3 | `TreeInput.theorem_6_3` (generic: `Inst.arbitrary_alg`, `Inst.combine_approx`) | `TreeNetworks.lean`, `Composite.lean` |
| §7 layered decomposition (`Δ = 3`) | `LineInput.lineLayered` | `LineNetworks.lean` |
| Theorem 7.1 | `LineInput.theorem_7_1` | `LineNetworks.lean` |
| Theorem 7.2 | `LineInput.theorem_7_2` | `LineNetworks.lean` |
| Observation A.1 | `observation_A_1`, `card_rfCrit_le` | `TreeDecomp.lean` |
| Appendix A (sequential 3-approximation) | `TreeInput.appendix_A` (generic: `Inst.seq_alg`) | `Sequential.lean` |

**Not formalized.**
* The balancing decomposition (§4.2).
* The message-passing implementation and the `Time(MIS)` bounds (Luby, network decompositions).
* Removing the assumption that `p_max/p_min` (and `h_min`) are known.
* The ratio-2 remark for a single tree network (App. A).

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity:
* MIS oracles exist (`Inst.exists_isMIS`, `Inst.exists_misOracle`).
* Admissible `b` and `K` exist (`exists_stages`, `exists_steps`).
* The algorithms' runs are shown to be valid framework runs with the interference property (`alg_validRun`,
  `alg_interference`), so the hypotheses of Lemmas 3.1 and 6.1 are discharged, not assumed.

The tree geometry builds on `Papers/PODC2026/TreeAA/TreeGeom.lean` (distance-based betweenness `Btw`, a CSLib
candidate). This is a cross-paper import: `TreeGeom` and the generic tree lemmas of `TreePath.lean` and
`IdealTD.lean` should be staged in `Podc/` (or upstreamed to CSLib), so that this folder no longer depends on
another paper's folder.

**CSLib candidates** (marked `-- CSLib candidate` in the files):
* the generic tree lemmas in `TreePath.lean` (path edges, wings, gate, neighbourhood crossing, median);
* the components of a convex set minus a vertex and the centroid `exists_balancer` in `IdealTD.lean`;
* the LCA criterion `TreeDecomp.btw_lca_of_adj`;
* the abstract primal–dual packing framework (`Framework.lean`), reusable for other "two-phase"
  primal–dual packing algorithms.
