# Distributed Spanner Approximation — PODC 2018

Keren Censor-Hillel, Michal Dory. *Distributed Spanner Approximation.* PODC 2018. DOI
[10.1145/3212734.3212758](https://doi.org/10.1145/3212734.3212758). Formalized version: arXiv
[1802.03160](https://arxiv.org/abs/1802.03160) v1; numbering follows it.

**Verdict: 🛠️ Proof repaired.** The main hardness results hold: the
`Ω(n/(√α·log n))` deterministic and (given the randomized communication complexity of set
disjointness) `Ω(√n/(√α·log n))` randomized CONGEST lower bounds for `α`-approximate minimum
directed `k`-spanner, `k ≥ 5` (Thms 2.8, 1.1). Their supporting lemmas also hold, including the
cited gap-disjointness bound (Lemma 2.5), which we prove. The vertex-cover reduction (Claim 3.1)
is correct. Lemma 3.2 has a gap: after the simulation, a node cannot compute its cover membership
"without any communication". One extra round fixes it, which is harmless for the asymptotic uses.

## Mistakes in the paper

* **Lemma 3.2: the conversion from spanner to vertex cover needs communication.** The paper says
  that after simulating the 2-spanner algorithm on `G_S`, every node converts the spanner `H` into
  `C_H` "without any communication". By §1.5, a node outputs *some* of its incident edges and the
  spanner is the union of the outputs. So node `v` does not know whether `u₂` output the cross edge
  `{v₁, u₂}`, and that edge decides whether `v ∈ C_H`. The natural local rule (apply `C_H` only to
  the edges that `v`'s own copies output) fails. Take the triangle and the optimal 2-spanner of
  `G_S` made of all weight-0 edges plus the cross edge `{0₁, 2₂}`. Either `0₁` or `2₂` may be the
  node that outputs that cross edge. The rule then gives `{0}` or `{2}`, and neither is a vertex
  cover (`localRule_counterexample`). One extra round, in which each node tells each neighbour
  whether it output their shared cross edge, repairs the proof. We prove Lemma 3.2 with `T + 1`
  rounds of `3B`-bit messages, or `3(T + 1)` rounds of `B`-bit messages, instead of `3T`
  (`lemma_3_2`, `lemma_3_2_congest`). This is a proof gap; the `+O(1)` does not affect
  Thms 3.3/3.4.
* **Minor slips.**
  - Proof of Lemma 2.4: "`V_B = Y1, V_A = V \ V_A`" should read `V_A = V \ V_B`.
  - Claim 3.1 / Lemma 3.2: the conversion `H → H'` gives `w(H') ≤ w(H)`. It has "the same cost"
    only because `H` is a minimum spanner in Claim 3.1. Lemma 3.2 applies the conversion to an
    `α`-approximate `H`, so there only `|C_H| ≤ w(H)` holds, and that is all the proof needs.
  - Proof of Thm 2.8: the constants `c₁`, `c₂` are handled loosely (`β` is defined from `α(n')`,
    the bound is used with `α(n)`). The argument is routine; our version has explicit constants
    and no monotonicity assumption.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous CONGEST from CSLib (`Cslib.Congest.Algorithm`): deterministic nodes, IDs = vertex
  names, `B`-bit messages per edge, direction and round, no failures. Randomized algorithms
  (Thm 1.1) get private uniform random strings `r v : ρ`; they may fail with probability `≤ δ` on
  each instance.
* Directed `k`-spanner: a digraph is a loopless arc set `E : Finset (V × V)`; the network is its
  underlying undirected graph (communication is bidirectional) and must be connected; node `v`
  knows the directions of its incident arcs. Each node selects some incident arcs; the output is
  the union. `H` is a `k`-spanner if `H ⊆ E` and every arc of `E` is joined by a directed walk of
  length `≤ k` in `H`; `α`-approximate means `|H| ≤ α·|H'|` for every `k`-spanner `H'`.
* Algorithms run on a fixed vertex set `V`, `n = |V|`, and must be correct on every such digraph
  on `V`. The lower-bound graph `G(ℓ, β)` is padded with pendant vertices to exactly `n` vertices
  (the paper uses monotonicity of `α(n)` instead). Bounds are stated concretely in `n, α, B, T`;
  `B = O(log n)` gives the paper's `Ω`-bounds.
* Two-party communication: CSLib protocol trees. Lemma 2.5 (gap disjointness, deterministic) is
  proved; the randomized lower bound for set disjointness (Lemma 2.1) is the hypothesis
  `RandDisjLB δ κ`.
* §3: undirected graphs `G` on `V` with a linear order (IDs). `G_S` lives on `V × Fin 3`, with
  weights in `ℕ`; the cross edge for `v < u` is `{v₁, u₂}`. A 2-spanner is `H ≤ G_S` covering every
  edge by a path of length `≤ 2`, and its cost is the sum of the weights of its edges. The spanner
  algorithm's node input is its incident edges with weights; the MVC algorithm's node input is its
  neighbourhood; the MVC output is the `out` bit. Algorithms may be required to be correct only on
  a class `P` of graphs.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Construction `G(ℓ, β)` | `Vtx`, `arc`, `arcs`, `dArcs` | `Graph.lean` |
| Claim 2.2 | `claim_2_2_path`, `claim_2_2_unique` | `Graph.lean` |
| Lemma 2.3 | `lemma_2_3` (general: `nonD_isDiSpanner`, `card_nonD_le`, `card_inter_D_ge`) | `Graph.lean` |
| Lemma 2.6 | `lemma_2_6` | `Graph.lean` |
| Lemma 2.5 (gap disjointness, cited) | `Cslib.CommunicationComplexity.Protocol.gapDisj_lowerBound` (`N ≤ 3c`) | `Podc/Computability/CommunicationComplexity/GapDisjointness.lean` |
| Lemma 2.7 | `lemma_2_7` | `LowerBound.lean` |
| Lemma 2.4 (randomized) | `lemma_2_4` (assumes `RandDisjLB`) | `LowerBound.lean` |
| Theorem 2.8 | `theorem_2_8`, `theorem_2_8'` | `Theorems.lean` |
| Theorem 1.1 (randomized) | `theorem_1_1` (assumes `RandDisjLB`) | `Theorems.lean` |
| Claim 3.1 | `claim_3_1` (min 2-spanner cost = vertex cover number); `isTwoSpanner_HC`, `cost_HC`, `isVertexCover_CH`, `ncard_CH_le_cost`; `approx_transfer` | `VertexCover.lean` |
| Lemma 3.2 | `lemma_3_2` (`3B`-bit messages, `T + 1` rounds), `lemma_3_2_congest` (`B`-bit, `3(T + 1)` rounds) | `VCReduction.lean` |
| Lemma 3.2's "no communication" step fails | `localRule_counterexample` | `VCReduction.lean` |

Statements: `theorem_2_8`: if `156α < β²`, `β(2β+5) ≤ n`, and a deterministic algorithm with
`B`-bit messages outputs an `α`-approximate minimum directed `k`-spanner (`k ≥ 5`) of every
connected loopless `n`-vertex digraph within `T` rounds, then `⌊n/(2β+5)⌋ ≤ 18·B·T + 1`
(`T = Ω(n/(√α·B))`). `theorem_1_1`: with `q = ⌈34α⌉ + 1`, `8q ≤ n`, a randomized algorithm failing
with probability `≤ δ` satisfies `κ·⌊√⌊n/8q⌋⌋ ≤ 6·B·T + 1` (`T = Ω(√(n/α)/B)`).

**Not formalized.** The weighted `k`-spanner bounds (Thms 2.9, 2.10), the LOCAL lower bounds for
weighted 2-spanner derived from Kuhn–Moscibroda–Wattenhofer (Thms 3.3, 3.4), and all algorithms of
§§4–6 (randomized upper bounds).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: full-information gathering plus a locally computed minimum spanner is an
exact algorithm in `n` rounds (`exact_algorithm`, `NonVacuity.lean`), so the hypotheses of
Thm 2.8 are satisfiable. Model from CSLib (`Cslib.Computability.Distributed.Congest.*`); new
shared code staged in `Podc/Computability/Distributed/Congest/AliceOutput.lean` (simulation where
Alice outputs a global function of her nodes' states) and
`Podc/Computability/CommunicationComplexity/GapDisjointness.lean` (both CSLib candidates). Further
CSLib candidates: `LBFamily.ofArcs`, the directed-spanner definitions in `Spanner.lean`, and the
generic slowdown `slow k` (split `kB`-bit messages over `k` rounds; `slow_run`, `slow_out`) in
`VCReduction.lean`.
