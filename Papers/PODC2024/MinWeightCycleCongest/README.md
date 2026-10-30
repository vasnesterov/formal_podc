# Minimum Weight Cycle in CONGEST — PODC 2024

Vignesh Manoharan, Vijaya Ramachandran. *Computing Minimum Weight Cycle in the CONGEST Model.*
PODC 2024. DOI [10.1145/3662158.3662801](https://doi.org/10.1145/3662158.3662801).
Formalized version: the PODC paper's Theorems 1.2.A and 1.4.A. Their proofs are deferred to the full
version arXiv:2308.08670v3, which in turn defers them to the companion paper arXiv:2205.14797v2
(*Near Optimal Bounds for Replacement Paths and Related Problems in the CONGEST Model*, §3.1.1–3.1.2,
Lemmas 13–14, Figures 4–5). We formalize those proofs.

**Verdict: 🛠️ Proof repaired.** Both checked lower bounds hold as stated. Computing a
`(2 − ε)`-approximation of the minimum weight cycle (MWC) needs `Ω(n / log n)` CONGEST rounds, both
in directed graphs (weighted or unweighted) and in undirected weighted graphs, even on networks of
constant diameter. The proofs need two repairs. The cited constructions are disconnected, so the
"constant diameter" part is not proved there. And Lemma 14's argument covers only the heavy weight
`w = 2`, not the large `w` that the `(2 − ε)` claim needs.

## Mistakes in the paper

* **"Even on graphs with constant diameter" (Thm 1.2.A, 1.4.A) is not proved.** The graphs of
  Lemmas 13 and 14 in the cited proofs can be disconnected: for `S_a = S_b = ∅` they are perfect
  matchings. The companion paper adds a sink vertex with an arc from every vertex to get diameter 2,
  but only for its replacement-path bound, not for MWC. For directed MWC the same sink works, since
  a sink lies on no cycle. For undirected weighted MWC it must be done with care. A hub joined to all
  vertices by unit-weight edges creates triangles `hub–ℓ_i–r_i` of weight 3, below the gap `2w + 2`,
  and the reduction fails. We add a hub whose edges weigh `2w`. Then every cycle through the hub
  weighs at least `4w`, and the bound holds on diameter-2 networks. We also add pendant padding
  vertices so that every `n` is covered, not only `n = 4k`. The statements are true; this is a
  proof gap. (`dComap_ediam`, `uComap_ediam`, `theorem_1_2_A`, `theorem_1_4_A`)
* **Lemma 14's argument does not cover the heavy weight `w` needed for `(2 − ε)`.** For
  `(2 − ε)`-approximation, the paper changes the heavy weight 2 to a large `w` and says one must then
  tell cycles of weight `2w + 2` from cycles of weight `4w`. Its proof bounds cycles with at least 6
  edges as follows: the graph is bipartite and the light edges form a matching, so a cycle has at
  most as many light edges as heavy edges. With `w = 2` this gives weight at least 9. With weight `w`
  it only gives `3w + 3` for a 6-cycle, which is below `4w` once `w > 3`. The claim is still true:
  light edges are the only edges between Alice's side `L ∪ L′` and Bob's side `R ∪ R′`, so every
  cycle has an even number of light edges. A 6-cycle therefore has at most 2 light edges and weighs
  at least `4w + 2`. The lemma is true; the proof needed this parity step. (`uGraph.weight_ge`)
* **Slips** (all in the companion paper's proofs, none affects a result):
  - The directed proof decides "by checking if the minimum cycle has length at least 4". Every
    cycle has length at least 4; the test should be "at least 8" (or "greater than 4").
  - The undirected proof likewise says "weight at least 6" where it should be "> 6" (or "≥ 8").
  - Both proofs say "the cut has `4k` edges". The graphs as constructed have `2k` cut edges (our
    graphs with a hub have `4k`). This is harmless.
  - In Lemma 14 the case list of 4-cycles leaves out the all-heavy cycles `r_i r′_j r_p r′_q` on
    Bob's side. They weigh `4w`, like the listed `ℓ_i ℓ′_j ℓ_p ℓ′_q`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous CONGEST, deterministic (`Cslib.Congest.Algorithm`). Node IDs are the vertex names, and
  the vertex type `V` is arbitrary with `|V| = n`. Messages have exactly `B` bits per edge, direction
  and round. Nodes have unbounded local computation. There are no failures.
* The network is the underlying undirected unweighted graph (§1.1). Node `v`'s input is the weights
  of its incident arcs in both directions (directed case, `WDigraph.view`) or of its incident edges
  (`WGraph.view`). Weights lie in `{0, …, W}`.
* MWC is the minimum weight of a simple cycle, `∞` if there is none (Def. 1.1). Simple cycles are
  periodic sequences of distinct vertices, of length `≥ 2` (directed) or `≥ 3` (undirected).
* Output convention (`ApproxOutput`): every node outputs `none` or an estimate. At least one node
  outputs an estimate, and every estimate `e` satisfies `MWC ≤ e ≤ α · MWC`. The paper's own
  algorithms meet this, and it is the weakest convention its lower bounds claim ("even when only one
  node is required to know the weight").
* The hypothesis is weaker than "solves MWC". The directed algorithm need only be correct on
  unweighted digraphs whose underlying network has diameter `≤ 2`. The undirected one need only be
  correct on weighted graphs of diameter `≤ 2`, with `W ≥ W₀(α)`. So the theorems cover weighted and
  unweighted algorithms and the constant-diameter claim.
* Bounds are explicit: `n ≤ 32 · B · T + 12`, i.e. `T = Ω(n / B) = Ω(n / log n)` for
  `B = Θ(log n)`. Set disjointness on `k²` bits is embedded into graphs with `n = 4k + 1 + p` nodes
  and `4k` cut edges. The deterministic bound `CC(DISJ_K) ≥ K` is proved in CSLib.
* Randomized versions (the paper: "all our lower bounds hold for randomized algorithms") use private
  random strings per node. They are *conditional* on the randomized communication lower bound for
  set disjointness (Razborov / Kalyanasundaram–Schnitger), which enters as the hypothesis
  `RandDisjLB δ κ` (private-coin protocols with nonempty finite uniform coin spaces) and is not
  formalized.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 1.2.A (directed, deterministic) | `theorem_1_2_A` (`theorem_1_2_A_family`: `k² ≤ 8k·B·T + 2`) | `LowerBound.lean` |
| Thm 1.2.A (randomized, given `RandDisjLB`) | `theorem_1_2_A_rand` | `LowerBound.lean` |
| Thm 1.4.A (undirected weighted, deterministic) | `theorem_1_4_A` (`theorem_1_4_A_family`) | `LowerBound.lean` |
| Thm 1.4.A (randomized, given `RandDisjLB`) | `theorem_1_4_A_rand` | `LowerBound.lean` |
| §1.2.1: directed 4-cycle detection needs `Ω̃(n)` | `directed_four_cycle_lowerBound` | `LowerBound.lean` |
| [38] Lemma 13 (gap 4 vs ≥ 8) | `dGraph_mwc_le`, `dGraph_mwc_ge`, `dGraph.len_ge_eight` | `DirectedGadget.lean` |
| [38] Lemma 14 (gap `2w+2` vs ≥ `4w`, any `w ≥ 1`) | `uGraph_mwc_le`, `uGraph_mwc_ge`, `uGraph.weight_ge` | `UndirectedGadget.lean` |
| Reduction from set disjointness (approximation gap) | `approx_lowerBound`, `approx_rand_lowerBound` | `Reduction.lean` |

**Not formalized.** Thm 1.2.B/1.3.A/1.4.B (the `Ω̃(√n)` and `Ω̃(n^{1/4})` bounds for larger
approximation factors, via Das Sarma et al.), 4-cycle detection for `q ≥ 5`, and all upper bounds
(Thm 1.2.C–D, 1.3.B, 1.4.C, 1.6), which are randomized, w.h.p. algorithms.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `gather_approx_directed` and `gather_approx_undirected` (`NonVacuity.lean`)
show that full-information flooding computes the exact MWC in 2 rounds on diameter-2 networks, so the
algorithm hypotheses can be met. `RandDisjLB` quantifies only over nonempty coin spaces; without that
restriction it would force `κ ≤ 0` and make the randomized theorems vacuous
(`randDisjLB_without_nonempty_degenerate`). The model and the simulation theorem come from CSLib
(`Cslib.Computability.Distributed.Congest.LowerBound`, `.Randomized`). The flooding algorithm is in
`Podc/Computability/Distributed/Congest/GatherInputs.lean`.

**CSLib candidates.** `Podc/Computability/Distributed/Congest/GatherInputs.lean` (gathering of
arbitrary finite inputs), and `ofWeights`, `thresholdAlg`, `approx_lowerBound`,
`approx_rand_lowerBound` in `Reduction.lean` (gap reductions for approximation lower bounds).
