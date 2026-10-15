# Simpler and More General Distributed Coloring Based on Simple List Defective Coloring Algorithms

Marc Fuchs, Fabian Kuhn (University of Freiburg; author list checked against the PDF and DBLP).
*Brief Announcement*, PODC 2024, pp. 425–428. DOI
[10.1145/3662158.3662808](https://doi.org/10.1145/3662158.3662808). The brief announcement defers its
proofs to the full version, arXiv [2405.04648](https://arxiv.org/abs/2405.04648) v1 (7 May 2024). That
version is the local PDF and is what we formalize. It is cited as [FK24].

## Status

**Done. No `sorry` or `axiom`.** `#print axioms` on all main theorems shows only `propext`,
`Classical.choice` and `Quot.sound`.

Formalized:
* Section 3.1 in full: Algorithm 1 (Two-Sweep) as a synchronous distributed algorithm, and Lemmas 3.1–3.3.
* Theorem 1.1, for both `ε = 0` and `ε > 0`. Lemma 3.4 is cited by the paper, so it is a hypothesis here.
* The corollaries stated in Section 1.1.
* The arithmetic of Theorem 1.2.
* Section 4.1 in full: Claim 4.1, Lemmas 4.2 and 4.3, and Theorem 1.4, with non-vacuity.
* Lemmas 4.4, 4.5 and A.1 as reductions at the level of specifications.

The main algorithmic result (Section 3) is **correct**. Lemma 3.1's proof has a flawed last step, which is fixed
here. **No stated theorem of the paper is refuted.** Section 4 has three issues in proofs or constructions. Each
has a Lean counterexample and a fix:

1. **Eq. (10) has a floor/ceiling slip.** The paper defines `d' = ⌊(d+1)/(7θ)⌋ − 1` and states `d' ≥ 0`. In fact
   `d' = −1` whenever `d < 7θ − 1`, and then eq. (11) fails.
   * With this `d'`, the Section 4.1 algorithm as defined colours no node. This happens for every colour with
     `d < 7θ − 1`, including all proper list colouring, so it is not a degenerate case. Example: proper list
     colouring on the triangle (`Sec41.theorem_1_4_paper_defects_false`).
   * With `d' = ⌈(d+1)/(7θ)⌉ − 1 = ⌊d/(7θ)⌋`, Theorem 1.4 holds (`Sec41.theorem_1_4`). The constant 7 can even
     be 4.
2. **Lemma 4.5 (colour space reduction) has a gap in its proof's construction.** A node may choose a subspace that
   contains none of its colours, which leaves it with an empty list (`ColorSpace.paper_counterexample`).
   * The fix is trivial: only offer subspaces that meet `L_v` (`lemma45`). The lemma's round-time statement is not
     refuted.
3. **Lemma A.1 has a genuine proof error.** The slack step `deg(v) − deg~(v) ≥ Δ − Δ/2` fails for nodes of degree
   `< Δ`. There is a 15-node counterexample (`SlackReduction.paperA1_counterexample`).
   * This affects the round-complexity argument. The existence of a colouring is unaffected.
   * Fix: test `deg~(v)` against half of the node's own residual degree (`lemmaA1`).

All differences, including smaller slips, are listed in `differencies.md`.

Not formalized:
* Lemma 3.4 ([Kuh09, KS18] defective colouring), Lemma 3.5 (Theorem 3 of [FK23a]) and Theorem 4 of [FK23a].
  The paper cites these as black boxes.
* Hence Theorem 1.2 and Theorem 1.3 are not formalized beyond their arithmetic.
* Theorem 1.5 and Lemma 4.6: these are round-complexity recursions in `O`-notation over the cited black boxes.
* All round complexities that go through black boxes, and all CONGEST message sizes. These appear in
  docstrings only.

Rough token spend: about 0.75M in total (paper agent about 0.45M, subagents about 0.16M and 0.14M).

## Model

* **Graphs.** `G : SimpleGraph V`.
  * Section 3 allows any `V`; only out-neighbourhoods are counted.
  * Section 4 uses `[G.LocallyFinite]` or `[Fintype V]` graphs.
* **Out-neighbourhoods.** An arbitrary `out : V → Finset V` with `u ∈ out v → G.Adj v u`.
  * The paper's edge orientation is a special case.
  * `out v = N(v)` turns OLDC into list defective colouring (used in `twoSweep_threeColoring`).
  * `β_v = max 1 |out v|`, as in the paper's Section 2 (`beta`).
* **Instances.** `ListInstance V α` consists of lists `L v : Finset α` and defects `d v : α → ℕ`.
  * Solutions: `IsOLDC`, `IsListDefective` and `IsListArbdefective`. In the last, an orientation `O` of the
    monochromatic edges is part of the output.
  * Slack: `HasSlack` (Definition 1.1), stated with a real `S`.
* **Distributed model (Section 3).** Synchronous, deterministic, fault-free LOCAL rounds. The model is CSLib's
  `Cslib.LocallyIterative.Algorithm`: a node's new state is a function of the round number, its own state and the
  *set* of its neighbours' states.
  * A node's state holds its identifier, its initial colour, its out-neighbour identifiers, its list and defect
    function (the local input), and its outputs `S_v` and `x_v`.
  * The step function does not depend on `G`.
  * Initial colouring: any `c : V → ℕ` with `c v < q` that is proper along out-edges, for example a proper
    `q`-colouring (`IsProper G c`).
  * All nodes know `p` and `q`.
  * Message sizes (CONGEST) are not modelled. Nodes broadcast their full state.
* **Section 4.1 (iterations).** The arbdefective subroutine `A` is not fixed. A run (`Sec41.IsRun`) is any
  assignment of an iteration `it : V → Option ℕ` and a colour `col` such that:
  * iteration `i` colours exactly `H_i` (eq. 13), from the lists `L_{v,i}` (eq. 12);
  * the colouring of each iteration is `d_i`-arbdefective. This is the output specification of `P_A(S, C)`.

  Runs exist (`Sec41.exists_isRun`, via a greedy list-arbdefective colouring). The round count
  `(⌈log Δ⌉+1)·T_A(S,C)` is in docstrings only.
* **Lemmas 4.4, 4.5 and A.1.** Each is a spec-level reduction: any solutions of the sub-instances (universally
  quantified) combine into a solution of the original instance, and the sub-instances have the claimed slack.
  * The defective colouring of Lemma 3.4 is a hypothesis.

## Theorem ↔ Lean map (namespace `FK24`)

| Paper | Lean | File |
|---|---|---|
| Definitions (OLDC, list defective/arbdefective, slack, `β_v`) | `ListInstance`, `IsOLDC`, `IsListDefective`, `IsListArbdefective`, `HasSlack` (Def. 1.1), `beta` | `Basic.lean` |
| Eq. (2) ↔ integer form | `slack_iff_nat` | `SubsetSelection.lean` |
| Double counting in the proof of Lemma 3.1 | `sum_powersetCard_sum`, `IsBestSubset.mul_sum_le` | `SubsetSelection.lean` |
| **Lemma 3.1** + Remark | `lemma_3_1`, `IsBestSubset.lemma_3_1`, `IsPhaseI.eq3_eq4` | `SubsetSelection.lean`, `TwoSweep.lean` |
| Alg. 1 line 4 (sort, take first `p`) | `isBestSubset_take`, `sum_le_sum_take` | `SubsetSelection.lean` |
| Phases I/II (spec) | `kCount`, `rCount`, `IsPhaseI`, `IsPhaseII` | `TwoSweep.lean` |
| **Lemma 3.2** | `exists_phaseII_color`, `IsPhaseII.isOLDC` | `TwoSweep.lean` |
| Algorithm 1 (distributed) | `twoSweep`, `NodeState`, `initState`, `TwoSweepAlg.step` | `Distributed.lean` |
| **Lemma 3.3** = **Thm 1.1** (`ε = 0`) | `twoSweep_correct`, `twoSweep_correct_of_isProper` (`2q` rounds) | `Distributed.lean` |
| Abstract: lists of size `p²`, slack `pβ` | `twoSweep_correct_sq` | `Distributed.lean` |
| Sec. 1.1: list colouring with lists `≥ β²+β+1` | `twoSweep_listColoring` | `Distributed.lean` |
| Sec. 1.1: list `d`-defective 3-colouring for `d > (2Δ−3)/3` | `twoSweep_threeColoring` | `Distributed.lean` |
| Algorithm 2, **Thm 1.1** (`ε > 0`) | `fastTwoSweep_correct`; `reducedSlack` (first display), `IsOLDC.of_reduced` | `FastTwoSweep.lean` |
| Thm 1.2, arithmetic (eq. (8), `< 3√C`) | `kappa_pow_lt_three_sqrt`, `theorem12_slack` | `Theorem12.lean` |
| **Claim 4.1** | `claim_4_1`; core `SimpleGraph.exists_isIndepSet_card_le_mul`, `SimpleGraph.card_le_of_subset_neighborSet`, `SimpleGraph.NeighborhoodIndepLE` | `NeighborhoodIndependence.lean` |
| Sec. 4.1 algorithm | `Sec41.IsRun`, `aCount`, `Cond` (12), `InL`/`listAt` (`L_{v,i}`), `InH` (13), `dI` | `Section41.lean` |
| **Lemma 4.2** | `Sec41.lemma_4_2` | `Section41.lean` |
| **Lemma 4.3** | `Sec41.lemma_4_3`; sharper `Sec41.lemma_4_3_sharp` (`X_v ≤ 4θ d'`) | `Section41.lean` |
| **Theorem 1.4** (corrected `d'`) | `Sec41.theorem_1_4`, `Sec41.theorem_1_4_paper_slack` (slack `42θ log₂Δ·S`), `Sec41.clog_add_one_le_two_logb` | `Section41.lean` |
| Eq. (10) floor/ceiling slip | `Sec41.theorem_1_4_paper_defects_false`, `Sec41.Counterexample.eq11_fails`, `lemma_4_2_fails` | `Section41Counterexample.lean` |
| Non-vacuity of Thm 1.4 | `Sec41.exists_isRun`, `Sec41.theorem_1_4_exists`, `exists_listArbdefective_greedy` | `Section41Exists.lean` |
| **Lemma 4.5** (fixed lists) | `lemma45` (`ColorSpace.choice_hasSlack`, `sub_hasSlack`, `isListArbdefective_of_sub`) | `ColorSpaceReduction.lean` |
| Lemma 4.5 proof construction (gap) | `ColorSpace.paper_counterexample` | `ColorSpaceReduction.lean` |
| **Lemma 4.4** | `lemma44` | `SlackReduction.lean` |
| Lemma A.1 proof (slack step fails) | `SlackReduction.paperA1_counterexample` | `SlackReduction.lean` |
| Lemma A.1 (fixed) | `lemmaA1`, `SlackReduction.lemmaA1_slack_node`, `lemmaA1_halving`, `two_pow_le_of_halving` | `SlackReduction.lean` |
| Thm 1.3, Lemma 4.6, Thm 1.5 | not formalized (black boxes, `O`-recursions) | — |

## CSLib candidates

* `ncard_nbrColors_filter` (`Distributed.lean`): it counts out-neighbours through the set of neighbour states
  when states carry identifiers. It belongs next to `Cslib.LocallyIterative.nbrColors`.
* `SimpleGraph.NeighborhoodIndepLE`, `SimpleGraph.exists_isIndepSet_card_le_mul` (an orientation with
  out-degree `≤ d` gives an independent set of size `≥ |W|/(2d+1)`) and
  `SimpleGraph.card_le_of_subset_neighborSet` (`NeighborhoodIndependence.lean`).
* `exists_listArbdefective_greedy` (`Section41Exists.lean`): the greedy list arbdefective colouring.
* `sameClass` (`ColorSpaceReduction.lean`): `G` restricted to the edges inside the classes of a map.
* `sum_powersetCard_sum`, `IsBestSubset.mul_sum_le` and `sum_le_sum_take` (`SubsetSelection.lean`): averaging
  over `m`-subsets, and optimality of the sorted prefix.
* The definitions in `Basic.lean`, if other list-colouring papers appear.
