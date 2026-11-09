# Fence Insertion for Straight-line Programs — PODC 2017

Mohsen Lesani. *Brief Announcement: Fence Insertion for Straight-line Programs is in P.* PODC 2017. DOI
[10.1145/3087801.3087849](https://doi.org/10.1145/3087801.3087849). Formalized version: the 3-page brief
announcement (author copy, mohsenlesani.github.io/companion/podc17/PODC17.pdf). It is self-contained, and no longer
version exists. Numbering follows it.

**Verdict: ✏️ Slip.** All three results hold: Lemma 2.1 (the problem splits by fence type), Lemma 2.4 (reduction to
multi-cut on a chain) and the optimality of the greedy Algorithm 1. The paper's two-fact optimality proof
formalizes as written. Only slips remain. The `O(n log n)` running time is stated in the number of vertices, but
the sort runs over the terminal pairs. One degenerate case is not handled: loops `(v, v)` in the multi-cut input.
Polynomial running time, the "in P" of the title, is argued in the paper but not formalized in a cost model.

## Mistakes in the paper

### ✏️ Slips
- **§3, running time.** "dominated by the sort operation on the terminal pairs; thus, it is `O(n·log n)`" uses
  `n = |V|`. There can be up to `n(n−1)/2` terminal pairs, and the loop of Algorithm 1 alone runs once per pair. The
  intended bound, also from the paper's own sentence, is `O(|T| log |T|)`. That bound needs a constant-time test on
  line 11, which the paper does not mention: as printed, the test scans the whole cut set `E′`. Comparing `i` with
  the right end of the last pair that added an edge gives the same result (`chainMultiCut_eq_fast`).
- **Algorithm 1 / Definition 2.3, loops.** Definition 2.3 allows any `T ∈ 𝒫(V × V)`. For a terminal pair `(v, v)`
  no multi-cut exists (`not_isMultiCut_of_diag`), yet line 5 silently drops the pair and the algorithm returns an
  edge set (the last `example` in `Greedy.lean`). This is harmless for fence insertion, where `→` is irreflexive.

### Typos
- Lemma 2.4, solution map `f ↦ {{i, i+1} | i ∈ f}`. Definition 2.2 allows `f ⊆ {1, …, |p|}`, and a fence at `|p|`
  would map to the non-edge `{|p|, |p|+1}`. The paper applies the map only to solutions, i.e. minimum insertions,
  which never contain `|p|`, so the claim is correct. Our `edgesOf` drops that index so the map is total.
- Lemma 2.1 writes `OptFI(π) = λn. …` as if minimum insertions were unique. They are not (`optFI_not_unique`). The
  intended reading, "the union of any four optima is an optimum", is what we prove (`Program.lemma_2_1`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Sequential and deterministic, as in the paper. Programs are straight-line lists of operations `x = read(l)`,
  `write(l, x)` and `write(l, d)` with types `τ ∈ {r, w}`. No concurrency semantics or memory model is modelled:
  "fence `fence(a, b)` preserves the orders of category `ab`" *is* the semantics, exactly as in the paper.
* Positions are `0, …, |p|−1` (the paper uses `1, …, |p|`). Gap `k` is right after operation `k`. A required order
  `i → j` is preserved iff a suitable fence lies in some gap `k` with `i ≤ k < j`.
* Multi-type insertions `f : Fin |p| → Finset FenceType` have size `∑ₖ |f k|` (§2). Single-type insertions
  (Definition 2.2) are sets of gaps.
* Multi-cut (Definition 2.3) is stated for an arbitrary Mathlib `SimpleGraph` via `deleteEdges` and `Reachable`. The
  chain is Mathlib's `pathGraph n`.
* Algorithm 1 takes the terminal pairs as a list (the input order is irrelevant after sorting). It sorts with
  `List.mergeSort` by right end and implements the line-11 test literally (`step`).
* Running time is not formalized in a cost model. We prove the loop equal to one with an `O(1)` test per pair
  (`chainMultiCut_eq_fast`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (independence of fence types) | `Program.lemma_2_1`, `Program.lemma_2_1_size`, `Program.lemma_2_1_single` | `Program.lean` |
| Lemma 2.1, abstract form | `isOptIns_biUnion`, `IsOptIns.size_eq_sum`, `isOptIns_of_isOptIns1` | `Basic.lean` |
| Remark after Lemma 2.1 (free / merged categories) | `Program.decomposition_merged`, `Program.decomposition_merged_single` | `Program.lean` |
| Definition 2.2 / 2.3 | `IsIns1`, `IsOptIns1` / `IsMultiCut`, `IsMinMultiCut` | `Basic.lean` / `MultiCut.lean` |
| Lemma 2.4 (`FenceIns ≤ MultiCut`) | `lemma_2_4` (with `isMultiCut_edgesOf`, `isIns1_cutIdx`, `card_cutIdx`) | `MultiCut.lean` |
| Algorithm 1 | `chainMultiCut` (literal), `chainMultiCutFast` (`O(1)` test), `chainMultiCut_eq_fast` | `Greedy.lean` |
| Optimality of Algorithm 1: first fact | `card_le_of_pairwiseDisjoint` | `Greedy.lean` |
| Optimality of Algorithm 1: second fact | `foldl_step_inv` | `Greedy.lean` |
| Algorithm 1 is a minimum multi-cut of the chain | `algorithm_1_optimal` | `Greedy.lean` |
| Title: greedy + Lemma 2.4 solve fence insertion optimally (optimality only; running time not formalized) | `fenceIns_greedy_optimal` | `Greedy.lean` |
| Figures 1 and 2 | `dekkerT1_opt`, `fig2b_valid`, `fig2_opt` | `Program.lean` |

The line-11 test is subtle in two cases, and both work. With ties (pairs with the same right end), the second pair
sees the edge `{v_{j−1}, v_j}` on its path. For a pair whose left end is an earlier cut's right vertex, the cut edge
`{v_{j−1}, v_j}` is not on the path `v_j … v_{j′}` (`i ≤ i′` fails). Both cases are covered by `example`s in
`Greedy.lean`. The paper proves path disjointness only for consecutive triggering pairs and then says "by
induction". The invariant we prove gives disjointness for all pairs at once: every triggering pair starts after
all earlier cut edges.

**Scope of Lemma 2.1 (remark, not a mistake).** In the paper's model, each fence type preserves only its own
category. The paper's remark extends this to memory models where some categories are free and categories that
share one fence instruction are merged. Both extensions hold (`Program.decomposition_merged`). The decomposition
fails when one category can be served by several instructions, as on ARMv8 (`dmb ish` covers everything,
`dmb ishst` only `ww`). For `write; write; read` with orders `ww` and `wr` from the first write, one `dmb ish`
suffices, but the per-category optima add up to 2 (`overlap_sum_gt_opt`). This is the setting of the NP-hardness
result in the DISC 2019 follow-up, and it lies outside this paper's model.

**Not formalized.** Running time in a cost model. That Lemma 2.4's maps run in polynomial time (they are explicit
`Finset` images and filters). Section 4 (generalization, open questions).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: optimal insertions exist (`exists_isOptIns`, `exists_isOptIns1`, `Program.exists_isOptFI`), and the
examples of Figures 1 and 2 are checked. Only Mathlib is used: `pathGraph`, `deleteEdges`, `Reachable`,
`List.mergeSort`.

CSLib candidates (marked `-- CSLib candidate`): the chain reachability characterization
`reachable_deleteEdges_iff` and the edge/index bijection `card_cutIdx` (`MultiCut.lean`). Also the optimality of greedy
interval stabbing, `foldl_step_optimal` with `card_le_of_pairwiseDisjoint` (`Greedy.lean`).
