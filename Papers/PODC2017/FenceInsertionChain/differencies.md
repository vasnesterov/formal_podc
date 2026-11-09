# Differences between the formalization and the paper

Paper: M. Lesani, *Brief Announcement: Fence Insertion for Straight-line Programs is in P*, PODC 2017 (3-page
author copy; no longer version exists).

## Mistakes (labeled, see README)

1. ✏️ **Running time (§3).** The paper claims `O(n·log n)` with `n = |V|`, but sorting the terminal pairs costs
   `O(|T| log |T|)`, and `|T|` can be `n(n−1)/2`. The loop runs `|T|` times. The paper's own justification ("dominated
   by the sort operation on the terminal pairs") gives the intended bound `O(|T| log |T|)`. That bound also needs
   the line-11 test in `O(1)`. As printed, the test scans `E′`. We prove that comparing `i` with the right end of
   the last triggering pair is equivalent (`chainMultiCut_eq_fast`). Running time itself is not formalized in a
   cost model.
2. ✏️ **Loops `(v, v)` in `T` (Definition 2.3 / Algorithm 1).** No multi-cut exists (`not_isMultiCut_of_diag`), but
   line 5 drops such pairs and Algorithm 1 returns an edge set. `algorithm_1_optimal` assumes `∀ p ∈ T, p.1 ≠ p.2`.
   Irrelevant for fence insertion (`→` is irreflexive).
3. (Reviewer: not a mistake, moved to the imprecisions below, see item 7a.)

## Typos / imprecisions (unlabeled)

4. Lemma 2.1 is written as an equation `OptFI(π) = λn. …`, but optima are not unique (`optFI_not_unique`). We prove
   that the union of *any* choice of the four restricted optima is an optimum (`Program.lemma_2_1`), and that the
   minimum sizes add up (`Program.lemma_2_1_size`). In Lemma 2.1, `OptFI(⟨p, →|c⟩)` is a multi-type insertion. We
   also prove that such an optimum uses only fences of type `c` (`IsOptIns.subset_singleton`), and the version with
   single-type optima the paper uses afterwards (`Program.lemma_2_1_single`).
5. Lemma 2.1's proof is one sentence ("straightforward"). The formal proof splits any insertion by fence type
   (`size_eq_sum_filter`) and compares with the restricted optima.
6. The optimality proof of Algorithm 1 does not state feasibility (every pair is cut), nor that `|E′|` equals the
   number of triggering pairs (each trigger adds a *new* edge). Both are part of `foldl_step_inv`. Disjointness is
   argued for consecutive triggers followed by "by induction". `foldl_step_inv` proves it for all pairs of
   triggers: a new trigger starts after every earlier cut edge.
7. Lemma 2.4 says `FenceIns ≤p MultiCut`. We formalize the two solution maps and their size and optimality
   preservation (`lemma_2_4`), not the polynomial-time bound on the maps. The maps are explicit `Finset`
   images and filters.

7a. Lemma 2.4, map `f ↦ {{i, i+1} | i ∈ f}`. For `|p| ∈ f`, the map produces the non-edge `{|p|, |p|+1}`. The paper
   applies the map to *solutions* of `FenceIns`, which are minimum-size insertions and never contain `|p|` (a fence
   after the last operation preserves no order), so the paper's claim is correct. `edgesOf` drops that index so the
   map is total; `|edgesOf F| ≤ |F|`, with equality for optimal `F`.

## Modelling choices

8. Positions are 0-indexed (`Fin |p|`): operation `k`, gap `k` after it, chain vertices `v_0 … v_{n−1}`, edge index
   `k` for `{v_k, v_{k+1}}`. The paper uses `1, …, |p|`.
9. Required orders and terminal pairs are `Finset (Fin n × Fin n)`. Algorithm 1 takes its input as a `List`, which
   it must enumerate anyway. `algorithm_1_optimal` is stated for `T.toFinset`.
10. Operations `Op D L X` follow the paper (`read`, `write(l, x)`, `write(l, d)`), with no finiteness assumptions
    on `D`, `L`, `X`; only `τ` matters. A concurrent system (a tuple of programs) is not modelled: fence insertion
    is per thread.
11. The generic layer (`Basic.lean`) allows any finite set `κ` of fence instructions and a per-order requirement
    `need : order → Option κ` (`none` = provided by the memory model). This covers both Lemma 2.1 and the remark
    after it (`Program.decomposition_merged`).
12. Section 4 (generalization to control structures) is not formalized; it states only open questions.

## Scope remark (not a mistake)

13. The decomposition of Lemma 2.1 fails when a category can be served by several fence instructions, as with
    ARMv8's `dmb ish` / `dmb ishst` / `dmb ishld` (`overlap_sum_gt_opt`). The paper's model (each fence type
    preserves only its own category) and its "merge categories" remark (one instruction per category) exclude this
    case. In that case the decomposition is still proved.
