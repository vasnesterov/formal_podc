# Differences between the formalization and the paper

Paper: Montealegre–Todinca, PODC 2016 BA; formalized version arXiv:1602.04095v3.

## Mistakes (labels per `mistakes-labeling.md`)

- ✏️ **Proposition 2 / proof of Theorem 3: "girth at least `2r`".** False as printed for `r = 2`: `K_{m,m}` has
  girth 4 and degeneracy `n/2` (`proposition_2_false`, which refutes it for every constant `C` and threshold
  `n₀`). Corrected: girth `> 2r` (no cycle of length `≤ 2r`) and `n ≤ s^r` give `s`-degeneracy (`proposition_2`).
  This is all that Theorem 3 uses, since `G̃` has no cycle of length `≤ 2r` (`prunedGraph_noShortCycles`).
- 🔧 **Theorem 1, proof sketch: stopping rule / count of active supernodes.** "Stop when every supernode is
  inactive" together with `n_{t+1} ≤ n_t / n^ε` gives only `n_{⌈1/ε⌉} ≤ 1`. For `ε = 1` and connected `G`, the
  protocol as described runs 2 rounds. Repaired: fixed `⌈1/ε⌉` rounds, and the count uses open supernodes, so
  `o_t (k+1)^t ≤ n` (`Supernodes.card_openComps_mul_pow_le`). Not proved in Lean: the claim that the literal
  stopping rule needs an extra round (it is only arithmetic, `n ≥ n^1`). The paper defines "active" only for rounds
  `t > 1`; we read it as `t ≥ 1`.

## Modelling choices and minor imprecisions

- **IDs.** The paper allows IDs bounded by a polynomial in `n`. We use `Fin n` and index the adjacency rows by
  `Fin n`. With IDs in `[N]`, `N = poly(n)`, Lemma 1 applies with dimension `N` and the bounds change by constant
  factors.
- **Messages.** Typed messages (`TAlg`) are encoded into `b` bits by a fixed injection whenever `|M| ≤ 2^b`.
  Bit counts are explicit instead of `O(·)`:
  - Theorem 1: `⌈n^ε⌉ · ⌈log₂(n+1)⌉` (a set of at most `k` IDs).
  - Theorem 2: `⌈log₂((n+1)·p)⌉ ≤ (2d+2)⌈log₂(n+1)⌉ + 1`.
  - Theorem 3: the same with `d = s = min{s : n ≤ s^r} < n^{1/r} + 1`.
- **`n^ε` not an integer.** We use `k = ⌈n^ε⌉₊` neighbours per round. Theorem 1 holds for every `ε > 0`; the
  hypothesis `ε ≤ 1` is unused.
- **Selection in Theorem 1.** Each node announces `min(k, #foreign supernodes)` neighbours in pairwise distinct
  supernodes other than its own (the introduction's "outside its current cluster"). The choice is arbitrary but
  fixed.
- **Lemma 1.** The point `x` is a fixed common non-root (`sketchPoint`), not necessarily the least one; any fixed
  choice works. The paper does not state `|T| ≤ (1+n)^{2d}`, which its proof needs. It holds because
  `|B| ≤ (1+n)^d` (`card_small_le`), so `|T| ≤ |B|²`. Each `P(t, X)` has degree `≤ n−1` and at most `n` roots.
  We use the bound `n`.
- **Theorem 2 output.** The paper's "computes a `d`-pruning". We output the pruning sequence (decoder: least
  remaining index of current degree `≤ d`) and the set of all edges of `G` incident to it.
- **Theorem 3, `BClique_r` input.** Node `v` receives `localView G r v`: the edges of `G` between vertices at
  distance `≤ r` from `v`. The ball is defined by walks of length `≤ r`. We assume `r ≥ 1` (the paper's `r > 0`).
  The paper's statement "a node sees all cycles of length `≤ 2r` through it" is proved as
  `isHeavy_localView_iff`.
- **Edge order.** Propositions 1 and 2 are proved for any injective edge rank `w`. Injectivity is needed: with
  ties, every edge of a triangle can be "maximal". Theorem 3 uses the paper's lexicographic order (`lexRank`).
- **Spanning forest.** It is maximal (footnote 1): an acyclic `F ≤ G` with the same connected components as `G`.
  The protocols output a fixed spanning forest of the graph known at the end (`A_T` in Theorem 1, the
  reconstructed `G̃` in Theorem 3).
- **Same output at every node.** The paper requires all nodes to output the same. Our theorems state only that
  every node's output is correct; in all three protocols the output depends only on the broadcast messages, so it is
  the same at every node, but this is not stated as a theorem.
- **Not formalized.** The optimality remark after Theorem 2 (`2^{Ω(nd log n)}` `d`-degenerate graphs) and the
  remarks of the Discussion.
