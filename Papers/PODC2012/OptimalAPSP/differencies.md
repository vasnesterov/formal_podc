# Differences between the formalization and the paper

Paper: Holzer–Wattenhofer, *Optimal Distributed All Pairs Shortest Paths and Applications*, PODC 2012, preliminary
full version of 22.05.2012.

## Statement-level issues

1. **Theorem 5 is false (❌).** "Algorithm 2 computes S-SP in time `O(|S| + D)`" fails: Algorithm 2 computes
   wrong distances (`Alg2.theorem5_false`, `Alg2.exB_wrong`, `Alg2.triangle_wrong`); running longer does not
   help, since a set `δ` never changes (`Alg2.not_eventuallyCorrect`); it fails also with the natural repaired
   tie rule (minimal `δ` among same-round receipts) and every neighbour numbering (`exB_wrong` quantifies over all
   `Network 4` with the same graph). The fix (priority by distance, then ID) changes the
   algorithm. The title names APSP; the abstract's last sentence does say
   "At the heart of these approximation algorithms is the S-Shortest Paths problem which we solve in `O(|S| + D)`
   time", and the `(×, 1+ε)` diameter algorithm built on it is also announced there. But the abstract claims are
   existential (no specific algorithm is named), they are true (correct `O(|S| + D)` S-SP algorithms exist, e.g.
   Lenzen–Peleg's source detection), so they are only unestablished, not refuted. The false statement
   that names Algorithm 2, Theorem 5, is not itself advertised in the abstract.
2. Consequence (not formalized): Theorem 6, Corollary 4 and Theorem 7 rely on Theorem 5 and
   are unestablished in the paper (their bounds follow from a correct S-SP algorithm).
3. The running-time part of Theorem 5 is also off for the stated loop bound `|S| + D'` (`Alg2.exC_late`), with the
   paper's tie rule; this example is not robust (it depends on the numbering), so it is reported as a secondary
   observation.

## Proof gaps of true statements (🔧)

4. **Lemma 9**: the proof never shows `diam ≥ d` for disjoint inputs; repaired (`lemma9`, potential argument,
   needs `k(n) ≥ 1`, which holds since `n ≥ d + 6`).
5. **Lemma 8**: "any two nodes `u, v ∈ G_a` have distance at most `p + 3` via `c₀`" is false for `p ≥ 2`
   (`d(l'_ν, l'_ν') = 2p + 2`); the needed bound `≤ d + 2` holds (`lemma8`, `claim2`).
6. **Theorem 4**: fill-up to `n/2` nodes per side is impossible for odd `n`; we split `⌊r/2⌋ / ⌈r/2⌉`.

## Typos and slips

7. Index formula `k(n)·(μ − k(n) + 1) + ν` (§5.2) out of range; Figure 1 and Figure 2 captions use other indexings.
   Lean indexes inputs by `Fin k × Fin k` (any bijection works).
8. §7.1: "`i ∈ [n − 1]`" (Thm 9 proof), "`[n − 4k(n) + 1]`" in `E_b`, "`[n − 4k(n) − 2]`" in `V_b` (one node too
   many with `[k] = {0,…,k}`), "`{k(n), …, k(n) − 1}`" in the prose.
9. Lemma 16's proof: "diameter 2 from graphs of diameter 2"; Theorem 11's proof: "`n − 1`" instead of `n`.
10. Claim 2: `p + 3` is "less than `d`" — equal for `d = 4`.
11. Lemma 11's proof: "radius always 2 (as witnessed by `c_L`)" also needs that no vertex is adjacent to all others;
    proved (`Diam23.radius_eq_two`).

## Modelling choices and scope

12. **Model.** Deterministic synchronous CONGEST (CSLib `Algorithm`). Upper bounds use typed messages compiled to
    `msgBits M = ⌈log₂ |M|⌉` bits (`Cslib.Congest.TAlgorithm`, `run_toAlgorithm`); Algorithm 1 has
    `≤ 5⌈log₂(n+1)⌉ + 2` bits (`msgBits_le`), i.e. `B = O(log n)` as in the paper.
13. **Algorithm 1 details the paper leaves open** (all consistent with the pseudocode): `T₁` is the BFS tree whose
    parent is the smallest neighbour one step closer to `r`; stage 1 runs exactly `n` rounds (nodes know `n`), so
    `O(n)` instead of `O(D)`; children are learned from the neighbours' last stage-1 messages; the pebble visits
    pending children in increasing ID order (any DFS works); `BFS_v` starts in the waiting slot; a node forwards a
    token once, to all neighbours, in the round after first receiving it. Explicit constants: APSP after `5n`
    rounds, diameter/radius after `6n` rounds (the paper: `O(n)`).
14. **Aggregation.** Lemmas 3–6 aggregate by max/min flooding for `n` rounds instead of convergecast on `T₁`
    (`O(n)` either way). Definition 6's "each node knows" is formalized as fields of the final state.
15. **Lower bounds** are deterministic and unconditional (`CC(DISJ_K) ≥ K` is proved in CSLib). The paper's
    ε-error public-coin versions are formalized only conditionally (`theorem4_randomized`, `theorem8_randomized`:
    private coins, hypothesis `RandDisjLB` = randomized CC of disjointness, with real κ and nonempty coin spaces).
    The `+D` terms of the Ω-bounds are not formalized. Bounds are stated explicitly:
    `k² ≤ T·2(2k+1)B + 2` and corollaries `⌊(n−4)/(d+2)⌋ ≤ 4TB + 2` (Thm 4), `n ≤ 16TB + 13` (Thm 8).
16. **Promise.** Lower-bound hypotheses only require correctness on connected graphs of diameter in `{d, d+2}`
    (Thm 4) resp. `{2, 3}` (Thm 8), matching the paper's promise problems; node inputs are adjacency rows.
17. **Output conventions in Lemmas 10, 11, 16, Theorem 11.** Instead of "solve, then aggregate in `O(D)`", each node
    applies a local test and CSLib's acceptance is "all nodes accept"; this needs no aggregation. Lemma 10's
    "finding a peripheral vertex" is formalized as "each node decides whether it is peripheral" (a stronger output
    requirement, hence a weaker lower bound). Theorem 11's 2-BFS trees are formalized as membership in the trees
    (each node knows which nodes are within distance 2), not parent pointers. Lemma 16 is proved for the
    diameter-2/3 family only (the paper's extension by an attached path is not formalized).
18. **Algorithm 2** is modelled literally (`Algorithm2.lean`): IDs = vertex indices, neighbour index order given by a
    list; a received ID already in `L` is ignored and not removed from `L_i`; ties among same-round receipts by
    lowest index (paper) or minimal `δ` (repaired variant). The initialization's `D' = 2·ecc(1)` only fixes the
    number of rounds.
19. **Not formalized:** Lemma 7, Claim 1, Lemmas 12–14, Theorems 6, 7, 10, Corollaries 1–4, Remark 5 (odd `d`),
    the `(+,1)` / `(×, 3/2−ε)` parts of Lemma 11 (the `(+,1)` center part has no real proof in the paper: in the
    Theorem 4 graphs with `k(n) ≥ 2` the radius is `p + 2` in both cases), and the parts of Lemma 10 that rely on
    [22].
