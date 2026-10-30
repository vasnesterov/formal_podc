# Differences between the formalization and the paper

Paper: Kosowski, Uznański, Viennot, *Hardness of exact distance queries in sparse graphs through hub
labeling*, PODC 2019 (arXiv 1902.07055v3). Scope: Section 2 (Theorem 2.1, Lemma 2.2, Theorem 1.1).

## Errors and gaps in the paper

1. **False claim in the proof of Lemma 2.2** (inside a proof → R1: proof repair, 🛠️).
   * The paper says: "for any `u ∈ V_i` and `v ∈ V_j` with `i < j`, `dist_G(u,v) = dist_H(u,v)`",
     justified by "the construction" for `j = i + 1` and by vertex cuts for `j > i + 1`.
   * It is false. In `G` a walk may turn around inside an in-tree (leaf → root → other leaf) without
     visiting the tree's vertex. That is shorter than the corresponding `H`-walk.
   * Counterexample (`dist_claim_false`): `b = 1`, `ℓ = 2`, `u = v_{0,(0,0)}`, `v = v_{1,(0,1)}`,
     with `d_G(u, v) ≤ 71 < 73 ≤ d_H(u, v)`.
   * The consequence actually used, the case `v_{0,x}`, `v_{2ℓ,z}` with `z − x` even, is true:
     `d_G = d_H = Lopt`, and every shortest `G`-walk passes through `v_{ℓ,(x+z)/2}`
     (`lemma_2_2_G`).
   * The repaired proof uses a potential that changes by at most 1 per edge (`pot`, `abs_pot_sub_le`),
     the level reflection (`refl`) and the cut at level `ℓ` (`exists_mem_support_midLevel`); see
     `Distances.lean`. The upper bound `d_G ≤ d_H` between vertices of `H` does hold
     (`edist_main_le_wlen`).
2. **Lemma 2.2 for `H`: routine gaps** (🛠️ at most; the statement is true). The proof does not show:
   * that a walk with exactly `2ℓ` edges is monotone in the level;
   * that `a² + b²` with `a + b` fixed and even has the unique minimizer `a = b`;
   * that this determines every vertex of the path;
   * that `Lopt < (2ℓ + 1)A`, which needs `ℓ ≥ 1`.

   All four are proved in `HLemma.lean`.
3. **Inequality (1)** `|S*_v| ≤ diam(G)·|S_v| ≤ (3ℓ+1)s²·4ℓ·|S_v|`. The diameter bound is asserted
   without proof (and `diam` should be `diam + 1`, counting vertices). We avoid it: only hubs `h` of
   `v` with `d(v, h) ≤ L := 8ℓ²s²` can serve the counted pairs, and `L ≥ Lopt`. So
   `S*_v` := union of fixed shortest paths to those hubs has size `≤ (L + 1)|S_v|`
   (`SimpleGraph.hubPathSet`, `card_hubPathSet_le`). The paper also uses shortest-path *trees*; we
   use arbitrary fixed shortest paths, which suffice.
4. **Typos.** "a path of length `w(e) − 2b + −2`" should be `w(e) − 2b − 2`. In
   "`V = ⋃_{r=0}^{2ℓ} V_i`" the union index is mismatched.

## Statement-level choices (no error in the paper)

* **Θ in lower bounds.**
  * Theorem 2.1 (iii) "`≥ 2^{bℓ}·2^{−Θ(b+ℓ)}`" is proved as `≥ 2^{bℓ}/2^{10(b+ℓ)}` (`theorem_2_1`).
  * Theorem 1.1 "`≥ n/2^{Θ(√log n)}`" is proved as `≥ n/2^{29√(log₂ n)}` (`theorem_1_1`).
  * In a lower bound only the `O` direction of the `Θ` has content.
* **Theorem 2.1 (i)** is proved as `2ℓ·s^{ℓ+1} ≤ |V| ≤ 16ℓ²·s^{ℓ+3}`. Since `ℓ·s = 2^{b + log₂ ℓ}`,
  this is `|V| = 2^{bℓ}·2^{Θ(b + log ℓ)}`.
* **Theorem 1.1** ("graphs of max-degree 3 require …") is proved for infinitely many `n`: for every
  `N` there is a graph with `≥ N` vertices, namely `G_{m,m}` with `m = N + 1`. The paper takes
  `b = ℓ = √(log N)` with an adjusted `N` and does not discuss rounding; we use the graphs `G_{m,m}`
  directly. "Every `n`" (by padding) is not formalized.
* **Hub labeling definition** (`SimpleGraph.IsHubLabeling`). We require a common hub on a shortest path
  (`edist u w + edist w v = edist u v`) only for reachable pairs. This is identical on connected
  graphs and weaker in general, so our lower bounds are slightly stronger. We do not prove that
  `G_{b,ℓ}` is connected; it is not needed.
* **Factor 2 in the counting.** `card_le_mul_sum` gives `|P| ≤ 2(L+1)·Σ_v|S_v|`, without using that
  the sources `V_0` and targets `V_{2ℓ}` are disjoint. This costs a constant factor, absorbed in the
  explicit constants.
* **Weights.** `hw u v = A + Σ_k (u_k − v_k)²`. On edges this equals the paper's `A + (j_c − j'_c)²`,
  because adjacent vectors differ only at `c`.
* **Coordinates are 0-indexed.** The changed coordinate between levels `i, i+1` is `i` for `i < ℓ` and
  `2ℓ − 1 − i` for `i ≥ ℓ` (the paper's `c = i + 1`, resp. `2ℓ − i`).
* **Heap numbering** of the trees: node `n` has children `2n+1, 2n+2`, and the leaf of value `t` is
  `s − 1 + t`. In-trees of `V_0` and out-trees of `V_{2ℓ}` are omitted, as in the paper.
* **Degree.** `Δ(G_{b,ℓ}) = 3` is stated as `maxDegree = 3` (for any `DecidableRel` instance), plus
  `ncard_neighborSet_le`, the version without a decidability instance.
* Assumptions `b, ℓ ≥ 1` throughout, matching "positive integers". For `b = 0` the parity triples
  degenerate.

## Not formalized

* Uniqueness of the shortest `v_{0,x}`–`v_{2ℓ,z}` path in `G` (the "consequently also in `G`" part
  of Lemma 2.2). We prove the distance and that all shortest walks pass through `v_{ℓ,(x+z)/2}`,
  which is all the theorem uses.
* Section 3 (Theorem 1.6 / Observation 3.1, the Sum-Index reduction) and Section 4 (Theorems 4.1,
  1.4, Lemma 4.2, the Ruzsa–Szemerédi upper bound).
