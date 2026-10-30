# Hardness of Hub Labeling in Sparse Graphs — PODC 2019

Adrian Kosowski, Przemysław Uznański, Laurent Viennot. *Hardness of exact distance queries in sparse
graphs through hub labeling.* PODC 2019. DOI
[10.1145/3293611.3331625](https://doi.org/10.1145/3293611.3331625). Formalized version: arXiv
[1902.07055](https://arxiv.org/abs/1902.07055) v3; numbering follows it.

**Verdict: 🛠️ Proof repaired.** The hub-labeling lower bound holds as stated. This covers Lemma 2.2
for the weighted layered graph `H_{b,ℓ}`, the pass-through and distance part of Lemma 2.2 for the
degree-3 graph `G_{b,ℓ}`, Theorem 2.1 (i)–(iii) and Theorem 1.1, all with explicit constants. One step
of the proof of Lemma 2.2 is false: the claim that `G_{b,ℓ}` preserves all distances of `H_{b,ℓ}`
between levels. Only the special case the theorem needs is true, and it needs a different argument.

## Mistakes in the paper

* **False claim in the proof of Lemma 2.2; the lemma's use is fine.** To transfer Lemma 2.2 from
  `H_{b,ℓ}` to `G_{b,ℓ}`, the proof asserts that `dist_G(u, v) = dist_H(u, v)` for all `u ∈ V_i`,
  `v ∈ V_j` with `i < j`. For `j = i + 1` it cites "the construction". This is false.
  * The mechanism: in `G`, a walk can enter the in-tree `T_w^in` of an upper vertex `w` through one
    leaf and leave it through another leaf without visiting `w`. That saves up to `2b` steps. The
    corresponding `H`-walk `u → w → u'` must pay both full edge weights.
  * Counterexample: `b = 1`, `ℓ = 2` (`A = 24`), `u = v_{0,(0,0)}`, `v = v_{1,(0,1)}`.
    * Every `H`-walk from `u` to `v` needs at least 3 edges, one of them changing coordinate 2, so it
      weighs `≥ 3A + 1 = 73`.
    * `G` has a walk of length `71`: `u → v_{1,(0,0)} →` in-tree of `v_{2,(0,1)}` (leaf `0`, root,
      leaf `1`) `→ v_{1,(0,1)}`.

    (`dist_claim_false`)
  * The vertex-cut argument for `j > i + 1` inherits the same gap.
  * Theorem 2.1 only needs the case `u = v_{0,x}`, `v = v_{2ℓ,z}` with `z − x` even, and there the
    conclusion is true. For this pair `d_G = d_H = 2ℓA + Σ_k (z_k − x_k)²/2`, and every shortest
    `G`-walk passes through `v_{ℓ,(x+z)/2}` (`lemma_2_2_G`).
  * The repaired proof uses potentials, not a walk-by-walk comparison with `H`:
    * An integer function on `V(G)` changes by at most 1 per edge. It is `0` at `v_{0,x}` and
      `ℓA + Σ_k (j_k − x_k)²` at `v_{ℓ,j}`. Coordinates not yet "reached" carry a correction term
      `2(s−1)|d| − d²`, and the potential interpolates linearly along trees and paths. The slack
      `A = 3ℓs² ≫ s² + b` absorbs the turnaround shortcuts.
    * The level reflection of `G` gives the same bound from `v_{2ℓ,z}`.
    * `V_ℓ` separates the bottom from the top. Summing the two bounds gives
      `Lopt + 2 Σ_k (j_k − m_k)²` for a walk through `v_{ℓ,j}`, with `m = (x+z)/2`.
* **Smaller gaps in the proof of Lemma 2.2 for `H`; statement true.** The proof does not argue that a
  walk with exactly `2ℓ` edges climbs one level per edge. It does not say why minimizing
  `δ_i² + δ_{2ℓ+1−i}²` under a fixed sum has a unique solution, or why that pins down every vertex
  of the path. These are routine, and we fill them in (`lemma_2_2`).
* **Bound (1) on `S*_v` is not checked; we avoid it.** The proof bounds `|S*_v| ≤ diam(G_{b,ℓ})·|S_v|`
  with an unproved diameter estimate. We instead count only hubs within distance
  `L = 8ℓ²s² ≥ Lopt` of `v`. These are the only hubs that can serve the counted pairs, so
  `|S*_v| ≤ (L+1)|S_v|` without any diameter bound.
* **Asymptotic notation.**
  * Theorem 2.1 (iii) "`≥ 2^{bℓ}·2^{−Θ(b+ℓ)}`" and Theorem 1.1 "`n/2^{Θ(√log n)}`" are lower bounds,
    so only the `O(·)` direction of the `Θ` is meaningful. We prove explicit constants:
    `2^{bℓ}/2^{10(b+ℓ)}` and `n/2^{29√(log₂ n)}`.
  * Theorem 1.1 is proved for infinitely many `n`, the usual reading of such a lower bound.
* Typos: "path of length `w(e) − 2b + −2`" should be `w(e) − 2b − 2`. "`V = ⋃_{r=0}^{2ℓ} V_i`" has a
  mismatched index.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Pure graph combinatorics; there is no distributed model, randomness or adversary.
* `H_{b,ℓ}` is a `SimpleGraph` on `Fin (2ℓ+1) × ([0,s−1]^ℓ)` (`s = 2^b`, `A = 3ℓs²`). It has
  integer weights `A + Σ_k (u_k − v_k)²`, which is the paper's `A + (j_c − j'_c)²` on edges. Walk
  weight `wlen` coincides with CSLib's `Walk.wlength`, and `wdist` is CSLib's weighted distance.
* `G_{b,ℓ}` is built exactly as in the paper: in- and out-trees as heaps, and every `H`-edge of
  weight `w` becomes a path of `w − 2b − 2` edges. Coordinates are 0-indexed.
* A hub labeling (`SimpleGraph.IsHubLabeling`) asks for a common hub on a shortest path
  (`d(u,w) + d(w,v) = d(u,v)`) only for *reachable* pairs. This is the paper's definition on
  connected graphs and a weaker hypothesis in general, so the lower bounds are slightly stronger.
* Throughout, `b, ℓ ≥ 1`, as in the paper ("positive integers").

**Main results in Lean.** (namespace `Podc.HubLabelingHardness`)

| Paper | Lean | File |
|---|---|---|
| Lemma 2.2 for `H_{b,ℓ}` (unique shortest path, through `v_{ℓ,(x+z)/2}`, weight) | `lemma_2_2`, `lemma_2_2_H`, `wdist_eq_Lopt` | `HLemma.lean` |
| Lemma 2.2 for `G_{b,ℓ}` (distance = `H`-distance; every shortest walk through `v_{ℓ,(x+z)/2}`) | `lemma_2_2_G` | `Main.lean` |
| Theorem 2.1 (i), (ii), (iii) | `theorem_2_1` (parts: `card_ge`, `card_le`, `maxDegree_eq`, `pow_mul_card_le_sum`) | `Main.lean`, `Degree.lean` |
| Counting step of Thm 2.1 (iii): `Σ|S*_v| ≥ s^ℓ(s/2)^ℓ` | `card_triples_le_sum`, `SimpleGraph.IsHubLabeling.card_le_mul_sum` | `Main.lean`, `Podc/…/HubLabeling.lean` |
| Theorem 1.1 | `theorem_1_1` | `Main.lean` |
| Claim "`dist_G = dist_H` between levels" in the proof of Lemma 2.2: **false** | `dist_claim_false` | `Counterexample.lean` |

Supporting facts: `edist_main_le_wlen` (`d_G ≤ d_H` between vertices of `H`), `pot` and
`abs_pot_sub_le` (the potential), `refl_adj` (level reflection is a homomorphism),
`exists_mem_support_midLevel` (the cut at level `ℓ`), `lopt_le_length_and` (in `Distances.lean`).

**Not formalized.** Uniqueness of the shortest `v_{0,x}`–`v_{2ℓ,z}` path *in `G`*, which the paper
states and never uses; we prove the pass-through property and the distance. Not formalized either:
Section 3 (Theorem 1.6, the reduction from Sum-Index) and Section 4 (Theorems 4.1/1.4, the
Ruzsa–Szemerédi upper bound).

**Trust.** No `sorry`. `theorem_1_1`, `theorem_2_1`, `lemma_2_2_G`, `lemma_2_2` and
`dist_claim_false` use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The hub-labeling
definition and the counting lemma are staged in
`Podc/Foundations/Combinatorics/SimpleGraph/HubLabeling.lean` (CSLib candidate). Weighted distances
come from CSLib's `Cslib/Foundations/Combinatorics/SimpleGraph/WeightedSpanner.lean`.
