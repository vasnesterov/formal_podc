# The Impact of Cooperation in Bilateral Network Creation — PODC 2023

Tobias Friedrich, Hans Gawendowicz, Pascal Lenzner, Arthur Zahn. *The Impact of Cooperation in
Bilateral Network Creation.* PODC 2023. DOI
[10.1145/3583668.3594588](https://doi.org/10.1145/3583668.3594588). Formalized version: arXiv
[2207.03798](https://arxiv.org/abs/2207.03798) v2 (full version with appendix); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** Every statement we checked is true: Lemma 2.4, Lemma B.1,
Proposition 3.1, Corollary 3.2, Lemmas 3.3–3.5, Theorem 3.6 (trees in BSwE have
`ρ ≤ 2 + 2 log α`), and Propositions 3.8 and 3.9 (stretched binary trees give the matching
`Ω(log α)` lower bound for BGE). Two proofs need real repairs. The explicit `α`-range given in the
proof of Lemma 2.4 is wrong for odd `n`. One case of the proof of Lemma 3.5 rests on an invalid
inference. For Proposition 3.8 we give our own, shorter proof instead of Lemmas D.2–D.7.

## Mistakes in the paper

* **Lemma 2.4: the `α`-range in the proof is wrong for odd `n`; the lemma is true.** The proof says
  `C_n` is in BSE for `(n+1)(n-1)/4 - (n-1) < α < (n+1)(n-1)/4` when `n` is odd, citing [14] for
  Remove Equilibrium on this range. But an agent on `C_n` who drops one of its two edges saves `α`
  and loses only `n(n-1)/2 - (n²-1)/4 = (n-1)²/4` in distance. So for
  `(n-1)²/4 < α < (n²-1)/4` the cycle is not even in RE. Example: `C_5` with `α = 5`, inside the
  claimed range `(2, 6)`. The right end must be `(n-1)²/4`. With it, the range is still nonempty and
  of order `n²` (for even `n` the paper's range is correct), so Lemma 2.4 as stated, "for some range
  of `α ∈ Θ(n²)`", holds. The same proof also misstates `dist_{C_n}(u)` for odd `n` as
  `(n-1)(n-2)/4` instead of `(n²-1)/4`. Its path case assumes that "one of the end nodes must be part
  of the coalition", which is unjustified: the edge may have been dropped by the other endpoint. Our
  proof avoids this by counting distance levels: every coalition member of degree `≤ 1` in a path,
  and every member of degree 2, is not better off. (`C5_not_BSE`, `cycle_odd_not_BSE`,
  `cycle_not_RE`; corrected statement `cycle_BSE`, `lemma_2_4`)
* **Lemma 3.5: invalid case in the proof; statement true.** The proof starts with "if `α ≥ n/2`,
  the claim holds by definition of the 1-median `r`". But `|T_u| ≤ n/2 ≤ α` does not give
  `|T_u| ≤ α/(ℓ(u)-1)` once `ℓ(u) ≥ 3`. The case split is unnecessary: the swap argument of the
  main case (`u` swaps its parent edge for an edge to `r`) works for every `α`. (`lemma_3_5`)
* **Lemma 3.4: a step rests on an unproved characterization.** The proof uses "for all `w ∈ T_u`
  with `ℓ(w) ≥ ℓ(v)+1`, `|T_w| ≤ |T_u|/2`" for the `T_u`-1-median `v`. This follows from the
  "equivalent" component-size definition of 1-medians stated in Section 3.2, which the paper does
  not prove. We prove the step directly from minimality: otherwise moving from `v` towards `w`
  (to a child of `v`, or to its parent if `w ∉ T_v`) decreases the distance cost within `T_u`.
  Minor gap. (`two_mul_card_sub_le_of_subMedian`)
* **Typos and small slips.**
  * Proposition 3.9 says "for sufficiently large `η`". The paper's proof (with `k = ⌈α/η⌉`)
    needs a threshold that depends on `γ`; `η^γ ≥ 512` suffices (`prop_3_9`). The statement
    also holds with the `γ`-independent threshold `η ≥ 512` (`prop_3_9_uniform`): if
    `η^γ < 512`, the claimed bound is below `1 ≤ ρ`, and a complete binary tree of the right size
    is in BGE.
  * The definition of the Bilateral `k`-Strong Equilibrium must require a nonempty coalition;
    otherwise the empty coalition "improves" vacuously and no graph is in BSE.
  * With `M` only required to exceed `α n³`, disconnecting is not always worse when `α` is tiny
    (e.g. `n = 3`, `α = 0.01`, `M = 1`: an agent of the triangle drops both edges). This never
    matters under the paper's standing assumption `α ≥ 1`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`)
* A static, one-shot game; no distributed model and no randomness. Agents = vertices of a finite type
  `V`, `n = |V|`. A state is the created graph `G` (`SimpleGraph V`). The paper does the same: in
  equilibrium nobody pays for an edge that is not built.
* `cost(u) = α · deg(u) + ∑_v d(u,v)`, where `d` is the hop distance and `M` is the distance between
  disconnected agents. Theorems assume the paper's `α ≥ 1` and `M > α n³` (`M ∈ ℕ`).
* Solution concepts are exactly the paper's: RE (one agent drops one edge), BAE, PS, BSwE (`u`
  replaces `uv` by `uw`, and both `u` and `w` must strictly gain), BGE = PS ∧ BSwE, `k`-BSE
  (coalition moves: dropped edges touch `Γ`, added edges lie inside `Γ`), BSE = `n`-BSE.
* `log` is `log₂` (`Real.logb 2`), as is standard; Lemma 3.4, Theorem 3.6 and Proposition 3.9
  are stated with it.
* `ρ(G) = cost(G) / cost(OPT)`, where `cost(OPT)` is the infimum over all graphs on `V`. We prove
  `cost(OPT) = 2(n-1)(α+n-1)` for `α ≥ 1` (lower bound `socialCost_ge`, star `optCost_le_star`).
* Trees: layers and subtrees are metric, `T_u = {x | d(r,x) = d(r,u) + d(u,x)}`. A 1-median
  minimizes the distance cost (`IsMedian`, `IsSubMedian`). The `k`-stretched complete binary tree is
  an explicit graph on `Σ ℓ : Fin (dk+1), Fin 2^⌈ℓ/k⌉` (`stretchedTree d k`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.4 (corrected range) | `lemma_2_4`, `cycle_BSE` | `Cycle.lean` |
| Lemma 2.4, the proof's odd range fails | `cycle_odd_not_BSE`, `C5_not_BSE` | `Cycle.lean` |
| Prop. A.2 (the direction used: RE ⇒ no gain from dropping any set of edges) | `RE.cost_le_delAt` | `Removal.lean` |
| Lemma B.1 | `lemma_B1` | `Removal.lean` |
| Proposition 3.1 | `prop_3_1` | `Removal.lean` |
| Corollary 3.2 | `cor_3_2` | `Removal.lean` |
| Lemma 3.3 | `lemma_3_3` | `Trees.lean` |
| Lemma 3.4 | `lemma_3_4` | `Trees.lean` |
| Lemma 3.5 | `lemma_3_5` | `Trees.lean` |
| Theorem 3.6 | `theorem_3_6` | `Trees.lean` |
| Lemma D.4 (with `2kn` instead of `5kn`), Lemma D.7 | `add_gain` / `bae_of_layerSized`, `bswe_of_layerSized` | `LayerTree.lean` |
| Proposition 3.8 | `prop_3_8` | `Prop38.lean` |
| Lemma D.1 | `lemmaD1` | `Stretched.lean` |
| Lemma D.8 (parts used) | `exists_depth` | `Prop39.lean` |
| Proposition 3.9 (threshold `η^γ ≥ 512`; uniform threshold `η ≥ 512`) | `prop_3_9`, `prop_3_9_uniform` | `Prop39.lean` |

**How Proposition 3.8 is proved.** The stretched binary tree is *layer-sized*: `|T_x|` depends only
on the layer and halves every `k` layers (`LayerSized`). For such trees:
* A swap is beneficial for both agents only if `w` lies on `v`'s side `C_v` of the edge `uv`, `v`
  is strictly less central in `C_v` than `w`, and `|C_u| · d(v,w) > α`. This uses lower bounds on
  distances after the swap (`d_swap_ge`, `Cut.lean`).
* The potential `Φ_S(y) = ∑_{x∈S} d(y,x)` along root paths (`phi_eq`) shows that neither happens for
  `α ≥ 7kn`.
* For additions, a layer-cake argument bounds the gain of the shallower endpoint by `2kn`.

**Not formalized.** Section 2 apart from Lemma 2.4, Theorem 3.10 and Sections 3.2.3–3.3, and the
auxiliary Lemmas D.2, D.3, D.5, D.6 (our proof of Proposition 3.8 does not need them).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `prop_3_8` / `prop_3_9` exhibit trees in BGE (hence in BSwE, the
hypothesis of Lemmas 3.3–3.5 and Theorem 3.6), and `lemma_2_4` exhibits admissible `α` for every
`n ≥ 3`. Graph basics come from Mathlib (`SimpleGraph.dist`, `IsTree`, bridges) and CSLib
(`ShortestWalks.exists_dart_of_pred`, BFS parents).

**CSLib candidates** (marked `-- CSLib candidate` in the files):
* the metric rooted-tree API (`TreeMetric.lean`);
* distance lower bounds after adding or swapping an edge (`Cut.lean`);
* parent-function trees (`parGraph`, `IsParFun`, in `Stretched.lean`);
* the distance-level bound for graphs of maximum degree 2 (`Levels.lean`).
