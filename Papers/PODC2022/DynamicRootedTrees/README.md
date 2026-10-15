# Broadcasting Time in Dynamic Rooted Trees is Linear (PODC 2022)

Antoine El-Hayek, Monika Henzinger, Stefan Schmid. *Brief Announcement: Broadcasting Time in Dynamic Rooted
Trees is Linear.* PODC 2022, pp. 54–56, DOI [10.1145/3519270.3538460](https://doi.org/10.1145/3519270.3538460),
arXiv:2211.11352 (the arXiv version is also only the 5-page brief announcement).
The proofs are in the full version: *Asymptotically Tight Bounds on the Time Complexity of Broadcast and its
Variants in Dynamic Networks*, ITCS 2023, arXiv:2211.10151v2 (Sections 1–3, Appendix A.1–A.2). Both PDFs are in
`src_pdf/` (don't commit them). The lower bound is due to Zeiner, Schwarz, Schmid (DAM 255, 2019), reproduced as
Figure 5 of the full version.

## Model

- `n` processes `Fin n`; synchronous rounds `t = 1, 2, …`; in each round an **oblivious message adversary**
  chooses a communication graph from `𝒯ₙ` = rooted (out-)trees on `Fin n` with a self-loop at every node
  (`treesWithLoops n`, `RootedTree`). No failures, no randomness; deterministic full-information flooding
  (each process forwards all ids it has heard of).
- Information flow = product of the relations: `G₁ ∘ ⋯ ∘ Gₜ` (`Cslib.DynNet.prod G 1 t`, Mathlib `Relation.Comp`).
- Broadcast after round `t`: `∃ x, ∀ y, (x, y) ∈ G₁ ∘ ⋯ ∘ Gₜ` (`Cslib.DynNet.Broadcasts`); broadcast time of a
  sequence `t*(G₁, G₂, …)` (`broadcastTime`, a `sInf`) and of the adversary `t*(𝒯ₙ)` (`advBroadcastTime`, a `⨆`).

## Main results ↔ Lean

| Paper | Lean (namespace `DynamicRootedTrees` unless noted) | File |
|---|---|---|
| BA Thm 3.1: `⌈(3n−1)/2⌉−2 ≤ t*(𝒯ₙ) ≤ ⌈(1+√2)n−1⌉` | `theorem_3_1` | `Main.lean` |
| FV Thm 3.6: `t*(𝒯ₙ) ≤ ⌈(1+√2)n⌉` | `theorem_3_6` | `Main.lean` |
| FV Thm 3.7 (Zeiner et al. lower bound) | `theorem_3_7`; construction `lbSeq`, `lbSeq_mem`, `lbSeq_not_broadcasts` | `Main.lean`, `LowerBound.lean` |
| upper bound per sequence | `broadcasts_trees` | `Main.lean` |
| generalization: any rooted rounds with self-loops | `broadcasts_of_rooted` | `Main.lean` |
| sharper bound `m + n − 1` if `2(n−1)² < m(m+1)` (new) | `advBroadcastTime_trees_le_of_sq_lt`, `broadcasts_of_sq_lt` | `Main.lean`, `UpperBound.lean` |
| FV Def 1.1/1.3/1.4 (product, `t*`) | `Cslib.DynNet.prod`, `Cslib.DynNet.broadcastTime`, `Cslib.DynNet.advBroadcastTime` | `Cslib/Computability/Distributed/DynamicNetworks/Product.lean` |
| FV Def 1.2 (`𝒯ₙ`) | `treesWithLoops`, `RootedTree.adj`, `RootedTree.isRoot` | `Defs.lean` |
| FV Def 2.1/2.2 (`I_t^{t'}`, `O_t^{t'}`) | `Cslib.DynNet.inNbhd`, `Cslib.DynNet.outNbhd` | `Cslib/Computability/Distributed/DynamicNetworks/Product.lean` |
| FV Lemma 2.3 | `Cslib.DynNet.mem_outNbhd_iff_mem_inNbhd` | ″ |
| FV Lemma 2.4 (i)(ii)(iii) | `Cslib.DynNet.outNbhd_trans`, `outNbhd_trans_of_mem_inNbhd`, `outNbhd_trans_of_mem_inNbhd_of_mem_inNbhd` (+ `inNbhd_trans`) | ″ |
| FV Lemma 2.5 (i)(ii) | `Cslib.DynNet.inNbhd_mono`, `Cslib.DynNet.outNbhd_mono` | ″ |
| FV Def 3.1 (root of round) | hypothesis `hr : ∀ t, IsRoot (G t) (r t)` | `UpperBound.lean` |
| FV Lemma 3.2 (i), (ii) | `Cslib.DynNet.card_inNbhd_lt_of_root_notMem`, `Cslib.DynNet.card_outNbhd_lt_of_root_mem` | `Cslib/Computability/Distributed/DynamicNetworks/Product.lean` |
| FV Lemma 3.3 | `lemma_3_3` | `UpperBound.lean` |
| FV Def 3.4 (rounds graph) | `roundsGraph`, `RoundsAdj`, `outdeg` (parameters `m`, `R`) | `UpperBound.lean` |
| FV Lemma 3.5 | `lemma_3_5` (paper parameters); generic `exists_outdeg_ge` | `Main.lean`, `UpperBound.lean` |
| FV Thm 3.6 proof (generic) | `broadcasts_of_sum_min`, `min_card_le_card_outNbhd` | `UpperBound.lean` |
| small-n exact values `t*(𝒯ₙ) = 0,1,2,4` for `n = 1..4` (kernel-verified exhaustive search) | `advBroadcastTime_trees_one/two/three/four`; framework `FrontierSearch` (`frontier_sound`, `advBroadcastTime_le_of_frontier`, `le_advBroadcastTime_of_seq`) | `Small.lean` |

All listed theorems: no `sorry`; `#print axioms` = `propext, Classical.choice, Quot.sound`.

## Status

**Complete.** Upper bound (both the BA's `⌈(1+√2)n−1⌉` and FV's `⌈(1+√2)n⌉`), every supporting lemma of FV
Section 2–3.1, and the lower bound `⌈(3n−1)/2⌉−2` for all `n` are formalized.

Findings (details in `differencies.md`):
- The BA claims `⌈(1+√2)n − 1⌉` but the FV proof only gives `⌈(1+√2)n⌉`; the BA's sharper claim is true (slack
  in the pigeonhole of Lemma 3.5) and is proved here. With optimized parameters the same proof gives
  `m + n − 1` with `m` minimal s.t. `m(m+1) > 2(n−1)²` (≈ `(1+√2)(n−1)`).
- The proof needs only self-loops + a root per round, not trees (`broadcasts_of_rooted`).
- Minor gaps: Lemma 3.3 used outside its stated range (`t₁ = t₂ + 1`), typos in Lemma 3.5. No real errors.
- Exhaustive search: `t*(𝒯ₙ) = 0,1,2,4,5,7` for `n = 1..6` (n ≤ 4 kernel-verified in `Small.lean`; n = 5 Python,
  n = 6 C search modulo relabeling, unverified) = the lower bound `⌈(3n−1)/2⌉−2` for `n ≥ 2`; the upper bound
  (`2, 4, 7, 9, 12, 14`) is far from tight for small `n`.

## CSLib candidates

- `Cslib/Computability/Distributed/DynamicNetworks/Product.lean` (migrated to CSLib, namespace `Cslib.DynNet`): dynamic networks as relation sequences, products (`Relation.Comp`),
  generalized neighbourhoods, monotonicity, rooted rounds (`IsRoot`, `exists_edge_cross`, strict growth lemmas),
  broadcast time of sequences/adversaries (`advBroadcastTime_le`, `le_advBroadcastTime`).
- `RootedTree`/`RootedTree.ofRank` (`Defs.lean`, `LowerBound.lean`) if a parent-function tree API is wanted.

## Files

- `Defs.lean` — rooted trees with loops, `𝒯ₙ`.
- `UpperBound.lean` — Lemma 3.3, rounds graph, generic Lemma 3.5 / Theorem 3.6, sharpened bound.
- `LowerBound.lean` — Zeiner–Schwarz–Schmid construction, `lbSeq_not_broadcasts` (all `n ≥ 2`).
- `Main.lean` — paper-parameter Lemma 3.5, Theorems 3.6, 3.7, 3.1.
- `Small.lean` — kernel-verified exhaustive checks for small `n`.

## Token spend

Roughly 0.55M tokens in total (paper agent ≈ 0.3M, lower-bound subagent ≈ 0.09M, small-n subagent ≈ 0.15M).
