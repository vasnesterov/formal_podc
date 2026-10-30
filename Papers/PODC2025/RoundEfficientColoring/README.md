# Round and Communication Efficient Graph Coloring — PODC 2025

Yi-Jun Chang, Gopinath Mishra, Hung Thuan Nguyen, Farrel D. Salim. *Round and Communication Efficient
Graph Coloring.* PODC 2025. DOI [10.1145/3732772.3733508](https://doi.org/10.1145/3732772.3733508).
Formalized version: arXiv [2412.12589](https://arxiv.org/abs/2412.12589) v2 (9 May 2025); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The edge-colouring results we checked hold. Theorem 2 is the
deterministic `(2Δ−1)`-edge colouring with `O(n)` bits and `O(1)` rounds; we even get it in a single
round. Theorem 3 is `2Δ` colours without communication, and Lemma 6.2 is the ZEC game bound
`11024/11025`. Fournier's theorem (Prop. 3.5) and Vizing's theorem (Prop. 3.4) are proved too. The only
statement that is wrong as written is Lemma 5.3, and only in the degenerate case `Δ = 0`.

## Mistakes in the paper

* **Lemma 5.3 fails for `Δ = 0`.** Lemma 5.3 claims that in a graph of maximum degree `Δ` whose
  degree-`Δ` vertices are independent, some matching covers all degree-`Δ` vertices. A single
  isolated vertex is a counterexample with `Δ = 0`. The case is degenerate, since Algorithm 2 uses the
  lemma only for `Δ ≥ 8`. For `Δ ≥ 1` the lemma holds. Hall's theorem gives every degree-`Δ` vertex
  its own neighbour using only "maximum degree `≤ Δ`". The independence hypothesis then makes the
  chosen edges pairwise disjoint. (`lemma_5_3_false_of_zero`; repaired version `lemma_5_3_matching`)
* **Theorem 3, ambiguous step.** The proof says each party "sequentially identifies edges connecting
  two vertices of degree `Δ` and colors them using any color from the other party's palette". This
  is correct only if *degree* means the current degree in the remaining graph. Then the deferred
  edges form a maximal matching and one colour of the other palette suffices. If it means the
  degree in the party's graph, all such edges are deferred at once and they need not be colourable
  with `Δ` colours: take Alice holding a triangle with `Δ = 2`. We formalized the sequential reading
  (`exists_deferral`), the one Algorithm 2 uses. The theorem is true.
* Typos and slips:
  - Proof of Theorem 2: "for `Δ < 7` apply Lemma 5.1 … otherwise, for `Δ ≥ 8`" leaves out `Δ = 7`.
    Lemma 5.1 covers it.
  - Lemma 5.2 says "the maximum degree of DG is 2" where "at most 2" is meant.
  - Proof of Lemma 6.2, last display: `E_A ∩ E_B ∩ E_1 ∩ E_2` should be `E_A ∩ E_B ∩ E'_A ∩ E'_B`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Two-party, edge-partition model (Section 3.1). The vertex set (`Fin n` for the protocols), `n` and
  `Δ` are public. Alice holds `A : SimpleGraph V`, Bob holds `B`, with `Disjoint A B`, and
  `G = A ⊔ B` has maximum degree `≤ Δ` (`ValidInput`). This is more general than the paper's
  "maximum degree exactly `Δ`". Each party outputs colours for its own edges. The outputs are correct
  if the combined colouring is a proper edge colouring with colours `< k` (`SolvesEdgeColoring`).
  Colourings are maps `Sym2 V → ℕ`.
- Deterministic protocols, no randomness. Zero communication (Theorem 3): each output is a function of
  that party's own edge set. One round (Theorem 2): a `OneRoundProtocol` where both parties
  simultaneously send a bit string and then output (the paper's footnote 1 convention). Cost is the
  total number of bits.
- Message lengths cannot hide information: `theorem_2_tree` restates Theorem 2 as a protocol tree of
  CSLib's `Cslib.CommunicationComplexity.Protocol`, where each message is one symbol of a fixed
  alphabet. Its cost is `≤ 224 n + 2`.
- ZEC game (Lemma 6.2): private-coin randomized strategies are stochastic kernels, one per input.
  Inputs are independent and uniform over the 21 pairs. The winning probability is an explicit
  finite sum.

**Main results in Lean** (namespace `Podc.RoundEfficientColoring` unless noted).

| Paper | Lean | File |
|---|---|---|
| Prop. 3.5 (Fournier) | `SimpleGraph.exists_isProperEdgeColoring_of_ncard_le`, `…_maxDegree` | `Podc/…/EdgeColoring/Vizing.lean` |
| Prop. 3.4 (Vizing) | `SimpleGraph.exists_isProperEdgeColoring_maxDegree_add_one` | `Podc/…/EdgeColoring/Vizing.lean` |
| Theorem 3 | `theorem_3` | `ZeroComm.lean` |
| Lemma 5.1 (for `Δ ≤ 7`, the only case used) | `lemma_5_1`, `lemma51Protocol_costLE` (`13n` bits, one round) | `Theorem2.lean` |
| Lemma 5.2 (deferral, `deg DG ≤ 2`) | `exists_deferral`, `Plan.defer_le_two` (via `exists_plan`) | `Model.lean`, `Plan.lean` |
| Lemma 5.3 (`Δ ≥ 1`) / false for `Δ = 0` | `lemma_5_3_matching` (paper's form), `lemma_5_3` (injective neighbour choice, no independence needed) / `lemma_5_3_false_of_zero` | `Matching.lean` |
| Lemma 5.4 | `exists_greedy_cover`, `cover_bits_le`, `length_encInfo_le`, `cross_R'_M` | `SetCover.lean`, `Theorem2.lean`, `Algorithm2.lean` |
| Lemma 5.5 | `Plan.three_le_card_dlist`, `Plan.dcol_spec` | `Algorithm2.lean` |
| Algorithm 2 correctness | `color_proper`, `cross`, `alg2Protocol_correct` | `Algorithm2.lean`, `Theorem2.lean` |
| Theorem 2 | `theorem_2` (`≤ 224 n` bits, 1 round), `theorem_2_tree` | `Theorem2.lean` |
| Lemma 6.2 | `lemma_6_2` | `ZEC.lean` |
| Sec. 2.3, deterministic hard instance (`2Δ − 1 = 3` colours need communication, `Δ = 2`) | `exists_losing_input` | `ZEC.lean` |

**Not formalized.** Theorem 1 and Section 4 (randomized `(Δ+1)`-vertex colouring, palette
sparsification). Theorem 4 and Corollaries 1.1, 1.2, Theorem 5: they need Newman's theorem and the
parallel repetition theorem (Raz/Holenstein). Lemma 6.1.

**Trust.** No `sorry`. `theorem_2`, `theorem_2_tree`, `theorem_3`, `lemma_5_1`, `lemma_5_3_matching` and `lemma_6_2` use only the axioms
`propext`, `Classical.choice` and `Quot.sound`, and so do Fournier's and Vizing's theorems. Non-vacuity:
`theorem_2` and `theorem_3` quantify over all valid inputs and construct the protocols, so they are not
vacuous. `winProb_pos_example` shows that the ZEC winning probability can be positive.

Infrastructure, staged in `Podc/` as CSLib candidates:
- `Podc/Foundations/Combinatorics/SimpleGraph/EdgeColoring/Basic.lean`: edge colourings, missing
  colours, greedy list edge colouring.
- `…/EdgeColoring/Vizing.lean`: Kempe swaps, Vizing fans, Fournier, Vizing, line-graph colourability.
- `Podc/Computability/CommunicationComplexity/OneRound.lean`: one-round simultaneous-message protocols
  and the bridge to CSLib protocol trees.
