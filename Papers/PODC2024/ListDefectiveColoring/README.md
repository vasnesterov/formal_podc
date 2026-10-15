# List defective colouring — PODC 2024

Marc Fuchs, Fabian Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective Coloring
Algorithms.* PODC 2024 (brief announcement). DOI
[10.1145/3662158.3662808](https://doi.org/10.1145/3662158.3662808). Formalized version: full version, arXiv
[2405.04648](https://arxiv.org/abs/2405.04648) v1.

**Verdict: ⚠️ Correct with fixes.** The main algorithmic result (Two-Sweep, Theorem 1.1) and Theorem 1.4 are
proved, and no stated theorem is refuted. But the Section 4.1 algorithm as literally defined colours no node
(a floor/ceiling slip in eq. (10)), the construction in the proof of Lemma 4.5 has a gap, and the proof of
Lemma A.1 is wrong. All three are repaired.

## Mistakes in the paper

1. **Eq. (10) breaks the Section 4.1 algorithm (definition error).** The modified defect is
   `d'_v(x) = ⌊(d_v(x)+1)/(7θ)⌋ − 1`, claimed non-negative with `∑(d'+1) ≥ (1/7θ)∑(d+1)` (eq. (11)). Whenever
   `d_v(x) < 7θ − 1` we get `d' = −1`; then no colour ever satisfies condition (12), every list `L_{v,i}` and
   every `H_i` is empty, and no node is ever coloured. This covers every colour with small defect, in particular
   all of proper list colouring (`d ≡ 0`), so it is not a corner case. Concrete instance: the triangle, `θ = 1`,
   `S = 1`, `d ≡ 0`, 85 colours per list; it satisfies the paper's slack hypothesis, yet the algorithm terminates
   with nobody coloured and `∑(d'+1) = 0 < 85/7`. With the ceiling, `d' = ⌈(d+1)/(7θ)⌉ − 1 = ⌊d/(7θ)⌋`,
   Theorem 1.4 holds as stated (`Sec41.theorem_1_4_paper_defects_false`; fix `Sec41.theorem_1_4`).
2. **Lemma A.1, proof error (statement about existence unaffected).** The proof claims
   `deg(v) − deg~(v) ≥ Δ − Δ/2 ≥ µ·deg_{G_i}(v)`, but the first step fails for nodes of degree `< Δ`. In a
   15-node instance with `Δ = 6`, `µ = 2`, `ε = 1/4`, a node of degree 4 with 3 coloured neighbours and one
   neighbour in its class ends with residual weight exactly `µ·deg_{G_i}(v)`, so its sub-instance lacks slack `µ`.
   It still has slack 1, so what breaks is the round-complexity argument, not existence. Fix: compare `deg~(v)`
   with half of the node's own residual degree and take the defective colouring on the residual graph; per-node
   residual degrees then halve each phase (`SlackReduction.paperA1_counterexample`; fix `lemmaA1`).
3. **Lemma 4.5, gap in the construction (trivial fix).** Every node is offered all `p` colour subspaces, so it may
   pick one disjoint from its list (nothing forbids it when no neighbour picks the same subspace) and is left with
   an empty list. Smallest case: one isolated node, `L = {0}`, two subspaces. Offering only subspaces that meet
   `L_v` repairs it; the slack bound survives because `L_v ≠ ∅` (`ColorSpace.paper_counterexample`; fix `lemma45`).
4. **Smaller proof gaps (statements true).**
   - Lemma 3.1, case `|L_v| > p`: the final pigeonhole bounds the wrong right-hand side (all of `L_v` instead of
     `S_v`). Averaging the *difference* of the two sides of (4) over all `p`-subsets works and also proves the
     Remark that Algorithm 1's sorted choice satisfies (4).
   - Lemma 3.2: the displayed inequality is garbled; the step is a pigeonhole on sums against (6).
   - Section 4.1: the setup of Lemma 4.2 states `deg~(v,i) ≤ ∑_x a_v(x,i)`, but the proof needs (and the truth is)
     the reverse; eq. (9) omits the factor `deg(v)`; Lemma 4.3 can be sharpened to `X_v ≤ 4θ d'`, so the constant
     7 could be 4.
   - Round counts (not formalized, noted only): as written, Theorem 1.2's argument gives
     `O(log³C + log C · log* q)` rather than `O(log³C + log* q)`, and Lemma A.1 recomputes Lemma 3.4 in every
     phase; Theorem 1.5's arithmetic gives `log⁷Δ` where `log⁸Δ` is stated (only weaker).
   - Typos/conventions: "let `ε > 0` be an integer" (`ε` is real); Theorems 1.1/1.2 say "`β_v` is the outdegree"
     while Section 2 defines `β_v = max(1, outdeg)` (we use the latter).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Any `SimpleGraph V`; out-neighbourhoods are arbitrary sets `out v ⊆ N(v)` (an orientation is a special case;
  `out v = N(v)` gives plain list defective colouring). The initial `q`-colouring need only be proper along
  out-edges. This is more general than the paper.
- Section 3: synchronous, deterministic, fault-free LOCAL rounds (CSLib's `Cslib.LocallyIterative.Algorithm`: a
  node's new state depends on the round, its state and the *set* of neighbour states); states carry IDs, lists
  and defects. Two-Sweep runs in exactly `2q` rounds. CONGEST message sizes are not modelled.
- Algorithm 1's "sort and take the first `p`" is modelled as any best `p`-subset; the sorted prefix is shown to be
  one, so every tie-breaking is covered.
- Section 4.1 and Lemmas 4.4, 4.5, A.1 are specification-level: the arbdefective subroutine is replaced by its
  output specification and all its outputs are quantified over; Lemma 3.4's defective colouring (cited by the
  paper) is a hypothesis. `Δ ≥ 2` per the paper's Section 2 convention.

**Main results in Lean** (namespace `FK24`).

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (+ Remark), Lemma 3.2 | `lemma_3_1`, `exists_phaseII_color` | `SubsetSelection.lean`, `TwoSweep.lean` |
| Lemma 3.3 = Theorem 1.1 (`ε = 0`) | `twoSweep_correct`, `twoSweep_correct_of_isProper` | `Distributed.lean` |
| Theorem 1.1 (`ε > 0`, Algorithm 2) | `fastTwoSweep_correct` | `FastTwoSweep.lean` |
| Section 1.1 corollaries | `twoSweep_listColoring`, `twoSweep_threeColoring` | `Distributed.lean` |
| Theorem 1.2 (arithmetic only) | `theorem12_slack` | `Theorem12.lean` |
| Claim 4.1, Lemmas 4.2, 4.3 | `claim_4_1`, `Sec41.lemma_4_2`, `Sec41.lemma_4_3_sharp` | `NeighborhoodIndependence.lean`, `Section41.lean` |
| Theorem 1.4 (corrected `d'`) | `Sec41.theorem_1_4`, `Sec41.theorem_1_4_paper_slack` | `Section41.lean` |
| Eq. (10) counterexample | `Sec41.theorem_1_4_paper_defects_false` | `Section41Counterexample.lean` |
| Lemma 4.4; Lemma 4.5 (fixed) | `lemma44`; `lemma45` | `SlackReduction.lean`, `ColorSpaceReduction.lean` |
| Lemma A.1 (fixed) and counterexample | `lemmaA1`, `SlackReduction.paperA1_counterexample` | `SlackReduction.lean` |

**Not formalized.** The cited black boxes (Lemma 3.4, Lemma 3.5, [FK23a] Thm. 4), hence Theorems 1.2/1.3 beyond
their arithmetic, Theorem 1.5 and Lemma 4.6 (`O`-recursions), and all round/message-size bounds that go through
them.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: Section 4.1 runs exist (`Sec41.exists_isRun`, via a greedy list-arbdefective colouring;
`Sec41.theorem_1_4_exists`), and the eq. (10) counterexample comes with an explicit run.
