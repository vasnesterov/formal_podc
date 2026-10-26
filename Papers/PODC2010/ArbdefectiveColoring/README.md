# Arbdefective colourings — PODC 2010

Leonid Barenboim, Michael Elkin. *Deterministic Distributed Vertex Coloring in Polylogarithmic
Time.* PODC 2010. DOI [10.1145/1835698.1835797](https://doi.org/10.1145/1835698.1835797).
Formalized version: arXiv [1003.1608](https://arxiv.org/abs/1003.1608) v1; numbering follows it.

**Verdict: 🛠️ Proof repaired.** Sections 3 and 4 hold. This covers Lemma 3.1, Theorems 3.2
and 3.5, Corollaries 3.4 and 3.6, Lemmas 4.1 and 4.2, Theorem 4.3 and Corollary 4.4, all with
explicit constants. Lemma 2.1 (Kuhn's defective colouring) is a black-box hypothesis, and so is the
`(Δ+1)`-colouring of [BE09] for Lemma 4.1. The proof of Corollary 4.4 has a gap: its case split
on `a` is wrong. The corollary is still true, and we prove it with a corrected three-way split.

## Mistakes in the paper

* **Corollary 4.4: wrong case split in the proof; the statement is true.** For "superlogarithmic"
  `a` the paper runs Legal-Coloring with `p = ⌊a^{μ'}/log n⌋`, `μ' = μ/2`. It claims that
  `p > a^{μ'/2}` "since `a` is superlogarithmic", which would bound the number of iterations by a
  constant. This needs `a^{μ'/2} > log n`, i.e. `a > (log n)^{2/μ'}`. Counterexample: take
  `a = (log₂ n)²` (superlogarithmic) and any `μ' ≤ 1/2`. Then `p ≤ 1 < a^{μ'/2}` for every `n ≥ 4`
  (`p = 0` if `μ' < 1/2`). With `p = 1`, line 15 gives `α ↦ ⌊(3+ε)α⌋ ≥ α`, so the while-loop never
  ends. So the second case is only valid for `a > (log n)^{2/μ'}`, not for all superlogarithmic
  `a`. The `a` below this threshold are polylogarithmic, and the paper's remark before the
  corollary (Theorem 4.3 for polylogarithmic `a`) can handle them, but only if the threshold is made
  explicit and Theorem 4.3 is used with a smaller exponent (`μ'' = μ²/4`). This is a proof gap
  (a wrongly stated case condition), not a false statement. We prove the corollary with three cases:
  (1) `p₁ = ⌊a^{μ/2}/ℓ⌋ ≥ 16` and `(3+ε)a^{μ/4} ≤ p₁`, where `ℓ = ⌊log₂ n⌋+1`: Legal-Coloring with
  `p₁`, `O(a^μ + log n)` rounds;
  (2) otherwise `a^{μ/4} ≤ 5ℓ`: Theorem 4.3 with `μ²/4`, `O(ℓ^{1+μ})` rounds;
  (3) `a` bounded by a constant: Lemma 2.2(1).
  (`corollary_4_4_proof_gap`, `line15_one`; repaired: `corollary_4_4`)
* **Implicit parameter choices (minor).** Theorem 3.5 needs an `⌊a/t⌋`-defective colouring of the
  H-sets. These have maximum degree `⌊(2+ε)a⌋`, not `a`, so Lemma 2.1 must be called with
  parameter `≈ (2+ε)t`; we use `3t` (valid for `ε ≤ 1`). Algorithm 2 calls Arbdefective-Coloring on
  subgraphs whose arboricity is only bounded by `α`. The H-partition and the defect must use the
  bound `α`, not the unknown exact arboricity (line 2 `α := a(G₁)` must be a known upper bound).
  The final step of Theorem 4.3 needs only `O(p² log n) = O(a^μ log n)` rounds. So the legal
  colouring of Lemma 2.1 (`q = Δ+1`) suffices there, and the `(Δ+1)`-colouring of [BE09] is not
  needed for Theorem 4.3.
* **Typos.** Theorem 4.3 states `p = ⌈a^{μ/2}⌉`, while the text and the proof use `⌊a^{μ/2}⌋`. In
  the proof of Theorem 3.2, "for each parent `w` of `u`, `len(u) ≤ i−1`" should be `len(w)`.
  Theorem 5.3 says "`O(a/t)`-coloring" for `O(a·t)` (Section 5 is not formalized).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic synchronous LOCAL model, no failures. The vertices of every graph are the elements
  of a fixed finite type `V`, which serve as the identifiers. All vertices know `n = |V|`, the
  arboricity bound `a` and the parameters (`ε`, `μ`, `k`, `t`, `p`).
* Round complexity is CSLib's locality `IsLocal R f`: the output of `v` depends only on the edges
  at distance `< R` and the inputs at distance `≤ R`. This is exactly what `R` LOCAL rounds
  compute. Each algorithm is a fixed function of `(G, inputs)`, local for *all* graphs, and correct
  on the graphs of arboricity `≤ a`.
* Simple-Arbdefective and the greedy colouring are implemented operationally in CSLib's
  locally-iterative round model (vertex states with identifier, parents and colour). Their locality
  comes from `run_isLocal`. The H-partition is local by a direct induction. Procedures are composed
  with `IsLocal.comp` (radii add up). "For each subgraph `Gᵢ` in parallel" runs the procedure on
  `classGraph G c`, which keeps only the edges inside the colour classes. This costs no extra
  rounds (`isLocal_classGraph`).
* Black boxes, as `DefectiveAlg V Δ d K R`: an `R`-round algorithm computing a `d`-defective
  colouring with colours `< K` on every graph of maximum degree `≤ Δ`.
  - Lemma 2.1 [Kuhn]: `Lemma21 V C R`, i.e. `⌊Δ/q⌋`-defective with `< Cq²` colours.
  - The `(Δ+1)`-colouring of [BE09], only for Lemma 4.1: `DeltaPlusOne V C' R'`.

  The paper takes `R = O(log* n)`; our bounds are explicit in `R`. Both hypotheses are
  satisfiable. CSLib's Linial colouring is also packaged as a `DefectiveAlg`.
* Arboricity is CSLib's `ArboricityLE` (edges covered by `α` forests). Lemma 2.5 is CSLib's
  `OutOrientation.arboricityLE_of_rank`. The H-partition only uses an orientation of out-degree
  `≤ a`, so it also works for pseudo-arboricity.
* Partial orientations are parent sets `par v ⊆ N(v)`. Length means the number of edges on directed
  walks, which equals the paper's paths for acyclic orientations. Colours are `0, …, k-1`.

**Main results in Lean** (namespace `Podc.ArbdefectiveColoring`).

| Paper | Lean | File |
|---|---|---|
| Def. 2.1 (per colour class) | `IsArbdefective`, `IsArbdefective.induce` | `Basic.lean` |
| Lemma 2.3 (H-partition, `L = ⌈2/ε⌉(⌊log₂n⌋+1)` rounds) | `hPartition`, `hIdx_isLocal`, `hRounds_ok` | `HPartition.lean`, `Parameters.lean` |
| Lemma 3.1 | `exists_complete_extension` | `Extension.lean` |
| Theorem 3.2 | `simpleArbdefective`, `simpleArb_isLocal` (combinatorial core `isArbdefective_of_parents`) | `AlongOrientation.lean`, `Extension.lean` |
| Lemma 3.3 / Lemma 2.4 | `completeOrientation_spec`, `partialOrientation_isLocal` | `PartialOrientation.lean` |
| Lemma 2.2(1) | `legalColoring_spec`, `legalCol_isLocal`; unconditional (Linial) `legalColoring_linial` | `PartialOrientation.lean`, `LinialBridge.lean` |
| Corollary 3.4 | `corollary_3_4` | `Parameters.lean` |
| Theorem 3.5 | `partialOrientation_spec`, `partialOrientation_isLocal` | `PartialOrientation.lean` |
| Corollary 3.6 | `corollary_3_6` (general form `arbdefectiveColoring_spec`) | `Parameters.lean`, `PartialOrientation.lean` |
| Lemma 4.1 | `lemma_4_1` | `Lemma41.lean` |
| Algorithm 2, Lemma 4.2(1) | `LCParams.proc`, `LCParams.lab_spec`, `LCParams.proc_correct`, `LCParams.proc_isLocal` | `Recursive.lean` |
| Lemma 4.2(2), (3); line 15 | `iters_lt`, `bound_mul_pow_le`, `next_le` | `Theorem43.lean` |
| Theorem 4.3 | `theorem_4_3` (general `p`: `legalColoring_general`) | `Theorem43.lean` |
| Corollary 4.4 | `corollary_4_4`; gap: `corollary_4_4_proof_gap`, `line15_one` | `Corollary44.lean` |
| Lemma A.2 | `exists_legal_of_complete_of_lengthLE` | `Extension.lean` |

Explicit bounds:
* Theorem 4.3, for `0 < ε ≤ 1/2`, `μ > 0` and `p = ⌊a^{μ/2}⌋ ≥ 16`:
  fewer than `(3+ε)^{4/μ+1}·a` colours, in at most `(4/μ+1)(L(9C·a^μ+2)+R)` rounds.
* Lemma 4.1: fewer than `((2+ε)(3+ε)+1)a` colours, in at most
  `(9C+25)L·a^{2/3} + 25C'a^{2/3} + R + R' + 4L` rounds.
* Corollary 4.4: constants `c₁, c₂, c₃` depending only on `ε, μ, C`, with time
  `c₁(a^μ + ℓ^{1+μ}) + c₂R` and fewer than `c₃·a` colours.

**Not formalized.** Lemma 2.1 and the [BE09] colouring (black boxes), Lemma 2.2(2) (forest
decomposition), Theorem 4.5, Corollaries 4.6 and 4.7, Section 5 (Arb-Kuhn, Theorems 5.2 and 5.3)
and Appendix B.

**Trust.** No `sorry`. The theorems in the table use only the axioms `propext`, `Classical.choice`
and `Quot.sound`. Non-vacuity:
* `Lemma21.satisfiable` (`NonVacuity.lean`) instantiates the Lemma 2.1 hypothesis with `C = 1` and
  `n` rounds. Each vertex learns its component and outputs a canonical defective colouring, which
  exists by Lovász's lemma (`exists_defective`, proved).
* `DeltaPlusOne.satisfiable` does the same for the [BE09] hypothesis.
* `linialAlg` is a genuine `O(log* n)` black box: CSLib's Linial algorithm.

CSLib modules used: `SimpleGraph/Arboricity`, `Local/Locality`, `Local/LocallyIterative`,
`Local/Identifiers`, `Local/Linial`.

CSLib candidates (marked in the code):
* `isLocal_classGraph`, `isLocal_one_nbr`, `IsLocal.map/prod`, `isLocal_self` (`LocalTools.lean`);
* `arboricityLE_mono`;
* the H-partition (`Active`, `hIdx`, `hPartition`, `sum_card_adj_le`);
* height functions and completion of partial orientations (`Basic.lean`, `Extension.lean`);
* Lovász's `exists_defective`.
