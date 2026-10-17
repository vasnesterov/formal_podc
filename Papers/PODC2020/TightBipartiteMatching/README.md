# Truly Tight-in-Δ Bounds for Bipartite Maximal Matching — PODC 2020

Sebastian Brandt, Dennis Olivetti. *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants.*
PODC 2020. DOI [10.1145/3382734.3405745](https://doi.org/10.1145/3382734.3405745). Formalized version: arXiv
[2002.08216](https://arxiv.org/abs/2002.08216) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The main result holds. In the deterministic port-numbering model on
2-coloured `Δ`-regular trees, bipartite `x`-maximal `y`-matching (the encoded version `Φ^W_Δ(x, y)`) has white
round complexity exactly `T_Δ(x, y)` for `0 ≤ x ≤ Δ`, `1 ≤ y ≤ Δ − 1`; in particular it is `2Δ − 1` for maximal
matching. We prove both bounds, and the round elimination step they use. The tightness claim of Theorem 1.2
and §6 is false in the degenerate case `y = Δ`. Several proofs needed small repairs: empty sets in `R_B`, an
ill-defined problem in Lemma 4.3, and two errors in the output rule of the algorithm.

## Mistakes in the paper

* **Theorem 1.2 / end of §6: tightness fails for `y = Δ` (false only in a degenerate case).** The paper claims
  tightness "for any combination of integers `x ≥ 0, y ≥ 1, Δ ≥ 2`". For `y = Δ` and `x < Δ` the formula gives
  `T_Δ(x, Δ) = 1`. But matching every edge is a valid solution, so 0 rounds suffice. The paper itself notes
  the trivial algorithm after Theorem 4.5. (`theorem_1_2_false_y_eq_Δ`)
* **Lemma 4.1–4.3 proofs ignore the empty set (proof gap, statements true).** `R_B(Π)` uses labels from
  `2^Σ`, which includes `∅`. A configuration such as `(∅, MZPOX, …, MZPOX)` is vacuously universal and
  maximal. For `a ≤ Δ − 2` it extends to none of the three configurations listed in the proof of Lemma 4.1. The
  lemmas survive because `∅` never appears in a correct solution. We use nonempty sets throughout.
  (`emptyConf_counterexample`)
* **Lemma 4.3 produces `Ψ^W_Δ(y, x, 0)`, which is undefined for `x > Δ − y` (under-specified).** The family
  requires `a + b ≤ Δ`. We prove the lemma with `Ψ^W_Δ(y, min{x, Δ − y}, 0)`. Theorem 4.5 is unaffected,
  since it only uses the lemma when `x < Δ − y`. (`lemma_4_3`)
* **§5, the algorithm's output rule is wrong as literally written (proof error, bound true).** The text hints
  at both fixes, but the stated rule fails on small cycles.
  * White nodes must accept proposals received in the last round. Without this, an unmatched black node
    that proposed in the last round may see more than `x` labels `X`. Example: `Δ = 2`, `x = y = 1`
    (2 rounds) on an 8-cycle, where a black node gets `X` from both neighbours.
  * In the `2⌈(Δ−x)/y⌉ − 1`-round variant, unmatched whites must output `P` on all ports, not only where
    they proposed. Whites are active only `k − 1` times there. Example: BMM with `Δ = 2` (3 rounds) on a
    6-cycle, where an unmatched white node outputs `P X`, which violates `x = 0`.

  With these fixes the bound holds on all `Δ`-regular properly 2-coloured port-numbered graphs. (`upper_bound`)
* **Theorem 4.5 has small gaps.**
  * Its parameter formulas break down when `⌈(Δ−x)/y⌉ = 1`. That case needs `Φ^W` and `Φ'` to be not
    0-round solvable, which is asserted without proof.
  * The caps `min{c + a, Δ − a}` of Lemma 4.1 are ignored. They are inactive.

  We prove both points. (`phi_not_zero`, `phi'_not_zero`, `seqBC_le`)
* **Typos.**
  * Theorem 2.1 says "complexity `min{0, T − 1}`"; it should be `max`.
  * The proof of Lemma 4.1 says the universal quantifier is applied to the *white* constraint; it should be
    the black one.
  * "Δ-regular balanced trees" is imprecise: finite trees have leaves, while the problems are defined for
    `Δ`-regular graphs (§2 uses regular graphs of girth `≥ 4Δ + 2`). We use the infinite 2-coloured
    `Δ`-regular tree.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic port-numbering model, no identifiers, no randomness. Graphs are `Δ`-regular and properly
  2-coloured, and the colour is a node's only input. White algorithms: white nodes label their ports, and the
  black constraint is checked on the labels written by the white neighbours, as in §2.2.
* **View model** (`Views.lean`). A `t`-round algorithm is a function of the radius-`t` view, an inductive type
  of port-numbered rooted trees. `Solves A Act Pas` means correctness on every port numbering of the infinite
  2-coloured `Δ`-regular tree.
* **CSLib model** (`Bridge.lean`). For CSLib message-passing algorithms (`Cslib.PortNumbering.Algorithm`):
  * in every `Δ`-regular 2-coloured port-numbered graph, the state of a node after `t` rounds is a function
    of its view (`state_eq`);
  * every view is realized at the root of an explicit port-numbered infinite tree `treeGraph d arr`.

  So the lower bound applies to genuine algorithms on these trees (`theorem_4_5_PN`).
* Not covered: the paper's finite graphs of girth `≥ 4Δ + 2`, where algorithms may know `n`. The transfer from
  trees to such graphs is standard but not formalized.
* `Δ = d + 1` in Lean. Problems are transcribed literally as unions of condensed configurations (`Cond.Gens`).
  The round elimination theorem (forward direction, bipartite form) is proved from scratch. It needs no edge
  symmetry breaking, unlike the converse (cf. `Papers/PODC2019/AutomaticSpeedup`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1.2 (deterministic PN, `1 ≤ y < Δ`, `x ≤ Δ`) | `theorem_1_2` | `Main.lean` |
| Theorem 1.2 false for `y = Δ` | `theorem_1_2_false_y_eq_Δ` | `Degenerate.lean` |
| Theorem 2.1 (forward direction) | `theorem_2_1`, `theorem_2_1_dual`, `re_forward` | `RoundElim.lean` |
| Relaxations (Lemma 2.4 et al., combined) | `Relax`, `relax_of_meaning` | `RoundElim.lean` |
| `Φ^W_Δ(x, y)`, `Φ'(x, y)`, `Ψ^W_Δ(a, b, c)`, `T_Δ(x, y)` | `Phi`, `Phi'`, `Psi`, `Tval` | `Problems.lean` |
| Lemma 4.1 | `lemma_4_1` | `Relaxations.lean` |
| Lemma 4.2 | `lemma_4_2` | `Relaxations.lean` |
| Lemma 4.3 (with `min{x, Δ − y}`) | `lemma_4_3` | `Relaxations.lean` |
| `∅` gap in the proofs of Lemmas 4.1–4.3 | `emptyConf_counterexample` | `EmptySet.lean` |
| Lemma 4.4; 0-round hardness of `Φ`, `Φ'` | `lemma_4_4`, `phi_not_zero`, `phi'_not_zero` | `LowerBound.lean` |
| Theorem 4.5 (view model / CSLib algorithms) | `theorem_4_5`, `theorem_4_5_PN` | `LowerBound.lean`, `Main.lean` |
| §5 upper bound (CSLib algorithm, all `Δ`-regular 2-coloured PN graphs) | `upper_bound` | `UpperBound*.lean` |
| Views ↔ CSLib algorithms, realizing trees | `state_eq`, `viewOf_treeGraph_root`, `solves_of_solvesOn_trees` | `Bridge.lean` |

**Not formalized.**
* Theorems 1.3 and 1.4 (randomized and LOCAL lower bounds). They rely on the cited randomized round elimination
  lemma (Lemma 6.1, [1, Lemma 41]) and on ID-generation and gap arguments.
* The transfer to finite high-girth graphs.
* The 1-round equivalence between the encoded and the natural matching problem (Definition 1.1).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
* Non-vacuity: `upper_bound` exhibits an algorithm, so `theorem_1_2` is not vacuous.
* The realizing trees are explicit and simple (`treeGraph_isSimple`).
* The port-numbering model comes from CSLib (`Cslib/Computability/Distributed/PortNumbering/Basic.lean`).

CSLib candidates (marked `-- CSLib candidate` where applicable):
* the bipartite round elimination core: `Views.lean`, `RoundElim.lean`, condensed configurations in
  `Config.lean`;
* the view/CSLib bridge `Bridge.lean`;
* `exists_split` (`UpperBoundLabels.lean`).
