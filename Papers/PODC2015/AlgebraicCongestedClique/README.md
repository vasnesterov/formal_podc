# Algebraic Methods in the Congested Clique — PODC 2015

Keren Censor-Hillel, Petteri Kaski, Janne H. Korhonen, Christoph Lenzen, Ami Paz, Jukka Suomela.
*Algebraic Methods in the Congested Clique.* PODC 2015. DOI
[10.1145/2767386.2767414](https://doi.org/10.1145/2767386.2767414). Formalized version: arXiv
[1503.04963](https://arxiv.org/abs/1503.04963) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The checked results hold:
- Theorem 4: 4-cycle detection in `O(1)` rounds, with Lemmas 12 and 13;
- Theorem 1, semiring part: `O(n^{1/3})`-round matrix multiplication;
- Lemma 14 and the case split of Theorem 15.

Two statements are wrong as written, each with an evident fix. Step 1 of the 3D algorithm sends the
`T`-blocks to the wrong nodes (an index typo). Lemma 12 omits its hypothesis `∑ deg(y)² < 2n²`. The
proof of Lemma 12 also needs a small repair for degrees 1–3, and the final routing step of the
4-cycle algorithm needs an argument the paper does not give.

## Mistakes in the paper

* **Section 2.1, Step 1: the `T`-blocks go to the wrong nodes (typo; R3).** The paper says node `v`
  sends `T[v, w₃∗∗]` to every `w ∈ ∗v₂∗`, and that `v` receives `T[w, v₃∗∗]` from every
  `w ∈ ∗v₂∗`. But node `v` multiplies `S[v₁∗∗, v₂∗∗] T[v₂∗∗, v₃∗∗]`, so it needs the rows
  `w ∈ v₂∗∗` of `T`. As written, for `n^{1/3} ≥ 2` some needed row is never sent to `v`. The
  intended pattern is clear from "each node `v` receives … `T[v₂∗∗, v₃∗∗]`": `v` sends to
  `w ∈ ∗v₁∗` and receives from `w ∈ v₂∗∗`. We implement the corrected pattern.
  (`step1_as_written_wrong`, `step1_corrected`)
* **Lemma 12 omits its hypothesis (R4).** As stated, Lemma 12 claims disjoint tiles
  `A(y) × B(y) ⊆ V × V` with `|A(y)| ≥ deg(y)/8` for every graph. This fails for dense graphs: the
  tiles of the complete graph `K_n` would need total area at least `n(n−1)²/64 > n²` once
  `n ≥ 67`. The lemma is meant under
  the bound `∑_y deg(y)² < 2n²` derived just before it ("Using this bound, we obtain the following
  lemma"), and it is only used there. We state it with that hypothesis. (`lemma_12`)
* **Lemma 12, proof: `f(y)` is undefined for degrees 1–3 (proof gap).** `f(y)` is "`deg(y)/4`
  rounded down to the nearest power of 2". For `1 ≤ deg(y) ≤ 3` no positive integer power of two
  is `≤ deg(y)/4`. Yet `|A(y)| = f(y) ≥ deg(y)/8 > 0` must hold. With the natural fix `f(y) = 1`,
  the first step of the chain `∑ f(y)² ≤ ∑ deg(y)²/16 < n²/8 < k²` fails. The conclusion
  `∑ f(y)² ≤ k²` still holds: `16 f² ≤ deg² + 15` gives `16 ∑ f² < 2n² + 15n ≤ 16k²` for `n ≥ 3`,
  and `n ≤ 2` is direct. (`sixteen_mul_tileSize_sq_le`, `sum_tileSize_sq_le`)
* **4-cycle detection, last step: routing with `O(n)` loads (proof gap).** "Each node needs to send
  `O(n)` words and receive `O(n)` words, and the running time is therefore `O(1)` rounds" [46]. But
  Lenzen's routing (Theorem 3.7 of [46]) needs loads of at most `n`. Here a node sends up to `64n`
  walks and receives up to `2n − 2`. Splitting the instance needs coordination, because a node does
  not know the loads of the others. We add a deterministic reduction: one round of counts, one round
  of receiver-side offsets, then `a·b` Lenzen instances of load `≤ n` each, for send loads `≤ a·n`
  and receive loads `≤ b·n`. A referee may consider this folklore. (`Prog.exists_routedBig`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Network** (`Podc/Computability/Distributed/CongestedClique/Phases.lean`, shared). Synchronous
  congested clique on a finite node set with known identifiers. The algorithms are deterministic,
  with no failures and unbounded local computation. An algorithm is a `Prog`: a sequence of
  communication steps. In a step, every node computes from its own state a list of words for every
  node; every node then computes its new state from its old state and the received lists. So
  locality holds by construction.
* **Direct steps.** A direct step is sent over the links, one word per ordered pair per round. It
  costs the length of its longest list. This is the plain congested clique.
* **Routed steps.** A routed step has the same semantics. It requires every node to send and
  receive at most `n` words and costs 16 rounds. This is the black box of Lenzen's routing
  (PODC'13, Theorem 3.7), formalized separately in `Papers/PODC2013/CongestedCliqueRouting` for
  opaque messages but not composed with this model. Only the final step of the 4-cycle algorithm
  uses routed steps. The 3D algorithm uses direct steps only.
* **Words.** For 4-cycle detection a word is a triple of numbers `≤ 64n` (`O(log n)` bits). For
  matrix multiplication a word is one semiring element, as in the paper ("entries of `O(log n)`
  bits").
* **Inputs and outputs.** For 4-cycle detection, node `v` starts with `N(v)` of a simple undirected
  graph on `Fin n`, and every node must output whether a 4-cycle exists. For matrix multiplication,
  `n = q³` (the paper's assumption that `n^{1/3}` is an integer); node `v` starts with rows `S[v,∗]`
  and `T[v,∗]` and must output row `(ST)[v,∗]`, over any (even non-associative, non-unital)
  semiring.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4 (4-cycle detection in `O(1)` rounds; here `≤ 2069` rounds) | `theorem_4` | `FourCycleAlg.lean` |
| Lemma 12 (disjoint tiles; Morton-order packing) | `lemma_12`, `tiles_disjoint`, `card_tileA` | `Tiles.lean` |
| Lemma 13 (`W(b)` partition `P(∗,∗,∗)`, `\|W(b)\| ≤ 64n`) | `lemma_13` | `FourCycle.lean` |
| 4-cycle criterion, Phase 1 test, `∑ deg² = ∑_x \|P(x,∗,∗)\|` | `hasFourCycle_iff`, `exists_of_card_walksFrom`, `sum_degree_sq`, `sum_degree_sq_lt` | `FourCycle.lean` |
| Theorem 1, semiring part (`O(n^{1/3})`; here `≤ 6 n^{1/3}` rounds) | `theorem_1_semiring` | `MatMul.lean` |
| Step 1 typo of Section 2.1 | `step1_as_written_wrong`, `step1_corrected` | `MatMul.lean` |
| Oblivious routing ([24, Lemma 1], used by Theorem 1) | `Prog.exists_oblivious` | `Podc/.../CongestedClique/Oblivious.lean` |
| Routing `O(n)` loads with Lenzen's algorithm (used by Theorem 4) | `Prog.exists_routedBig` | `Podc/.../CongestedClique/Routing.lean` |
| Lemma 14 (girth vs. edges) | `lemma_14`, `lemma_14_of_le` | `Girth.lean` |
| Theorem 15, case split for `ρ > 0`, `ℓ = ⌈2 + 2/ρ⌉` | `theorem_15_dense`, `theorem_15_sparse` | `Girth.lean` |

**Not formalized.**
- Fast (ring) matrix multiplication: Lemma 10, the second part of Theorem 1, `ρ`.
- Corollary 2, Theorem 3 (colour coding), Lemma 11, Corollaries 6–8, Theorem 9, Section 3.4, and
  the lower bounds of Section 4.
- Theorem 15 as an algorithm: it needs Theorem 3. Only its combinatorial core is checked, and the
  `ρ = 0` case is not covered.

**Trust.** No `sorry`. `theorem_4`, `theorem_1_semiring`, `lemma_12`, `lemma_13`, `lemma_14`,
`theorem_15_dense`, `Prog.exists_oblivious` and `Prog.exists_routedBig` use only the axioms
`propext`, `Classical.choice`, `Quot.sound`. Theorems 4 and 1 are existential statements about
explicit programs (`fourCycleProg`, built from the paper's steps). Their conclusions are exact
input/output specifications, so no hypothesis can be vacuous. The tiles of Lemma 12 are computed
explicitly by a Morton-order packing, not chosen.

Shared code staged in `Podc/Computability/Distributed/CongestedClique/` (CSLib candidates):
- `Phases.lean`: the `Prog` model;
- `Oblivious.lean`: oblivious routing via König's theorem;
- `Routing.lean`: Lenzen routing with `O(n)` loads.

Further CSLib candidates, marked in `Tiles.lean`: the Morton bijection and the packing of
power-of-two squares.
