# Local Advice and Local Decompression — PODC 2024

Alkida Balliu, Sebastian Brandt, Fabian Kuhn, Krzysztof Nowicki, Dennis Olivetti, Eva Rotenberg,
Jukka Suomela. *Brief Announcement: Local Advice and Local Decompression.* PODC 2024. DOI
[10.1145/3662158.3662805](https://doi.org/10.1145/3662158.3662805). Formalized version: the full version
*Distributed Computation with Local Advice*, arXiv [2405.04519](https://arxiv.org/abs/2405.04519) v2
(22 Aug 2025); numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The 3-colouring result holds: every 3-colourable graph of
maximum degree `Δ` can be 3-coloured in `O(Δ⁹)` rounds with 1 bit of advice per node (Theorem 30).
Lemmas 31–34 hold, including the Lovász-Local-Lemma step of Lemma 32. Theorem 5 (advice algorithms can
be made order-invariant) also holds, but its proof ignores that LOCAL nodes know `n`; this needs a
repair. Two statement-level slips are minor: the cited Lemma 1 is false in the corner `d = 0`, and the
decoder's description has a typo.

## Mistakes in the paper

* **Theorem 5: the proof ignores the knowledge of `n` (proof gap; the statement is true).**
  The paper's LOCAL model (Section 3.1) gives every node `n`. The proof of Theorem 5 treats `A` as one
  map from labelled radius-`T` views to outputs, colours `s`-subsets of identifiers by that map, and
  takes an infinite monochromatic set `I`. Then it runs `A` on a graph `H` made of many copies of `G`,
  with `N ≫ n` nodes and `N` chosen *after* `I`. If `A` reads `n`, the behaviour on `H` is that of
  `A_N`, a different map, and `I` was built for the wrong one. The repair: for each `M`, apply finite
  Ramsey on `{1, …, N_M}` with `N_M = (R(M) + M)!` to `A_{N_M}`. That gives a homogeneous `M`-set whose
  behaviour is one of finitely many types. By pigeonhole one type `F*` occurs for infinitely many `M`.
  For a graph with `n` nodes take such an `M ≥ n + s`; then `n | N_M`, so `H` can be exactly
  `N_M / n` copies of `G`. The resulting `A'` does not even depend on `n`. (`theorem_5`)
* **Lemma 1 as stated is false for `d = 0` (degenerate case).** The paper states the symmetric local
  lemma with the condition `e·p·d ≤ 1`. One event of probability 1 depends on no other event and
  satisfies `e·1·0 ≤ 1`, yet it always occurs. The standard condition is `e·p·(d+1) ≤ 1`. The only use
  (Lemma 32, `d ≤ 48Δ⁸`, `p ≤ 1/(144Δ⁸)`) satisfies it as well. This is a cited textbook result.
  (`lemma_1_as_stated_false`; used instead: `Cslib.Probability.exists_forall_not_of_symmetric`)
* **Typos and small slips.**
  * The decoder (page 42) takes `x` as the smallest identifier "among all nodes in the
    `(30Δ³)`-hop neighborhood of `w` in `C(u)` that receive *color* 1". No node of `C(u)` has
    colour 1. It must be "receive *bit* 1", as the overview of Appendix D and the proof of Theorem 34
    show. The proof of Theorem 34 drops the qualifier altogether ("the smallest-ID node among all
    nodes in the neighborhood").
  * The existence of a greedy 3-colouring of a 3-colourable graph is used but not shown. It is easy:
    take a proper colouring with minimal colour sum (`exists_isGreedy`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *3-colouring (Theorems 30, 34; Lemmas 31–33).* Deterministic synchronous LOCAL with unique
  identifiers and no failures. The nodes of every graph are the elements of a fixed finite linearly
  ordered type `V`, and the order is the identifier order. An `R`-round algorithm is a function
  `SimpleGraph V → (V → Bool) → V → Fin 3` whose output at `u` depends only on the radius-`R` view of
  `u` (CSLib `Cslib.Local.IsLocal`: edges at nodes at distance `< R`, labels at distance `≤ R`). The
  advice is one bit per node, and the algorithm knows the degree bound `Δ`. The paper's colours
  `1, 2, 3` are `0, 1, 2`. Components of `G_{2,3}` and distances `dist_C` are those of the graph
  `H23 G φ` on `V`, where colour-1 nodes are isolated. Nodes in different components are at distance
  `⊤`, so the per-component ruling sets `R_C` merge into one set `R`.
* *Theorem 5.* Identifiers are natural numbers. An instance is a finite node set `Vs ⊆ ℕ`, a graph on
  `ℕ` with edges inside `Vs`, and node inputs from a finite alphabet. The algorithm
  `A : ℕ → SimpleGraph ℕ → (ℕ → In × (Fin β → Bool)) → ℕ → Out` gets the number of nodes `n` as
  first argument, and each `A n` is `T`-local. The paper's "identifiers in `{1,…,poly(n)}`" is
  abstracted as any admissibility predicate that accepts every `{1,…,N}`. "Component-wise defined"
  means: a valid solution restricts, along an isomorphism onto a union of components, to a valid
  solution. The graph family must be closed under disjoint unions of copies. The conclusion is
  stronger than the paper's: `A'` is order-invariant, does not know `n`, and works for arbitrary
  identifiers.
* *Randomness* appears only inside a proof (Lemma 32): the LLL on a uniform finite product space,
  where probabilities are counts.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 30 (1 bit of advice, `Δ^{O(1)}` rounds) | `theorem_30` (radius `8000Δ⁹ + 3`); `theorem_30_decode` (the same for the explicit decoder, uniform in `V`) | `Main.lean` |
| Lemma 31 | `lemma_31` (and the path version `exists_witness_on_path`) | `Lemma31.lean` |
| The encoding schema | `PreSchema`, `Schema`, `Schema.bit` | `Schema.lean` |
| Lemma 32 | `lemma_32` (`exists_preSchema`, `exists_sel`) | `Lemma32.lean`, `Lemma32LLL.lean` |
| Lemma 33 | `Schema.lemma_33` | `Schema.lean` |
| Algorithm `A` | `decode` | `Decoder.lean` |
| Theorem 34 | `theorem_34` (`Schema.decode_eq_psi`, `psi_proper`, `decode_isLocal`) | `Theorem34.lean`, `Decoder.lean` |
| Theorem 5 | `OrderInvariance.theorem_5` | `OrderInvariance.lean` (+ `OrderInvarianceAux.lean`) |
| Lemma 1 (as stated) | `lemma_1_as_stated_false` | `Lemma1.lean` |
| Lemma 1 (standard form) | `Cslib.Probability.exists_forall_not_of_symmetric` | `Podc/Probability/Finite/LocalLemma.lean` |

**Not formalized.** Appendices A, B, C and E: LCLs in sub-exponential growth graphs (Theorem 7),
balanced orientations and decompression, `Δ`-colouring, and composability (Lemmas 35–36). Also
Theorem 6 (ETH lower bound).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Theorem 30 is non-vacuous: the advice it uses comes from `lemma_32`, which builds the
whole schema (ruling set, `Q_r`, witnesses, paths, LLL selection) for every 3-colourable graph. The
locality notion is CSLib's `Cslib.Computability.Distributed.Local.Locality`. Finite hypergraph Ramsey
comes from `Podc/Foundations/Combinatorics/HypergraphRamsey.lean`. The Lovász Local Lemma was proved
here and staged in `Podc/Probability/Finite/LocalLemma.lean` (CSLib candidate).
