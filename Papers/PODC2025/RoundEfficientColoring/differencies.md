# Differences between the formalization and the paper

Paper: Chang, Mishra, Nguyen, Salim, *Round and Communication Efficient Graph Coloring*, PODC 2025,
arXiv 2412.12589v2.

## Statement-level issues (verdict rules from `verdicts.md`)

1. **Lemma 5.3 is false for `Δ = 0`.** The lemma has no hypothesis `Δ ≥ 1`. With `Δ = 0` every vertex
   has degree 0, the degree-0 vertices are trivially independent, and no matching covers them: one
   isolated vertex is a counterexample (`lemma_5_3_false_of_zero`). Rule **R2** (degenerate: a
   parameter corner that Algorithm 2, with `Δ ≥ 8`, never uses) gives **⚠️**. This is the only
   statement-level issue, so it alone sets the verdict. It is a borderline call: by R6 the worst label
   wins, and R2 explicitly classifies a degenerate failure as ⚠️ rather than ✅. We prove `lemma_5_3`
   for `Δ ≥ 1` in a stronger form: only "maximum degree `≤ Δ`" is needed for an injective choice of
   neighbours (Hall). The independence hypothesis is used separately, to show the chosen edges are
   disjoint (`lemma_5_3_matching`, `Plan.M_unique`).

## Proof-level remarks (no effect on the verdict)

2. **Theorem 3, deferral.** "Sequentially identifies edges connecting two vertices of degree `Δ`" must
   use the current degree in the remaining graph. Then the deferred edges form a maximal matching
   between vertices of party-degree `Δ`, and a single colour of the other palette suffices. With the
   static reading the deferred edges need not be `Δ`-edge-colourable (Alice holds `K₃`, `Δ = 2`). We
   formalize the sequential reading, the same procedure as Algorithm 2 lines 3–5 with threshold `Δ`
   instead of `Δ − 1` (`exists_deferral`). The statement of Theorem 3 is true.
3. **Lemma 5.3, proof.** The paper uses integrality of the bipartite fractional matching polytope
   [Sch03]. We use Hall's theorem directly (double counting). Same content.
4. **Theorem 2, proof.** The proof says "for `Δ < 7` use Lemma 5.1, otherwise `Δ ≥ 8`", which misses
   `Δ = 7`. Our protocol uses Lemma 5.1 for every effective degree bound `≤ 7`.
5. **Lemma 5.2.** It says "the maximum degree of DG is 2" where "at most 2" is meant
   (`Plan.defer_le_two`).
6. **Lemma 6.2, proof.** The last display writes `E_A ∩ E_B ∩ E_1 ∩ E_2` for
   `E_A ∩ E_B ∩ E'_A ∩ E'_B` (typo, checked on the rendered PDF). In Case 1 our proof keeps one fixed
   Bob input, which gives the weaker loss bound `1/2205` instead of the paper's `1/105`. The paper's
   `1/105` is also correct, and both are `≥ 1/11025`, so the final bound is the paper's.

7. **Lemma 6.2, labels.** Case 2 uses `|L_A(v_i)| ≥ 2` for `v_i ∉ V_A`, which tacitly needs
   `L_A(v_i) ≠ ∅`. This holds because some input contains `v_i` and one of the 3 colours then has
   probability `≥ 1/3 ≥ 1/5` (`label_nonempty`). Routine.

## Modelling choices

8. **Degree bound.** Inputs satisfy "maximum degree `≤ Δ`" (`ValidInput`) instead of "maximum degree
   exactly `Δ`". This is more general, and all protocols work under it.
   - In Theorem 2 the protocol internally uses the effective bound `Δ' = min(Δ, n)`. It is a public
     parameter, valid because degrees are `< n`. With it, colour codes have `O(log n)` bits even when
     the given `Δ` is huge.
   - The colours used are `< 2Δ' − 1 ≤ 2Δ − 1`.
9. **Rounds.** The paper claims `O(1)` rounds; Lemma 5.5 is stated with two rounds and Lemma 5.4 with
   one. We prove Theorem 2 with **one** round of simultaneous messages. The information of Lemma 5.5
   (which of the first seven own colours are used at each vertex) and the cover data of Lemma 5.4
   depend only on the sender's own graph. So everything can be sent at once:
   - Lemma 5.4's cover is computed for all vertices of sender-degree `≤ Δ/2`, not only the "match
     vertices";
   - the receiver colours its deferred graph after reading the message.
10. **Communication model.**
   - A one-round protocol (`OneRoundProtocol`) has two message functions (`List Bool`) and two output
     functions. Each party's output depends on its own input and the received message. Cost is the
     total message length.
   - Variable-length messages could in principle carry information in their lengths. To exclude this,
     `theorem_2_tree` converts the protocol into a CSLib protocol tree. There each party sends one
     symbol from an alphabet of size `2^(L+1)`, where `L = 112 n` bounds its message length, and the
     cost is `≤ 224 n + 2`.
   - Bits are counted exactly. Constants: Algorithm 2 messages have `≤ 112 n` bits per party, the
     Lemma 5.1 message `13 n` bits.
11. **Encoding of Lemma 5.4.**
    - The paper sends the colours `c₁, …, c_t` and the bit arrays `V₁, …, V_t` (`|V_i| = |U_i|`).
    - We send `t` in unary, the colours in binary with `⌊log₂ n⌋ + 1` digits, and for every vertex `v`
      its level `ℓ(v)` in unary. Here `v` is first covered by `c_{ℓ(v)+1}`, and `ℓ(v) = 0` for
      vertices outside the cover set.
    - The total `Σ_v (ℓ(v) + 1) = n + Σ_{i ≥ 2} |U_i|` is the paper's `Σ |V_i|` up to `n`. Both are
      `≤ 3n`.
    - `t = O(log n)` is proved as `3^t ≤ 2^t · 3n` (`exists_greedy_cover`), and the colour list costs
      `(t + 1)(w + 1) ≤ 100 n` bits (`cover_bits_le`).
12. **Palettes.** Alice's palette is `{0, …, Δ−2}`, Bob's is `{Δ−1, …, 2Δ−3}`, and the special colour
    is `2Δ−2`. "The first seven colours of Bob's palette" are `Δ−1, …, Δ+5`. In Theorem 3 Alice's
    palette is `{0, …, Δ−1}`, Bob's is `{Δ, …, 2Δ−1}`, and the deferred matchings get colours `Δ`
    (Alice) and `0` (Bob).
13. **Local choices.**
    - Each party's local computations are made by choice, in Lean's classical logic: the deferral, the
      matching (Lemma 5.3), the Fournier colouring and the greedy cover form a `Plan`.
    - "Find a colouring by Proposition 3.5" is likewise existential in the paper.
    - The deferral is any terminal run of the sequential procedure (`exists_deferral`). Every such run
      has the properties used.
14. **Lemma 5.4 as stated.** The paper states it for Bob's vertices of degree `≤ Δ/2`, with Alice
    learning one available colour of Bob's palette for each.
    - We prove its content: the greedy cover exists with `Σ ℓ ≤ 2|U|` and `t = O(log n)`; the encoding
      has `O(n)` bits; and the cover colour is missing at `v` in Bob's colouring of `R \ M`
      (`Plan.cover`, used in `cross_R'_M`).
    - "Available" means not used by Bob's colouring of `R_B \ M_B`. These are exactly Bob's edges that
      use Bob's palette, which is what the correctness proof needs.
15. **ZEC game (Lemma 6.2).**
    - Alice's output is a full map `Fin 7 → Fin 3` (colour of `{v_A, v_i}` for every `i`); only the
      values on her input matter, so this is fully general.
    - A randomized private-coin strategy is a stochastic kernel per input. The joint law is the product
      of the inputs' uniform distributions and the two kernels.
16. **Edge colourings** are maps `Sym2 V → ℕ` with a bound `< k` on edges (`IsProperEdgeColoring`).
    `IsProperEdgeColoring.lineGraph_colorable` bridges them to Mathlib's `G.lineGraph.Colorable k`.
17. **Fournier's theorem** is proved in the strong form: maximum degree `≤ k` and no edge joining two
    vertices of degree `k` imply `k` colours suffice. With `k = Δ` this is Prop. 3.5; with
    `k = Δ + 1` it is Vizing (Prop. 3.4). The proof uses Vizing fans and Kempe chains, not Fournier's
    original argument.
18. **Lemma 5.1 scope.** The paper states it for any constant `Δ` (cost `O(n)` with a constant
    depending on `Δ`). We prove it for `Δ ≤ 7`, the only case Theorem 2 uses: Alice sends a fixed
    13-bit array per vertex (`13 n` bits). The general case is the same argument with
    `(2Δ − 1) n` bits.
19. **Lemma 5.3, form.** `lemma_5_3_matching` is the paper's statement (for `Δ ≥ 1`): a matching
    `M ≤ G` (every vertex has `≤ 1` `M`-neighbour) covering every vertex of degree `Δ`. It follows
    from `lemma_5_3`, an injective choice `f` of neighbours of the degree-`Δ` vertices, which needs
    only maximum degree `≤ Δ`; Algorithm 2 uses `lemma_5_3` directly.

## Not formalized

- Theorem 1 and all of Section 4 (randomized `(Δ+1)`-vertex colouring), Lemma 3.1, Prop. 3.2 (palette
  sparsification, an external result), Lemma 3.3.
- Lemma 6.1 (communication guessing, Newman's theorem), Prop. 6.3 (parallel repetition, external),
  Lemma 6.4, Theorem 4, Corollaries 1.1 and 1.2, Theorem 5 (ZEC-NEW, W-streaming).
