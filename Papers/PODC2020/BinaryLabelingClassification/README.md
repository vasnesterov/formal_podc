# Classification of distributed binary labeling problems — PODC 2020

Alkida Balliu, Sebastian Brandt, Yuval Efron, Juho Hirvonen, Yannic Maus, Dennis Olivetti, Jukka Suomela.
*Brief Announcement: Classification of Distributed Binary Labeling Problems.* PODC 2020. DOI
[10.1145/3382734.3405703](https://doi.org/10.1145/3382734.3405703). Formalized version: the full version
arXiv [1911.13294](https://arxiv.org/abs/1911.13294) v3 (48 pages); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** Everything we checked holds as stated:
- Observation 3.2 (the four equivalent problems);
- Theorems 8.1–8.3 (families V and VI have deterministic complexity `Θ(n)`), proved for every number of nodes;
- Lemma 10.4 (every problem not of type I–IV relaxes to a forbidden-degree or bipartite sinkless-orientation problem);
- Lemmas 10.8–10.9 (FDSO(s) is a fixed point of round elimination).

Two steps in the §8 proofs need small repairs. In the proof of Theorem 8.3 an orientation goes the wrong way. In the
proof of Theorem 8.2 an intermediate claim is false for general trees, though it holds for the instances the proof uses.

## Mistakes in the paper

- **Proof of Theorem 8.3: the orientation goes the wrong way (proof slip, statement true).** The hardest VI.b problem
  is `W = 010⁺`, `B = 0⁺10`. With the paper's convention (an `X`-edge points from black to white), every relevant node
  must have exactly one incoming edge. The paper roots the tree at a leaf and orients all edges *towards* it. Then a
  non-root node of degree `k` has `k − 1` incoming edges, which violates the constraints for `k ≥ 3`. Orienting
  *away* from the leaf works: every non-root node has one incoming edge, and the leaf root is irrelevant. The same
  slip appears in the sentence "it is always possible to orient a tree towards a root" about the Theorem 8.2
  problem. (`viHard_exists`, `theorem_8_3`)
- **Proof of Theorem 8.2: "at most a single vertex has all edges outgoing" is false for general trees (proof
  imprecision, statement true).** Only relevant nodes (white degree `d`, black degree `δ`) must have at most one
  incoming edge. Nodes of other degrees can absorb several incoming edges, so in a general tree many nodes can be
  sources. The paper then calls the problem equivalent to the "oriented tree problem"; that equivalence also fails
  in general. The claim does hold on the instances the reduction actually uses: a path whose nodes are all relevant,
  with leaves attached. Our proof runs the paper's mirroring argument directly on those caterpillars and never uses
  the general claim. (`dirR_mono`, `Caterpillar.viEasy_lower`)
- **Minor slips.**
  - Theorem 8.1, upper bound: the proof only treats subdivided `d`-regular trees ("it is sufficient that V.a is
    solvable on any `d`-regular tree"). On a general bipartite tree, black nodes of degree `≠ 2` are not edges of an
    underlying tree. A solution still always exists: root the tree at a node of degree `≤ 1` and use the parity of
    `⌊dist(r, u)/2⌋` at white nodes `u` (`va_exists`).
  - Proof of Lemma 10.4, case `1010`: the case `B = 0⁺` (type II.b) is not mentioned; the lemma's hypothesis excludes it.
  - Proof of Lemma 10.8 (2): "configurations consisting of `δ` labels" (and `Z₁ … Z_δ`) should read `d`.
  - Proof of Lemma 10.9, items (1)–(2): "black" and "white" (and `d`, `δ`) are swapped in the description of the
    output problem; the proof itself uses the right constraints.
  - The `Ω(n)` arguments of §8 build a caterpillar with `n ≡ 1 (mod d)` nodes, and do not say how to obtain other
    values of `n`. We pad with extra leaves at one end, so the bounds hold for every `n`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Problems and solutions.** A binary labeling problem is `Π = (d, δ, W, B)` with `d, δ ≥ 2`, `W ⊆ [0, d]`, `B ⊆ [0, δ]`.
  An instance is a finite tree `G` with a proper 2-colouring `f` (white/black). A solution is an edge labelling,
  symmetric on edges. White nodes of degree exactly `d` must have `X`-degree in `W`; black nodes of degree exactly
  `δ` must have `X`-degree in `B`. All other nodes are unconstrained (§3.1, §3.6).
- **Computation.** Deterministic, synchronous, fault-free LOCAL with unique identifiers. The nodes of every
  instance are the elements of a fixed finite type `V`, so `n = |V|` is known, and node names serve as identifiers.
  A `T`-round algorithm is a function of the radius-`T` view (CSLib's `Cslib.Local.IsLocal`: edges at distance
  `< T`, inputs at distance `≤ T`). The colour is a local input. A `T`-round message-passing algorithm is
  `(T + 1)`-local in this sense (it also learns the degrees at distance `T`), which only shifts the constants.
- **White and black algorithms.** In a *white* algorithm every edge gets the label written by its white endpoint;
  a *black* algorithm is symmetric (§5). `WhiteSolvable Π V T` means some `T`-round white algorithm solves `Π` on
  every tree on `V` with every proper 2-colouring.
- **No port numbers.** With identifiers, port numbers can be derived from the IDs. For the lower bounds, assuming
  them absent is without loss of generality: an algorithm correct for all port numberings is correct for the
  ID-induced one.
- **Identifiers.** The identifiers are exactly the `n` nodes rather than a `poly(n)` range. This only restricts the
  instances, so the lower bounds become stronger. The upper bounds gather the whole tree in `n` rounds.
- **Randomized results.** §10.3–10.4 and §11 are not formalized. Lemmas 10.8–10.9 are the purely combinatorial
  round-elimination step: output problems, maximal configurations, renaming.

**Main results in Lean** (namespace `Podc.BinaryLabeling`).

| Paper | Lean | File |
|---|---|---|
| Observation 3.2 (solutions) | `isSolution_compl_iff`, `isSolution_swap_iff` | `Basic.lean` |
| Observation 3.2 (complexities: `Π₁₀` same `T`, `Π₀₁` within `T + 1`) | `observation_3_2_compl`, `observation_3_2_swap` | `Basic.lean` |
| Observations 3.4, 5.1, 5.2 | `IsSolution.of_restriction`, `WhiteSolvable.of_restriction`, `observation_5_1`, `white_to_black`, `black_to_white` | `Basic.lean`, `Global.lean` |
| Theorem 8.1 (V.a, V.b: `Θ(n)`; `n` rounds suffice, `T` rounds need `n < (3T+6)d` resp. `(3T+9)δ`) | `theorem_8_1` | `Global.lean` |
| Theorem 8.2 (VI.a, VI.b: `T` rounds need `n < (6T+10)(d+δ−2)`) | `theorem_8_2` | `Global.lean` |
| Theorem 8.3 (VI.a, VI.b: `n` rounds suffice) | `theorem_8_3`, `theorem_8_2_8_3` | `Existence.lean`, `Global.lean` |
| "every solvable problem is solvable in `O(n)` rounds" | `whiteSolvable_card` | `Existence.lean` |
| Lemma 10.4 | `lemma_10_4` | `Coverage.lean` |
| Lemma 10.8 | `RoundElim.lemma_10_8_black`, `RoundElim.lemma_10_8_white` | `RoundElim.lean` |
| Lemma 10.9 | `RoundElim.lemma_10_9_white`, `RoundElim.lemma_10_9_black` | `RoundElim.lean` |
| FDSO(s) is a fixed point (§10.6) | `RoundElim.fdso_fixedPoint` | `RoundElim.lean` |

**How the lower bounds are proved.**
- **Instances.** `Caterpillar.lean` builds the caterpillar: a spine `w₀ b₀ w₁ b₁ …` of relevant nodes with hairs,
  plus padding. It is a tree via parent pointers (`Podc/Foundations/Combinatorics/SimpleGraph/ParentGraph.lean`).
- **Mirrored copies.** A mirrored copy is the caterpillar relabelled along the permutation that reverses a spine
  segment, `graph.comap σ`. It is a tree by isomorphism, and it agrees with the caterpillar at every node except
  the four segment-boundary nodes (`adj_mirror`).
- **Same views.** A 1-Lipschitz "spine position" potential (`natAbs_le_edist`) shows that nodes far from the
  boundary see identical radius-`T` views in both trees.
- **Theorem 8.1** uses the parity of the alternating labels (`va_alternate`).
- **Theorem 8.2** uses the paper's two-case mirroring argument with monotone edge directions (`dirR_mono`).
- **Transfer to `V`.** `WhiteSolvable.of_equiv` moves the result to an arbitrary `V` with the same number of nodes.

**Not formalized.**
- Sections 6–7 (types I–IV), the `O(log n)` algorithms of §9, Lemmas 10.5, 10.7, 10.10, Theorem 10.11 and
  Corollary 10.12 (local failure probability, the `Ω(log log n)` randomized bound, the gap theorem of [12]), and §11.
- Lemma 10.4 is proved assuming only "not of type II, III or IV"; type I is not needed.

**Trust.** No `sorry`; `theorem_8_1`, `theorem_8_2_8_3`, `lemma_10_4` and `RoundElim.fdso_fixedPoint` use only the
axioms `propext`, `Classical.choice`, `Quot.sound`. Non-vacuity: the upper bounds show that the lower-bound hypotheses
are satisfiable for `T = n`, and `Global.lean` exhibits members of V.a and VI.b. The locality model is CSLib's
`Cslib/Computability/Distributed/Local/Locality.lean`.

CSLib candidates (marked `-- CSLib candidate`):
- `edist_map_hom_le`, `edist_comap_equiv`, `natAbs_le_edist` (`Transport.lean`);
- tree parent facts `IsTree.exists_adj_dist_add_one`, `IsTree.eq_of_adj_dist_add_one`, `IsTree.parentSet_eq`,
  `IsTree.childSet_eq` (`Existence.lean`).
