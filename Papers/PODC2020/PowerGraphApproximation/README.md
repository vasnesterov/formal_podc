# Distributed Approximation on Power Graphs — PODC 2020

Reuven Bar-Yehuda, Keren Censor-Hillel, Yannic Maus, Shreyas Pai, Sriram V. Pemmaraju. *Distributed
Approximation on Power Graphs.* PODC 2020. DOI
[10.1145/3382734.3405750](https://doi.org/10.1145/3382734.3405750). Formalized version: arXiv
[2006.03746](https://arxiv.org/abs/2006.03746) v1; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** Every checked statement is true. That covers the centralized 5/3-approximation for
`G²`-MVC (Theorem 12, Lemmas 13–16), Lemma 6, the combinatorial core of the `(1+ε)`-approximation (Theorem 1,
Lemmas 2–5), Corollary 17, and the `Ω̃(n²)` CONGEST lower bounds for exact `G²`-MWVC and `G²`-MVC (Theorems 20 and 22,
Lemmas 21, 23, 24, with the [CKP17] family lemma proved from scratch). Two proofs need repairs. The proof of
Corollary 17 applies Theorem 12 to a graph that is not a square, and Algorithm 2 really is only a 2-approximation
there. The proof of Lemma 6 claims a strict inequality that is false.

## Mistakes in the paper

* **Corollary 17's proof misapplies Theorem 12; the corollary is true.** The proof runs Phase I of Algorithm 1 with
  `ε = 1/2` and then says the leader "locally uses Theorem 12 to compute a 5/3-approximation for the remaining
  graph" `G²[U]`. Theorem 12 only covers squares `G²`. `G²[U]` is just an induced subgraph of a square, and every
  graph is one. The proof of Theorem 12 also breaks there: Lemma 13 (3) needs the `G`-midpoint of every blue edge
  to lie in `V1`, but now the midpoint can lie in `S`. Concrete run: take vertices `a₀..a₃`, `b₀..b₃` and midpoints
  `wᵢⱼ ~ aᵢ, bⱼ`. Phase I picks `a₀, …, a₃` and ends with `U = {aᵢ, bⱼ}` and `G²[U] = K₄,₄`. That graph is
  triangle-free and 4-regular, so Algorithm 2 goes straight to part 3. Part 3 may output all 8 vertices (both ends
  of a perfect matching), while 4 vertices suffice (`corollary_17_proof_gap`). The overall 5/3 bound still holds,
  with a different accounting. A midpoint in `S` has at most two neighbours in the triangle-free remainder, so it
  pays for at most one blue edge, just like a triangle vertex. Lemma 5 charges `S` at ratio `3/2`, the same as part 1
  charges triangles. So Lemma 14 (4) becomes `s₁ + |S| ≥ (3/2)|V_{R'}|` and the 5/3 computation goes through
  (`induced_bound`, `corollary_17`).
* **Lemma 6's proof claims `|I| < n/α`; only `|I| ≤ n/α` holds.** Take the path `0–1–2–3` with `r = 2`. Then
  `I = {0, 3}` is independent in `G²` and `|I| = 2 = n/α`. The non-strict bound follows from the paper's own
  argument and is all the lemma needs, so the statement holds (`lemma_6_strict_false`, `card_mul_le_of_indep`,
  `lemma_6`). Its second sentence (the `(1 + 1/⌊r/2⌋)`-approximation) needs `r ≥ 2`; for `r = 1` it divides by 0.
* **Small slips in proofs** (all statements true):
  - Theorem 12, degree-3 case: the three disjoint edges are `{y₁,z₁}, {y₂,z₂}, {x,y₃}`, not `{x,y₂}`.
  - In the degree-2 case, the edges `{z,y₁}` and `{x,y₂}` are disjoint only because `z ≠ y₂`. This holds because
    the graph is triangle-free, which the paper does not say.
  - Lemma 5 writes `Sᵢ = N(vᵢ) ∩ R` for `N(cᵢ) ∩ R`.
  - The distributed description of Phase I calls vertices with "at least `1/ε`" neighbours in `R` candidates;
    the pseudocode, Lemma 2 and Lemma 5 need "more than `1/ε`".
  - Theorem 1, case `ε > 1`: "a `G²`-MIS has at most `n/2` vertices" fails for `n = 1`.
  - Theorems 20 and 22: `V_B = V(G) \ V_B` should be `\ V_A`.
  - The order of the 4-cycle in the [CKP17] bit gadgets is not specified. We use `t_A – f_A – t_B – f_B`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Graphs are finite `SimpleGraph`s. `G.power r` joins distinct vertices at `G`-distance `≤ r`
  (`Podc/Foundations/Combinatorics/SimpleGraph/Power.lean`). Vertex covers are Mathlib's `IsVertexCover` or a
  `Finset` covering `G²[X]`.
* **Centralized algorithms (Algorithms 1 and 2)** are nondeterministic transition systems (`Step`). Each choice the
  pseudocode leaves open is a nondeterministic choice, and the theorems hold for *every* complete run. Algorithm 2
  stores only `V'`, since `E' = G²[V']` throughout, as the paper proves. Degree-0 vertices may be removed at any
  time in parts 1–2 (the paper removes them eagerly). Part 3 is "any 2-approximate cover". Existence of runs comes
  from `exists_step`/`exists_run`: the existence claims of lines 9–10 hold, and part 3 can use a maximal matching.
  "Polynomial time" is formalized as an `n + 3` bound on the number of steps, each step being a polynomial-time
  check.
* Theorem 1 (CONGEST, `O(n/ε)` rounds) is formalized only in its sequential semantics with `ε = 1/l`: correctness
  and approximation, Lemma 3, and the facts behind the round count. These are: at most `l` neighbours in `U` per
  vertex, hence `|F| ≤ ln`, and at most `n/(l+1)` Phase-I iterations. BFS pipelining and ID symmetry breaking are
  not modelled.
* **Lower bounds** use CSLib's deterministic synchronous CONGEST model with `B`-bit messages and families of
  lower-bound graphs (`Cslib/Computability/Distributed/Congest/`). Nodes know their IDs and neighbourhoods, plus
  their weight for Theorem 20. "Computes MVC of `G²`" is formalized, as in [CKP17]/Theorem 19, as *deciding* the
  threshold predicate "`H²` has a cover of size (weight) `≤ W'`". The deterministic bound is unconditional, because
  CSLib proves `CC(DISJ_K) ≥ K`. The randomized versions assume `CC^R(DISJ_K) ≥ κK` (real `κ > 0`, private coins from nonempty
  coin spaces) as a hypothesis. There are also
  versions that need correctness only on connected networks (`H_{x,y}` is disconnected only for `x = y = 1`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2 (key fact: `≤ 1/ε` neighbours in `U`) | `Algorithm1.card_nbrs_U_le`, `Algorithm1.phase1_length` | `Algorithm1.lean` |
| Lemma 3 | `Algorithm1.lemma_3` | `Algorithm1.lean` |
| Lemma 4 | `Algorithm1.lemma_4` | `Algorithm1.lean` |
| Lemma 5 | `Algorithm1.lemma_5` | `Algorithm1.lean` |
| Theorem 1 (approximation factor, sequential semantics) | `Algorithm1.theorem_1_approx`, `Algorithm1.exists_final` | `Algorithm1.lean` |
| Lemma 6 | `lemma_6`, `lemma_6_approx` | `Lemma6.lean` |
| Lemma 6, proof claim `\|I\| < n/α`: **false** | `lemma_6_strict_false` (correct: `card_mul_le_of_indep`) | `Lemma6.lean` |
| Theorem 12 (5/3-approximation, Algorithm 2) | `Centralized.theorem_12`, `Centralized.exists_run`, `Centralized.run_length_le` | `Centralized.lean` |
| Lemmas 13, 14 (incl. `s₁ ≥ (3/2)\|V_{R'}\|`) | `Centralized.Inv` (`noTri`, `triClosed`), `Centralized.blue_bound` | `Centralized.lean` |
| Lemma 15 | `Centralized.Inv.charge`, `Centralized.inv_final` | `Centralized.lean` |
| Lemma 16 | `Centralized.lemma_16` | `Centralized.lean` |
| Corollary 17 (approximation, CONGEST variant) | `corollary_17` (via `Centralized.induced_bound`) | `Corollary17.lean` |
| Corollary 17, proof step "Theorem 12 on `G²[U]`": **false** | `Cor17Gap.corollary_17_proof_gap` | `Corollary17Gap.lean` |
| [CKP17] MVC family: cover `≤ 4(k−1)+4 log k` iff `x, y` intersect | `LowerBound.ckp17` | `CKP17.lean` |
| Lemma 21 | `LowerBound.lemma_21` | `LBGraphs.lean` |
| Lemma 23 | `LowerBound.lemma_23` | `LBGraphs.lean` |
| Lemma 24 | `LowerBound.lemma_24`, `LowerBound.lemma_24_vertexCoverNum` | `LBGraphs.lean` |
| Theorem 20 (exact `G²`-MWVC, `Ω̃(n²)`) | `LowerBound.theorem_20`, `theorem_20_n`, `theorem_20_connected`, `theorem_20_randomized` | `WeightedLB.lean`, `ConnectedLB.lean` |
| Theorem 22 (exact `G²`-MVC, `Ω̃(n²)`) | `LowerBound.theorem_22`, `theorem_22_n`, `theorem_22_connected`, `theorem_22_randomized` | `UnweightedLB.lean`, `ConnectedLB.lean` |

The namespaces sit under `Podc.PowerGraphApproximation`. `theorem_2x` gives `k² ≤ 8TB log k + 2` for
`n = 10k + 12k log k + 32 log k` (Theorem 22) and `6k + 4k log k + 16 log k` (Theorem 20). The `_n` versions say
`n² ≤ c · log² n · (8TB log n + 2)`. The generic gadget machinery is in `PathGadget.lean`: attaching paths to a core
graph so that the square, restricted to the core, is the core.

**Not formalized.** The CONGEST round complexities of Theorems 1, 7 and 11. Theorem 7 and Lemma 8 (weighted).
Theorem 11 and Corollary 10 (Congested Clique). Lemma 25, Theorem 26 and Corollary 27. Section 6 (G²-MDS
algorithm). Section 7 (MDS lower bounds). Section 8 (centralized hardness).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. Several
checks show the hypotheses are satisfiable: Algorithm 2 always reaches an output (`exists_run`), Phase I always
terminates (`exists_final`), and the "decides on connected members" hypotheses of Theorems 20/22 are met by CSLib's
gathering algorithm (`theorem_20_hyp_satisfiable`, `theorem_22_hyp_satisfiable`). The Corollary 17 counterexample
is checked by `decide`. CSLib candidates (`-- CSLib candidate`): `SimpleGraph.power` (staged in
`Podc/Foundations/Combinatorics/SimpleGraph/Power.lean`), `protocol_not_disj_lowerBound_of_ne_one` and
`family_not_disj_lowerBound_of_ne_one` (`ConnectedLB.lean`: `CC(¬DISJ)` lower bound for protocols correct except
on the input pair `(1, 1)`).
