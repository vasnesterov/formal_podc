# Differences between the formalization and the paper

Paper: Hussak–Trehan, *On Termination of a Flooding Process*, arXiv 1907.07078v1 (full version of the
PODC 2019 brief announcement).

## Statements

1. **Connectivity (under-specified statement; false only for disconnected graphs).** Section 3 says
   "Let `G` be a graph" but needs `G` connected. The abstract does assume connectivity.
   * Lemma 3.3 fails without connectivity: two isolated nodes have no ec node, but node 1 lies in no
     round-set (`Examples.lemma_3_3_needs_connected`).
   * Lemma 3.4 fails without connectivity: with the source isolated and an edge `1 – 2`, the graph is
     bipartite and `1` is an ec node (`Examples.lemma_3_4_needs_connected`). This counterexample
     relies on `edist` treating `∞ = ∞` as equidistant. If ec nodes are read with finite distances
     only, Lemma 3.4 still fails in the other direction: an isolated source plus a triangle is
     non-bipartite and has no ec nodes (not formalized; it is immediate).
   * We assume `G.Connected` in Lemmas 3.3 and 3.4 and Theorems 3.5 and 3.7, plus `Finite V` /
     `Fintype V` where eccentricity or termination is involved. Lemmas 3.2 and 3.6 and Theorem 2.2
     hold for every graph, finite or not, and are stated that way.
2. **Theorem 3.5.** "Flooding will have terminated after round `e`" is formalized as
   `TerminatesAfter G s e` (no message in any round `> e`). We also prove the exact form
   `IsTerminationTime G s e ↔ G.IsBipartite` (`theorem_3_5'`), using `R_e ≠ ∅`.
3. **Theorem 3.7.** "Flooding terminates after `j` rounds" is formalized as `IsTerminationTime G s j`
   (last active round `j`). `e` enters as a hypothesis `G.eccent s = e`; `d` is Mathlib's `G.diam`.
4. **Corollary 2.4** ("fewer than `2|G| + 1` rounds"). We prove the slightly stronger `R_t = ∅` for
   all `t ≥ 2|G|`, which the paper also states in the text. Hence the termination time is `< 2|G|`
   (`exists_isTerminationTime_lt`).
5. **Lemma 3.2(iii)** is stated as `IsSecondIn G s g (j + 1)`, i.e. `g² ∈ R_{j+1}`. The hypothesis
   `j ≥ 1` is kept but not needed.
6. **Lemma 3.3** "each node is contained in exactly one round-set" is formalized as
   `∀ v, ∃! j, v ∈ R_j`.
7. **Abstract (PODC version).** "An adversary can always ensure non-termination" is an over-claim if
   "always" means "on every graph". On every finite forest every adversary's run terminates
   (`asyncAF_terminates_of_isAcyclic`, `asyncAF_terminates_single_edge`). The arXiv text only claims
   (and proves) existence: an example suffices, the triangle. That is what we formalize
   (`asyncAF_triangle_nonterminating`).
   Cosmetic: the PODC abstract's "AF terminates on any arbitrary graph" is literally false for
   infinite graphs (an infinite ray, flooding from its endpoint, never terminates). The full version
   says "finite graph", and we assume `Finite V` / `Fintype V`.
8. **Figure 7 (wrong example).** As drawn (with the node `i`), `e = 3`, `d = 5`, and flooding takes
   7 rounds, so the figure does not attain `e + d + 1 = 9`, contrary to the caption
   (`Examples.figure_7_as_drawn`). Without `i`, the caption's `e = 2`, `d = 4`, `T = 7` is correct
   (`Examples.figure_7_without_i`). Sharpness of Theorem 3.7 itself is true: the Petersen graph
   (`petersen_sharp`) and the triangle (`triangle_sharp`) attain it.

## Proofs

9. **Theorem 3.5, proof gap (statement true).** The step "no node in 2 round-sets iff `R_e` is the
   last non-empty round-set (by Lemma 3.2)" is unjustified in the direction ⇐. If `R_e` is the last
   active round, some node might still receive twice, with both times `≤ e`; Lemma 3.2 does not exclude
   this. A correct argument: in a connected non-bipartite graph, a node at distance `e` has a walk of
   the other parity and therefore receives again in a round `> e`. We formalize this argument
   (`theorem_3_5`, via `exists_mem_roundSet_of_not_bipartite`). The gap can also be filled from the
   paper's own Lemma 3.6. By Lemma 3.2(iii) an ec node has a second appearance. By Lemma 3.6 and
   connectivity, every node then has one, including a node at distance `e`, whose second appearance
   is after round `e`.
10. **Theorem 2.2.** We prove it in two ways: from the parity-distance characterization
    (`theorem_2_2`), and by the paper's own minimal-counterexample argument (`PaperProof.no_even_repeat`).
    The paper's double minimality (duration, then start point) becomes a nested strong induction. The
    paper's proof is correct as written.
11. **Lemmas 3.2, 3.3, 3.4, 3.6 and Theorem 3.7.** Our proofs go through the characterization
    `v ∈ R_t ↔ t` is a parity distance (`mem_roundSet_iff`), not through the paper's case analyses. We
    checked those case analyses by hand and found them sound, apart from the small slip in Lemma 3.3
    ("`h ∈ D_i` for some `i ≥ 1`" ignores `h = g₀`, which gives the impossible `g² ∈ R_1`).
    For Theorem 3.7's upper bound we bound parity distances directly through an ec edge. This is the
    content of the paper's repeated use of Lemma 3.6, which we also prove separately (`lemma_3_6`).

## Modelling choices

12. **Synchronous model.** Messages are a relation `sends t u v` ("`u` sends to `v` in round `t`"),
    defined by recursion on rounds following Algorithm 1.1. There is no message in round 0;
    `R_0 = {s}`. Multiple copies on the same directed edge in one round cannot arise in the
    synchronous model.
13. **Distances.** We use Mathlib's `edist` (`ℕ∞`, `⊤` when unreachable) for `D_j` and ec nodes. This
    matches the paper's "usual distance function". In connected graphs it agrees with `dist`.
14. **Asynchronous model (§1.1.1, §4).** The adversary is a delay function `δ : ℕ → V → V → ℕ`: the
    message sent by `u` to `v` in round `r` is delivered in round `r + δ r u v`. A node receiving in
    round `r` from the set `I` sends in round `r + 1` to `N(v) \ I`, exactly as in Algorithm 1.1.
    Messages on the same directed edge that are delivered in the same round are merged (Prop
    semantics); the paper does not specify this case. An adaptive adversary yields such a `δ` along
    its (deterministic) run, so "for all `δ`" covers adaptive adversaries and "there is a `δ`" is the
    paper's existence claim. Figure 8's adversary is `triangleDelay`: from round 3 on, `c` holds every
    message it sends in an odd round for one extra round. The resulting run has period 4.
15. **Not formalized.** The informal claims of asymptotic time optimality for broadcast, the
    discussion and speculation in §1 and §5, and multi-source flooding, which the paper leaves open.
16. **Typos (not reflected in Lean).**
    * In Lemma 3.2(i)'s proof, the "Case `j = 1`" label should mark the inductive case.
    * "Definition 2.2(i)" should be Definition 3.1(ii).
    * "Lemma 3." / "Lemma ." should be Lemma 3.2(iii).
    * Figures 3(a)/(b) in §3 should be Figure 6; Figure 8 in §1.2 should be Figure 3.
    * "hypergraph" should be "hypercube".
    * Stray "in D rounds on a bipartite graph" in §1.1.
