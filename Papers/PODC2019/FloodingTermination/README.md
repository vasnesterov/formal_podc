# On Termination of a Flooding Process — PODC 2019

Walter Hussak, Amitabh Trehan. *On Termination of a Flooding Process.* PODC 2019 (brief announcement).
DOI [10.1145/3293611.3331586](https://doi.org/10.1145/3293611.3331586). Formalized version: arXiv
[1907.07078](https://arxiv.org/abs/1907.07078) v1, the full version and the only arXiv version. Numbering
follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All results hold for finite connected graphs, as the abstract
assumes. These are termination of synchronous amnesiac flooding (Theorem 2.2, Corollary 2.4),
termination time exactly `e = ecc(source)` iff the graph is bipartite (Theorem 3.5), and
`e < T ≤ e + d + 1` otherwise (Theorem 3.7). The Section 4 non-termination example also holds. The
fixes needed:
* Theorem 3.5's proof has a gap, which the paper's own Lemma 3.6 can fill.
* The PODC abstract's "always" (non-termination under an asynchronous adversary) is false on forests.
* Lemmas 3.3 and 3.4 need connectivity.
* Figure 7 does not show sharpness.

## Mistakes in the paper

* **Lemmas 3.3 and 3.4 need `G` connected.** Section 3 states them for "a graph `G`", but both fail
  for disconnected graphs. The abstract assumes connectivity, so this is an under-specified statement,
  not a real error. Lemma 3.3 fails on two isolated nodes: there is no ec node, yet node 1 lies in no
  round-set. Lemma 3.4 fails when the source is isolated and there is one more edge `1 – 2`: the graph
  is bipartite, yet `1` is an ec node. This counterexample relies on `∞ = ∞` counting as
  "equidistant", which is the paper's literal "usual distance" (Mathlib `edist`). If only finite
  distances count, Lemma 3.4 still fails: take an isolated source plus a triangle. The graph is not
  bipartite, but it has no ec nodes. Theorems 3.5 and 3.7
  need connectivity too, for `e` and `d` to be finite and for the bipartite/ec link.
  (`Examples.lemma_3_3_needs_connected`, `Examples.lemma_3_4_needs_connected`)
* **Theorem 3.5: proof gap, statement true.** The last step of the chain claims "no node appears in 2
  round-sets iff `R_e` is the last non-empty round-set (by Lemma 3.2)". The direction ⇐ does not follow
  from Lemma 3.2. A node may receive twice, both times by round `e`. One must show that second
  appearances reach the farthest node, at a round after `e`. That needs Lemma 3.6 (which comes later)
  or a parity argument: in a connected non-bipartite graph, a node at distance `e` also has a walk of
  the other parity, so it receives again after round `e`. The gap can be filled with the paper's own
  Lemma 3.6 (with Lemma 3.2(iii) and connectivity, it propagates a second appearance to the farthest
  node). We use the parity argument. (`theorem_3_5`)
* **Figure 7 does not show sharpness as drawn.** The caption says flooding from `b` takes
  `7 = 2 + 4 + 1 = e + d + 1` rounds. The drawn graph has an extra pendant node `i` (`d – h – i`), so
  `e = 3`, `d = 5`, and termination takes `7 < 9` rounds. Without `i` the caption's numbers are right.
  So are the Petersen graph (from every node: `5 = e + d + 1`) and the triangle; the upper bound of
  Theorem 3.7 is sharp. (`Examples.figure_7_as_drawn`, `Examples.figure_7_without_i`,
  `Examples.petersen_sharp`, `Examples.triangle_sharp`)
* **The PODC abstract overstates Section 4.** It says "an adversary can *always* ensure
  non-termination". The paper shows this only for one graph, the triangle (Figure 8). On every finite
  forest, e.g. a single edge, every adversary's run terminates: each message moves away from the
  source. So non-termination is possible on some graphs, not on all. (`asyncAF_terminates_of_isAcyclic`,
  `asyncAF_terminates_single_edge`)
  Similarly, but only cosmetically, the PODC abstract says "AF terminates on any arbitrary graph". That is
  literally false for infinite graphs: on an infinite ray, flooding from the endpoint never stops. The
  full version says "finite graph".
* **Typos and slips.**
  * In the proof of Lemma 3.2(i), "Case `j = 1`" should be the inductive case.
  * In Lemma 3.2(iii), "Definition 2.2(i)" should be Definition 3.1(ii).
  * "Lemma 3." / "Lemma ." should be Lemma 3.2(iii).
  * §3 refers to Figures 3(a)/(b) for the cycles; it means Figure 6.
  * §1.2 refers to Figure 8 for the triangle; it means Figure 3.
  * "hypergraph" should be "hypercube".
  * Stray text "in D rounds on a bipartite graph" in §1.1.
  * In the proof of Lemma 3.3, "`h ∈ D_i` for some `i ≥ 1`" overlooks `h = g₀`, which is harmless.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `G : SimpleGraph V` with source `s`, in synchronous rounds `1, 2, …`. In round 1, `s` sends to all its
  neighbours. In round `t + 1`, every node that received in round `t` sends to all neighbours that did
  not send to it in round `t` (`sends`, `afStep`; Algorithm 1.1). The round-sets are `R_0 = {s}` and
  `R_t` = the receivers in round `t` (Definition 2.1).
* "Terminated after round `T`" means no message is sent in any round `> T` (`TerminatesAfter`). The
  termination time is the last active round (`IsTerminationTime`, which also needs `R_T ≠ ∅`).
* Distances, eccentricity, diameter and bipartiteness come from Mathlib (`edist`/`dist`, `eccent`,
  `diam`, `IsBipartite = Colorable 2`). Section 2 holds for arbitrary graphs (Theorem 2.2) or finite
  ones (Corollary 2.4). Section 3 assumes finite and connected.
* Single source only, as in the paper.
* Asynchronous model (§1.1.1, §4): a delay function `δ r u v`, so the message sent from `u` to `v` in
  round `r` arrives in round `r + δ r u v`. `δ = 0` gives the synchronous model (`asends_zero_delay`).
  The process is deterministic and sends at most one message per directed edge per round, so an
  adaptive adversary's choices in a run form such a function.
* **Key lemma** (`sends_succ_iff`, `mem_roundSet_iff`): `v ∈ R_t` iff some walk from `s` to `v` has
  length `t` and no shorter walk has the same parity. So amnesiac flooding is BFS in the bipartite
  double cover. All of Section 3 follows from it. Theorem 2.2 is also proved separately by the paper's
  own argument (`PaperProof.lean`).

**Main results in Lean** (namespace `FloodingTermination`).

| Paper | Lean | File |
|---|---|---|
| Theorem 2.2 (≤ 2 round-sets per node) | `theorem_2_2`, `theorem_2_2'` (`encard ≤ 2`) | `Termination.lean` |
| Theorem 2.2, the paper's proof | `PaperProof.theorem_2_2`, `PaperProof.no_even_repeat` | `PaperProof.lean` |
| Corollary 2.4 (`R_t = ∅` for `t ≥ 2n`; termination) | `corollary_2_4`, `terminates`, `exists_isTerminationTime_lt` | `Termination.lean` |
| Lemma 3.2 (i), (ii), (iii) | `lemma_3_2_i`, `lemma_3_2_ii`, `lemma_3_2_iii` | `TerminationTime.lean` |
| Lemma 3.3 (connected) | `lemma_3_3` | `TerminationTime.lean` |
| Lemma 3.4 (connected) | `lemma_3_4` | `TerminationTime.lean` |
| Theorem 3.5 (terminated after `e` ⇔ bipartite) | `theorem_3_5`, `theorem_3_5'` (exact time) | `TerminationTime.lean` |
| Lemma 3.6 | `lemma_3_6` | `TerminationTime.lean` |
| Theorem 3.7 (`e < T ≤ e + d + 1`) | `theorem_3_7` | `TerminationTime.lean` |
| Abstract: `≤ d` / `≤ 2d + 1` | `terminationTime_le_diam`, `terminationTime_le_two_mul_diam_add_one` | `TerminationTime.lean` |
| Figures 1, 2, 3, 6 (cube, path, cycles, triangle) | `cube_time`, `path4_time`, `cycles_time`, `triangle_sharp` | `Examples.lean` |
| Petersen graph, Figure 7, sharpness | `petersen_sharp`, `figure_7_as_drawn`, `figure_7_without_i` | `Examples.lean` |
| Section 4, Figure 8 (non-termination on the triangle) | `asyncAF_triangle_nonterminating` | `Async.lean` |
| (new) termination on forests for every adversary | `asyncAF_terminates_of_isAcyclic`, `asyncAF_terminates_single_edge` | `Async.lean` |

**Not formalized.** The informal remarks: asymptotic time optimality for broadcast, and the applications
and speculation in §1 and §5.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
The examples are checked by `decide` (no `native_decide`) through `simulate`, a finite-set
implementation proved equal to the model (`mem_simulate`). The same simulation computes distances
(`isFirstIn_iff`), so the examples also certify `eccent` and `diam`. The hypotheses are satisfiable:
the examples cover bipartite and non-bipartite connected graphs. The asynchronous model is checked
against the synchronous one (`asends_zero_delay`).

An exhaustive check on all connected graphs with at most 6 nodes (not part of the repository) agrees
with every claim of Sections 2–3.

**Infrastructure.** `Podc/Graphs/WalkParity.lean` (CSLib candidate) provides walks of exact length,
parity distances, the parity facts for bipartite and non-bipartite graphs, and unique BFS parents in
forests.
