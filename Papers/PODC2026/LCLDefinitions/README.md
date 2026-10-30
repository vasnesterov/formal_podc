# It does not matter how you define LCLs — PODC 2026

Antonio Cruciani, Avinandan Das, Alesya Raevskaya, Jukka Suomela. *Brief Announcement: It Does Not Matter How
You Define Locally Checkable Labelings.* PODC 2026. DOI
[10.1145/3796701.3815923](https://doi.org/10.1145/3796701.3815923). Formalized version: the full version
arXiv:2602.18188v1 (40 pages).

**Verdict: ❌ False claim.** Theorem 5.1, the graph-theoretic key of the reduction from LCLs to PN-checkable
problems, is false as stated. So is Lemma 5.13. The hypothesis compares colours only inside an `r`-gball, but the
conclusion is about a set of gadgeted diameter `2r`. Theorem 5.1 becomes true once edge-consistency is required for
all pairs of vertices; we prove that repaired version in full, with the paper's proof strategy. Section 6 (PN-checkable
→ RE formalism, Lemmas 6.2–6.6) is correct up to typos. The main Theorem 7.1 is not refuted, but as written it relies
on the false Theorem 5.1, through Lemmas 5.4 and 5.8.

## Mistakes in the paper

- **Theorem 5.1 is false as stated (numbered theorem, not the headline).** Condition 2 ("edge-consistent in every
  `r`-gball") requires: for every edge `{v,u}` and every `v' ∈ gball_r(v)` with `χ(v') = χ(v)`, `v'` has a
  neighbour of colour `χ(u)`. The conclusion claims all of `gball_r(v)` has distinct colours. Two vertices of
  `gball_r(v)` can be at gadgeted distance up to `2r`, and the hypothesis never compares such a pair.
  Counterexample: base graph `K_{3,3}`, edges expanded into `1, …, 9` A-gadgets (an injective, hence distance-`2r`,
  edge colouring), `r = 1`. Take an injective colouring and give the two original vertices `0` and `1` the same
  colour. They are at distance 2 in `K_{3,3}`, so at gadgeted distance `2 > r` and graph distance `> 2`. Hence
  conditions 1 and 2 hold. Both lie in the `1`-gball of the original vertex `3`. (`theorem_5_1_false`)
  The paper's proof establishes only that the colour of the centre `v` and of its outer neighbours is unique in
  `gball_r(v)` (Corollary 5.14, Lemma 5.13). Corollary 5.16 then concludes uniqueness for *every* pair, which does
  not follow. Even those partial claims fail at the boundary of the gball (next items).
- **Lemma 5.13 is false as stated (numbered lemma).** Same idea: in the gadgeted `K_{3,3}`, `r = 1`, give the
  original vertex `1` the colour of the outer vertex `v` of the expanded edge `{0,3}` next to `3`. Then `1 ∈ gball_1(3)`
  but `1` and `v` are at gadgeted distance `3/2 > 1`. (`lemma_5_13_false`)
- **Corollary 5.14 also fails (SAT experiment, not Lean-checked).** In the gadgeted `K_4` with lengths `1, …, 6`
  and `r = 1`, a SAT search found a colouring satisfying conditions 1 and 2 in which two *adjacent* original
  vertices get the same colour. The proof of 5.14 applies Lemma 5.13 to a vertex `u'` that may lie outside
  `gball_r(v)`.
- **What is true (our repair).** If edge-consistency holds for all pairs of vertices, then every `gball_r(v)` is
  injectively coloured. This uses `x` as a distance-`2r` edge colouring with positive lengths; simplicity and
  3-regularity are not needed (`theorem_5_1_repaired`). The proof follows the paper's ideas, made precise:
  - An original vertex never shares a colour with a vertex in a triangle (Lemma 5.2/5.9; the Figure 2 case
    analysis).
  - Colours propagate rigidly along expanded edges, so matched edges have equal length (Lemmas 5.12–5.13).
  - The distance-`2r` edge colouring then forces two equally coloured vertices of a gball onto the same expanded
    edge, read in opposite directions.
  - That is impossible: at the middle of the edge, two vertices at distance `≤ 2` would get the same colour.

  In the application (Lemma 5.4) consistency is only checked inside PN-views of radius `r_D`. So Problem D needs a
  view radius large enough to cover every pair the argument compares; see `differencies.md`.
- **Consequences.** Lemma 5.4 (soundness of the lift B → D) invokes Theorem 5.1 and inherits the gap. So do
  Lemma 5.8 and Theorem 7.1. We see no reason to doubt that they hold with the repaired theorem and a larger
  `r_D`, but this part is not formalized.
- Typos and small slips:
  - Proof of Lemma 6.4: `(T(v→u)) ≅ (T(v∖u))` should read `(T(u∖v))`.
  - Lemma 6.2 silently needs every view of `C_D` to have a root with 3 children. This holds for PN-views of
    3-regular graphs.
  - The remark "only original vertices are non-triangle vertices" is attributed to Lemma 5.2, but it holds by
    construction.
  - `x : E(G) → ℕ` allows length 0, which the gadget construction cannot handle; we require positive lengths.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- No distributed model is formalized. The checked results are about problem definitions, graphs and colourings.
  Round complexities, symmetry breaking `♢(M)` and the simulations of Section 3 are not modelled.
- Section 5: a base graph is given by an edge type with endpoint maps (`Base`), so multigraphs are allowed and
  edges have an orientation that is used only to lay out the chain. `len` is the paper's edge colouring `x`.
  `gadget(G, x)` is `Base.graph` on original vertices and chain positions `gad e k`, `k < 6·len e`.
  - The paper's A-gadget vertices `1, 2, 3, 5, 4, 6` become positions `0, …, 5`, so the chain is a path plus
    chords and reading it backwards is `k ↦ 6L−1−k`.
  - Gadgeted distance uses doubled 0/1 weights.
  - "Distance-`k` edge colouring" means line-graph distance `≤ k ⇒` different colours (the paper does not define it).
  - Conditions 1 and 2 of Theorem 5.1 are `IsDist2Coloring` and `IsEdgeConsistentIn r`, taken literally. Our
    repaired hypothesis is `IsEdgeConsistent`.
- Section 6: PN-views up to isomorphism are canonical forms `View L k` (label plus multiset of child views).
  `pnView G σ r v` is the tree of non-backtracking walks. An RE problem is a pair of multiset constraints on the
  half-edge labels around a node and along an edge, on a 3-regular simple graph. Outcomes are `PMF`s over
  labellings.

**Main results in Lean** (namespace `Podc.LCLDefinitions`).

| Paper | Lean | File |
|---|---|---|
| Theorem 5.1 as stated — **false** | `theorem_5_1_false` | `Counterexample.lean` |
| Lemma 5.13 as stated — **false** | `lemma_5_13_false` | `Counterexample.lean` |
| Theorem 5.1, repaired (global edge-consistency) | `Base.theorem_5_1_repaired` | `Theorem51.lean` |
| Lemma 5.2 / Figure 2 (local core) | `BlockFacts.ne_pv_p3`, `BlockFacts.ne_pv_p4` | `Local.lean` |
| Lemma 5.9, Corollary 5.10 (global consistency) | `ne_of_triangle`, `Base.orig_ne_gad` | `Local.lean`, `Rigidity.lean` |
| Lemmas 5.12–5.13 (inductions along expanded edges) | `block_step`, `Base.rigid`, `Base.match_pos` | `Local.lean`, `Rigidity.lean` |
| Remark of §5.1 (`gdist` of originals; gball shape) | `Base.gd2_start_stop`, `Base.mem_gball_orig`, `Base.mem_gball_gad` | `Theorem51.lean` |
| Remark of §6 (`T(v→u) ≅ T(u∖v)`) | `branch_eq_prune_pnView` | `PNView.lean` |
| Definition 6.1 (problem E) | `problemE` | `REFormalism.lean` |
| Lemma 6.2 | `pnView_eq_of_valid` | `REFormalism.lean` |
| Lemma 6.3 (lift E → D) | `liftED_valid` | `REFormalism.lean` |
| Lemma 6.4 (lift D → E) | `liftDE_valid` | `REFormalism.lean` |
| Lemmas 6.5, 6.6 | `lemma_6_5`, `lemma_6_6` | `Outcome.lean` |
| Lemmas 4.4, 4.5, 5.6, 5.7 (common argument) | `SolvesWithProb.map` | `Outcome.lean` |

**Not formalized.**
- Sections 3–4: the general encoding/decoding framework, the simulations, the ladder gadgets and Lemmas 4.1–4.3, 4.6.
- Problem D and Lemmas 5.3–5.5, 5.8.
- Lemma 6.7 and Theorem 7.1: the complexity statements.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the counterexamples are concrete. `theorem_5_1_repaired_nonvacuous` applies the repaired theorem to
the gadgeted `K_{3,3}`. `theorem_5_1_false` also checks that this instance is simple, 3-regular and correctly
coloured. CSLib candidates: `View`/`pnView`/`branch_eq_prune_pnView`, `REProblem` with the PN → RE reduction, and
`SolvesWithProb.map`.
