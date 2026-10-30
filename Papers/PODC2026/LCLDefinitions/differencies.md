# Differences between the formalization and the paper

Paper: Cruciani, Das, Raevskaya, Suomela, *It does not matter how you define locally checkable labelings*,
arXiv:2602.18188v1 (full version of the PODC 2026 brief announcement).

## Statement-level issues (with the verdict rule that decides them)

1. **Theorem 5.1 is false as stated** (`theorem_5_1_false`). Gadgeted `K_{3,3}`, lengths `1..9`, `r = 1`, colouring
   injective except `χ(0) = χ(1)` (two original vertices on the same side). The hypotheses of the paper hold
   literally: `K_{3,3}` is 3-regular and simple, and the injective colouring is a distance-`2r` edge colouring under
   any definition. Condition 1 holds since the vertices are at graph distance `≥ 3`. Condition 2 holds since they are
   at gadgeted distance `2 > r`. Yet `0, 1 ∈ gball_1(3)`.
   - Rule: R1 (numbered theorem). Not R2: `r = 1`, `K_{3,3}` is not degenerate. Not R3/R4: the fix changes a
     hypothesis of the theorem, its proof reasons with the stated version, and the proof also misses the pairs not
     involving the centre (Corollary 5.16 does not follow from 5.13–5.15). Not R5: Theorem 5.1 is not the headline
     (the abstract and title are about Theorem 7.1). So: ❌.
   - Reading checked on the rendered page (p. 26): condition 2 is spelled out as "for every vertex
     `v' ∈ gball_r(v)` such that `χ(v') = χ(v)` …". An alternative reading of the name "edge-consistent in every
     `r`-gball" is "for any two vertices of a common `r`-gball (of any vertex)". Under it, SAT checks on small
     instances found no counterexample: `K_4` and `K_{3,3}` at `r = 1` are UNSAT; `Q_3` at `r = 1` is UNSAT;
     `Prism_6` and Petersen were inconclusive. We judge the explicit definition.
   - The colours are `χ : Vert → C` for an arbitrary type `C` (the paper: `χ : V(G) → ℕ`). The counterexample
     uses `C = Vert`, a finite type, so it transfers to `ℕ` by any injection.
2. **Lemma 5.13 is false as stated** (`lemma_5_13_false`). Same instance; the original vertex `1` gets the colour of
   the outer vertex of the expanded edge `{0,3}` at `3`. R1, ❌ (numbered lemma).
3. **Corollary 5.14 fails** (SAT experiment only, not Lean-checked). Gadgeted `K_4`, lengths `1..6`, `r = 1`: a
   colouring satisfying conditions 1 and 2 with two adjacent original vertices of the same colour exists. Its proof
   uses Lemma 5.13 for a vertex `u'` outside `gball_r(v)`. Lemmas 5.2 and 5.9 and Corollaries 5.10–5.11 were also
   tested under the literal hypotheses:
   - Corollary 5.11 has SAT counterexamples (`K_4`, `K_{3,3}`).
   - Lemma 5.9 is UNSAT on `K_4`.
   - Lemma 5.2 and Lemma 5.12 were inconclusive or UNSAT.

   We do not rely on these for the verdict.
4. **Theorem 7.1 (headline) is unestablished, not refuted.** Its proof goes A → B → D → E. The step B → D
   (Lemmas 5.4, 5.8) uses Theorem 5.1. With our repaired Theorem 5.1 the step plausibly goes through, if Problem D
   uses a large enough view radius (item 8). R5: an unestablished headline is ❌, the same label as item 1.

## Repaired Theorem 5.1 (`Base.theorem_5_1_repaired`)

5. **Hypothesis strengthened.** Condition 2 is required for all pairs of vertices (`IsEdgeConsistent`), not only for
   `v' ∈ gball_r(v)`.
   - The proof compares only vertices on expanded edges that meet `gball_r(v)`, together with their far endpoints
     and neighbours. So a version with consistency up to gadgeted distance about `2r + 2` should suffice. This
     local version is **not** formalized.
   - SAT checks with consistency up to gadgeted distance `2r` were UNSAT: `K_4` and `K_{3,3}` at `r = 1`, `Q_3` at
     `r = 2`.
6. **Hypotheses weakened.**
   - The base graph may have loops and parallel edges and need not be 3-regular.
   - Lengths must be positive. The paper's `x : E → ℕ` allows `0`, for which "a sequence of 0 gadgets" is
     meaningless.
   - "Distance-`k` edge colouring" (undefined in the paper) is taken as: distinct edges at line-graph distance
     `≤ k` (endpoints at base distance `≤ k − 1`) get distinct colours.
7. **Proof.** It follows the paper's architecture, but each step is proved where the paper argues with figures or
   "by symmetry".
   - Local core (Lemma 5.2 / Figure 2, `Local.lean`): the vertex before a gadget never shares its colour with the
     gadget's paper-vertices `4`/`5`.
   - Lemma 5.9 / Corollary 5.10: originals never share colours with gadget vertices.
   - Lemmas 5.12/5.13: rigid propagation along expanded edges, gadget by gadget, up to the `2 ↔ 3, 4 ↔ 5`
     symmetry of the A-gadget. This gives equal lengths and equally coloured far ends.
   - Conclusion via the distance-`2r` edge colouring: two equally coloured vertices of a gball lie on the same
     expanded edge, matched with itself, either identically or backwards. Backwards fails at the middle gadget:
     for odd length, paper-vertex `2` gets the colour of `4` or `5`; for even length, two adjacent vertices
     `6 — 1` get the same colour. In the paper this case is covered by Lemma 5.12 (a gadget sequence is
     injectively coloured), whose proof by minimal counterexample is sketchy; the final sentence of Lemma 5.13
     ("no 2 sequences have the same length in the r-gneighborhood") covers different edges.

## Not formalized / informal parts of the paper (reviewed, not checked in Lean)

8. **Problem D.**
   - Reconstructibility ("for every two vertices labelled the same, the labels of their neighbours are also the
     same") is checked inside a PN-view, a tree whose leaves have only one neighbour in the view. Read literally,
     it fails whenever a leaf shares a colour with an internal node. The intended meaning (neighbours in `G` of
     vertices whose neighbourhood is visible) has to be assumed.
   - With the repaired Theorem 5.1, the view radius `r_D = (4k+1) r_B + 1` must also cover all pairs compared by
     the argument (item 5). This is a change of constants in the problem definition.
   - `k` (the colour bound of `x`) must bound the lengths used; this is implicit.
9. **Section 4.**
   - The decoded instance of an arbitrary 3-regular graph is a multigraph, possibly with vertices of degree
     `3 > d`, while `A` is an LCL on simple graphs of maximum degree `d` (Lemma 4.3 runs `A` on it). The
     introduction says an LCL can declare such nodes unconstrained, but always-solvability of that extension is
     not argued.
   - An isolated vertex of `G` becomes a "chordless cycle" of length 2 (a double edge).
   - "WLOG every element of `C_B` has radius exactly `r_B`".
10. **Lemmas 4.6, 5.8, 6.7, Theorem 7.1.** These are complexity statements over unspecified models
    `M` with `Θ`/`Ω` notation. Not modelled.
11. **Lemma 5.3 / 4.1 (uniqueness of encoding).** Not formalized (`decode` is not defined for Section 5).

## Section 6 (formalized; correct up to the following)

12. **Typo.** Proof of Lemma 6.4: `(T(v→u)) ≅ (T(v∖u))` should be `(T(u∖v))` (the paper's own Remark).
13. **Hidden assumption.** Lemma 6.2 needs every view in `C_D` to have exactly three root children; we add it to
    `C_V`. Such views are the only ones that occur on 3-regular graphs, so nothing is lost.
14. **Modelling.**
    - PN-views up to isomorphism are canonical forms (`View`).
    - `ζ` (neighbour enumeration of a view) is a fixed `Multiset.toList` order; `γ` is chosen by choice.
    - `Σ_E = View × Fin 3` instead of `C_D × [3]`; only labels with first component in `C_D` are accepted.
    - Radius written `r + 1 ≥ 1`.
    - The second conjunct of `I_fit` is redundant, since `C_E` is a set of unordered pairs.
15. **Lemmas 6.5/6.6** are proved for `PMF` outcomes. Locality of outcomes is not modelled. Lemmas 4.4, 4.5, 5.6,
    5.7 are the same argument (`SolvesWithProb.map`). Their soundness premises (Lemmas 4.2, 4.3, 5.4, 5.5) are not
    formalized.
