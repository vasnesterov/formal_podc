# Strong and Hiding Distributed Certification of k-Coloring — PODC 2025

Augusto Modanese, Pedro Montealegre, Martín Ríos-Wilson. *Brief Announcement: Strong and Hiding
Distributed Certification of k-Coloring.* PODC 2025. DOI
[10.1145/3732772.3733546](https://doi.org/10.1145/3732772.3733546). The proofs are in the full version
the BA cites, arXiv [2502.13854](https://arxiv.org/abs/2502.13854) **v1** (Feb 2025). We formalize the BA's
statements, using the v1 definitions and proofs. Numbering: BA Theorems 4.1–4.4 = v1 Theorems 1.1–1.4.
We also checked the corrected statements of v3 (Feb 2026, retitled "…of Bipartiteness", co-author
B. Jauregui). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** The main lower bound, **Theorem 4.2** ("no strong and hiding
`r`-round LCP for 2-colouring on classes containing an `r`-forgetful graph that is neither an even
cycle nor of minimum degree 1, no matter the certificate size, even if not anonymous"), is false. It
fails already for `r = 1`, for *anonymous* LCPs with `O(log n)`-bit certificates, and even on a
one-graph class. The authors' corrected v3 version (Theorems 2(1), 3(1), 4) is also false. The upper
bounds hold: Theorem 4.1 and Lemma 3.2 as stated. Theorems 4.3 and 4.4 hold as existence statements,
but their decoders are wrong: the shatter-point decoder is not strongly sound, and the watermelon
decoder is not even sound.

## Mistakes in the paper

* **Theorem 4.2 is false: a counter modulo `M > 2N` gives a strong, hiding, anonymous LCP.** Each
  node gets a counter `ℓ(v)`. With `M = 5(2N+1)` (odd, and larger than twice the number of nodes;
  nodes know `N` in the paper's model), a node accepts iff every neighbour's counter is
  `ℓ(v) ± 1 (mod M)`.
  - *Complete:* a proper `0/1` colouring is accepted on every bipartite graph.
  - *Strongly sound on every graph:* along a closed walk through accepting nodes, the integer
    displacement `z` satisfies `M | z`, `|z| ≤ L` and `z ≡ L (mod 2)`. A walk of length `L < 2n < M`
    therefore has even length, and short closed walks suffice for bipartiteness.
  - *Hiding, even against identifier-aware extraction algorithms:* use `θ(5,5,5)`, i.e. three paths
    of length 5 between two endpoints. It is bipartite, connected, 1-forgetful under both the BA
    and v3 definitions, has minimum degree 2, and is not a cycle. Label it `t + height`
    (`t ∈ ZMod M`), with identifiers rotating mod 5 on five nodes. Then node 2's view for `t` equals
    node 1's view for `t+1`: identifiers, ports, labels and degrees all agree. Nodes 1 and 2 are
    adjacent, so a successful extractor would flip its output at node 1 with every step `t ↦ t+1`.
    This is impossible since `M` is odd.

  The proof's gap: Lemma 5.3 (v3: Lemma 21) needs the odd closed walk in `V(D,n)` to have at most
  `√(N/Δʳ)` views, and this is never checked. Here every odd cycle of `V(D,n)` has length `≥ M > 2N`.
  This refutes BA Thm 4.2 for `H` = all bipartite graphs (`baTheorem42_false`). It also refutes
  v3's corrected statement for the class `{θ(5,5,5)}` (`v3Theorem4_false`); the same LCP is
  anonymous, so it refutes v1 Thm 1.5 (order-invariant) too.
* **Theorem 4.2's proof also restricts the class without justification.** v1 §5.2 says: "without
  restriction `H` only consists of `r`-forgetful graphs …, since a strong and hiding LCP for `H` is
  one for every subclass". This is false, because hiding only needs *one* hard instance. As a result,
  Theorem 4.2 fails even for anonymous **constant-size** LCPs: the paper's own LCP of Lemma 4.1 is
  complete on all bipartite graphs, strongly sound, and hiding through `P₆ ⊔ K₂`, so it works for
  `H` = all bipartite graphs (`baTheorem42Anon_false`). The authors concede the quantifier issue in
  v3 §2.2.4 and add `G ∩ H = ∅`.
* **The BA definition of `r`-forgetful is unsatisfiable for `r ≥ 2`.** The definition requires every
  `w ∈ Nʳ(u)` to move away along the path. Taking `w = v₁`, the distance drops from 1 to 0. So BA
  Theorem 4.2 is vacuous for `r ≥ 2` as written (`not_isForgetful_of_two_le`). v3 Definition 22
  fixes this.
* **Theorem 4.3's decoder is not strongly sound (statement true).** Two type-1 nodes `u, u'` attached
  to the same type-0 node (which rejects) can carry different colour vectors `(0,0)` and `(0,1)`.
  Then `u – w – u' – z' – z – u` is an accepted 5-cycle, with `w` in component 0 and `z, z'` in
  component 1. The proof's step "by 2(c), all neighbours of a type-1 node share the same colour" is
  false (`shatterLCP_not_stronglySound`). The theorem still holds. Graphs with a shatter point include
  `P₆` and `P₆ ⊔ K₂`, so the counter LCP (hiding against all algorithms) and the constant-size LCP of
  Lemma 4.1 (anonymous hiding) both work (`theorem_4_3`).
* **Theorem 4.4's decoder is not sound (statement true).** Rule 2(b) only asks that *some* entry of
  a path node records the endpoint's port, and a path node never checks the entry facing an
  endpoint. On a 5-cycle with endpoints `v₁, v₂`, path node `a` stores in its `v₂`-entry the port
  number that `v₁` uses towards `a`. So `v₁` reads the colour of the wrong edge, and every node of the
  5-cycle accepts (`watermelonLCP_not_sound`). The theorem still holds, because the counter LCP is
  hiding on the watermelon `θ(5,5,5)` (`theorem_4_4`).
* **Lemma 4.1 (δ = 1, part of Thm 4.1): proof gap, ambiguous rule, wrong figure.**
  - The soundness argument ("since `C` is odd, then `u ∈ V(C)`") proves nothing.
  - The rule "all other neighbours of `⊤` are labelled `β ∈ {0,1}`" works only if `β` is the same
    for all of them. If each neighbour may carry its own colour, a 5-cycle with a pendant node is
    accepted everywhere (`literalLCP_not_sound`).
  - Fig. 4's odd cycle in `V(D,4)` uses an edge between the views of nodes 3 and 4 that would need
    a triangle 2-3-4 (`fig4_edge_not_compatible`).

  We prove the lemma with the uniform reading. Strong soundness follows from an explicit 2-colouring:
  a `⊤` node gets `1-β` and a `⊥` node gets the `β` of its `⊤`. Hiding uses three labellings of
  `P₆ ⊔ K₂` (`theorem_4_1`).
* **Lemma 4.2 (even cycles): hiding argument mixes `C₄` and `C₆`.** Their views differ in `N`, so the
  claimed odd cycle is not in any `V(D,n)` of the paper's own model. A single `C₄` with
  reflection-symmetric ports suffices: two adjacent nodes get identical anonymous views
  (`lemma_4_2`).
* **v3 Theorem 1 is false as stated** ("for any class of bipartite graphs meeting `H`"). On `{P₃}`, an
  anonymous algorithm colours by degree (`v3Theorem1_false`). The paper itself makes this
  observation for stars.
* *Minor.* `k-col` is defined with colours `{0,…,k}` (k+1 colours). In Lemma 3.2's proof, "proper
  2-coloring" should read "k-coloring", and (v3) `D′(u) ≠ A(v)` mixes names.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* **Network and verifier.** One-round LCPs (`r = 1`) on finite simple port-numbered graphs (ports
  `0..deg-1`, injective), with injective identifiers `< N` and `N = bound n` known to every node.
  `bound` is arbitrary; all results hold for every choice. The model is deterministic, with no
  failures. The prover is an adversary that picks arbitrary labels in the soundness properties.
* **Views.** A view is `N`, the node's own identifier, label and degree, and the multiset of
  neighbour records (port here, port there, identifier, label, degree). This contains the paper's
  radius-1 view, plus neighbour degrees. The extra degrees only strengthen extraction algorithms,
  hence strengthen our hiding results. Anonymous algorithms factor through `View.anon`.
* **Properties.** We formalize completeness, soundness, strong (promise) soundness, hiding (some
  hard instance per algorithm) and anonymous hiding as in v1 §2. Extraction algorithms are
  arbitrary functions; the paper requires computable ones, which is weaker. Certificate sizes are
  sets `sz n` of admissible labels: constant size = a finite label type; the counter LCP uses labels
  `< 5(2N+1)`.
* **Not covered.** General `r` is not formalized. Thm 4.2 is refuted at `r = 1`, which suffices
  since it is stated for every `r ≥ 1`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.2 (hiding ⇔ `V(D,n)` not `k`-colourable) | `LCP.lemma_3_2`, `lemma_3_2_hiding`, `lemma_3_2_anon` | `NeighborhoodGraph.lean` |
| Theorem 4.1 (δ = 1 ∪ even cycles) | `theorem_4_1` | `MinDegreeOne.lean` |
| Lemma 4.1 (v1): strong soundness, completeness, hiding | `degOneLCP_stronglySoundAll`, `degOneLCP_complete`, `degOneLCP_anonHiding` | `MinDegreeOne.lean` |
| Lemma 4.1, literal rule 2(b) unsound | `literalLCP_not_sound` | `MinDegreeOne.lean` |
| Fig. 4 edge invalid | `fig4_edge_not_compatible` | `MinDegreeOne.lean` |
| Lemma 4.2 (v1, even cycles) | `lemma_4_2` | `EvenCycles.lean` |
| Theorem 4.2 false | `baTheorem42_false` (statement `BATheorem42`) | `Theorem42.lean` |
| v3 Thm 4 / 2(1) / 3(1) false | `v3Theorem4_false` | `Theorem42.lean` |
| Thm 4.2 false for anonymous constant-size LCPs | `baTheorem42Anon_false` | `Theorem42Anon.lean` |
| v3 Theorem 1 false | `v3Theorem1_false` | `Theorem42Anon.lean` |
| counter LCP: strong, hiding, anonymous | `counterLCP_strong_hiding`, `counterLCP_hiding` | `Theorem42.lean`, `Theta.lean` |
| `r`-forgetful (BA, v3); `θ(5,5,5)` is 1-forgetful; BA definition vacuous for `r ≥ 2` | `IsForgetful`, `IsForgetfulV3`, `thetaG_isForgetful`, `thetaG_isForgetfulV3`, `not_isForgetful_of_two_le` | `Forgetful.lean` |
| Theorem 4.3 (statement true; decoder not strongly sound) | `theorem_4_3`, `shatterLCP_not_stronglySound` | `ShatterWatermelon.lean` |
| Theorem 4.4 (statement true; decoder not sound) | `theorem_4_4`, `watermelonLCP_not_sound` | `ShatterWatermelon.lean` |

**Not formalized.**
* Lemma 3.1 (computability of `V(D,n)`).
* The `r ≥ 2` model.
* v1 §6: the Ramsey reduction to order-invariant LCPs, and Theorem 6.3, the constant-size
  non-anonymous lower bound. Our counterexamples use `Θ(log n)`-bit or anonymous LCPs, so they do
  not touch Theorem 6.3; its proof relies on Theorem 1.5, whose proof has both gaps above.
* v3's new Theorems 5–7.
* The watermelon class is not defined formally: Theorem 4.4 is proved for every bipartite class
  containing `θ(5,5,5)`.

**Trust.** No `sorry`, no `native_decide`. The listed theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Every LCP comes with completeness and with an
accepted hard instance, so hiding is never vacuous. Concrete instances are checked by `decide`.
The model is self-contained (Mathlib only). CSLib candidates, marked `-- CSLib candidate`:
`colorable_two_of_even_short_loops` and `exists_odd_cycle` (`Graph.lean`), and the one-round LCP
model (`Model.lean`).
