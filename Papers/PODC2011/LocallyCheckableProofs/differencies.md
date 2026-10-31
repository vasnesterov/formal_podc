# Differences between the formalization and the paper

Paper: Göös, Suomela, *Locally Checkable Proofs in Distributed Computing*, ToC 12(19), 2016 (journal
version of PODC 2011).

## Model (Section 2)

1. **Instances.** Nodes are identifiers: `Inst L` has a node set `V : Finset ℕ`, a graph on `ℕ` with edges
   inside `V`, node labels `lab : ℕ → L` (any type) and marked edges `S ≤ G`. Marked edges are the 0/1 edge
   labels of graph problems such as spanning trees and matchings. The paper allows general weights and labels
   on edges; only 0/1 edge labels are needed for the results we check.
2. **Locality.** `IsLocal r A` means: the output at `v` depends only on the radius-`r` view, which consists of
   the ball, the induced edges and marked edges on it, and node membership, labels and proof labels on it. This
   is equivalent to the paper's `A(G,P,v) = A(G[v,r],P[v,r],v)`. Like the paper, we impose no computability
   constraints.
3. **Proof size.** `|P(v)| ≤ s(n)` for every node, where `n = |V|`. `LogLCP` means size `C·(⌊log₂ n⌋+1)` for
   some constant `C`.
4. **Completeness ranges over `F ∩ P`.** The paper assumes `P ⊆ F`, and the two readings agree.
5. **Weak schemes** (§2.3): `AdmitsWeakLCP` requires, for each graph of `F` with some correct solution, an
   accepted proof for some correct solution on the same graph. All our Theorem 5.1 lower bounds are proved
   against weak schemes, so they also hold for strong ones (`AdmitsLCP.weak`), as the paper claims.
6. **Asymptotic notation.**
   * "No proofs of size `o(f)`" is proved in two forms: explicit bounds (`s(n) ≥ c·log n − C` on the relevant
     `n`; `s(n) ≥ c n²` for all large `n`; `s(n) ≥ c n` for all large even `n`) and `¬ s =o[atTop] f`.
   * The constants depend on the horizon `r`, as in the paper.
   * Odd number of nodes, non-bipartite and maximum matching on cycles: the bound holds for odd `n` (the paper's
     construction uses odd `n`).
   * FPF-symmetric trees: the bound holds for even `n`. Trees with an odd number of nodes never have a
     fixed-point-free automorphism, so for odd `n` completeness is vacuous.

## Families and identifiers

7. **Identifier ranges.** The paper takes identifiers in `{1, …, poly(n)}`.
   * Lower bounds assume only that `F` contains the instances that the constructions need. For Theorem 5.1
     these are cycles with identifiers in `{1,…,n²}` (`PlainCycleFamily`, `CycleFamily`). For Theorems 6.1 and
     6.3 they are connected graphs / trees with identifiers in `{1,…,n}`. This makes the lower bounds as strong
     as possible.
   * Upper bounds use families with identifiers in `{1,…,n^c}`, for every `c` (`connIdFamily c`, `ConnPlainId c`).
   * The `Θ` theorems in `Summary.lean` combine both on a common family, which needs `c ≥ 2` for Theorem 5.1.
8. **Unlabelled graph properties** use families of `Plain` instances (no marked edges). Upper bounds of
   §5.1 are proved on the larger family `connIdFamily c`, which also contains marked instances, and are
   restricted afterwards (`LogLCP.anti`).

## Theorem 5.1 (Section 5.3–5.4)

9. **Bondy–Simonovits replaced.**
   * We use only `k = 2`, i.e. a monochromatic `C₄`. All the paper's applications use `k = 2`; for "odd `n`, even
     `k`" `k = 2` works.
   * The `C₄` comes from an elementary pigeonhole argument (`exists_mono_rect`): `t(t+1)² < |A|` and `t < |B|`
     suffice. The paper's condition is "fewer than `n^{1/3}` colours", with the extremal theorem.
   * Resulting bound: `n ≤ 4 (|L|·2^{s(n)+2})^{12r+12}`, i.e. `s(n) ≥ log₂ n/(12r+12) − O(1)`.
10. **Colour window.** `c(a,b)` records the `2r+2` nodes nearest to the glued edge on each side: label, proof,
    and mark of the edge to the successor. The paper uses `2r+1` nodes and node data only. The extra node is
    needed because edge marks are attached to nodes (item 11).
11. **Edge labels under gluing** (an imprecision of the paper, see README). The mark of the edge `{x, succ x}`
    is stored at `x` (`cyc l lab mk`). A new edge `{b_{i-1}[1], a_i[1]}` therefore inherits the mark stored at `b_{i-1}[1]`,
    i.e. the mark of the removed edge `{a_{i-1}[1], b_{i-1}[1]}` of the same piece. The paper inherits only
    `L(v)` and `P(v)`, which does not determine the solution on the new edges.
12. **Gluing typo.** The paper adds `{b_{i−1}[1], a_i[1]}` "for each `i > 1`"; this should be "for each `i`"
    (with `b_0 = b_k`). Typo in a proof (R3); it does not affect the label.
13. **Identifier blocks.** `a_i = {1+in+j : j < ⌊n/2⌋}`, `b_i = {1+in+⌊n/2⌋+j : j < ⌈n/2⌉}`. This is a concrete
    instance of the paper's "any partition".
14. **Problem definitions.**
    * Leader election: exactly one node labelled `true`.
    * Spanning tree: `(S.induce V).IsTree`. Its equivalence with the upper-bound formulation `MarkedSpanningTree`
      (acyclic and spanning) on nonempty instances is `spanningTree_iff`.
    * Maximum matching: `S` is a matching of maximum cardinality among matchings `M ≤ G`.
    * Non-bipartite: `¬ G.Colorable 2`.
    * Odd `n`: `Odd |V|`.
15. **Maximum matching (§5.4 remark)** is proved in full: the pieces have exactly `(n−1)/2` marked edges, and the
    glued `2n`-cycle has `n−1` marked edges but a matching with `n` edges.
16. **Not formalized: the Hamiltonian-cycle entry of Table 2** (`Θ(log n)`). §5 has no lower-bound argument for
    it, and the cycle gluing cannot give one: a glued all-marked cycle is a Hamiltonian cycle. A modified gadget
    (cycles plus an unmarked chord that is swapped during gluing) should work. Not counted in the verdict
    (unformalized).

## Section 5.1 (upper bounds)

17. The spanning-tree certificate adds a parent identifier to the paper's (root id, distance); children must be
    explicit for the counters. Proof size `m(2c+5)(⌊log₂ n⌋+1)` with `m ∈ {3,5,6}` numbers per label.
18. Non-bipartiteness uses a variant certificate of the same size: a tree from a root `r`, plus a second tree
    rooted at a node `g` that has a neighbour at the same claimed depth. The tree paths and that edge form an odd
    closed walk. The paper's "counter along the odd cycle through the leader" also only certifies an odd closed
    walk, which is enough. No error.
19. Colourability needs `k ≥ 1`: for `k = 0` the empty instance is a no-instance that no verifier can reject.
    This is a degenerate case of a remark, not a numbered statement.
20. `acyclic_logLCP` is proved on the connected family only.

## Section 6

21. **Universal `O(n²)` bound** (§6 intro): `(4c+10)·n²` bits on connected plain graphs with identifiers in
    `[1,n^c]`, for every `P`. Closure under isomorphism is not needed, because the code must equal the instance
    exactly. The bit length of identifiers is bounded crudely (`c·n+1`), which changes only the constant.
22. **Theorem 6.1.**
    * The family of `G₁` is the "good" graphs: asymmetric, and any two distinct vertices have `≥ 3` common
      neighbours. The paper uses all asymmetric connected graphs.
    * With good graphs, the degree-2 (more precisely: fewer than 3 neighbours) nodes of `G₁ ⊛ G₂` are exactly the
      path nodes. So an automorphism fixes or reverses the path. This replaces the paper's unproved step "by
      construction, `ϕ` must swap `G₁` and `G₂`", which is true but needs an argument.
    * "Almost all graphs are connected and asymmetric" (Erdős–Rényi) is replaced by a self-contained crude
      count: at least `2^{C(k,2)}/2` good labelled graphs for large `k` (`exists_many_good`).
    * Isomorphism classes are handled by "at most `k!` relabellings", not canonical forms.
    * The connecting path has `p` nodes for any `p ≥ k`. This gives the bound for all large `n` rather than only
      `n = 3k`. Constant: `c = 1/(256(2r+1))`.
23. **Theorem 6.3.**
    * Instead of all rooted trees (OEIS A000081) we use an explicit family of `2^m` caterpillars on `5m` nodes,
      pairwise non-isomorphic as rooted trees, with no degree-2 node.
    * Bound for all large even `n`, `c = 1/(32(2r+1))`.
    * The `O(n)` upper bound of §6.2 is `Trees.tree_upper` (`8n` bits). It needs `P` closed under isomorphism,
      which is what "graph property" means, and the fact that a connected graph covering a tree is isomorphic to
      it.
24. **Theorem 6.4 not formalized.** The fooling-set step is elementary (no communication-complexity black box
    is needed, since pigeonhole over the `2^{|I×I|}` sets suffices). The 3-colouring gadgets (Boolean gadget, colour
    changer, disjunction, decoder, wires) are not formalized.

## Section 7

25. **PN verifiers** (`IsPN`): the output is a function of the node's own proof label and the multiset of its
    neighbours' labels; there are no ports and no identifiers. This is a sub-class of one-round PN algorithms,
    which makes Theorem 7.1 stronger. The converse remark (PN verifiers are fooled by lifts) is proved for this
    class.
26. **Theorem 7.1.**
    * The honest proof "`(H, v)`" conflicts with the requirement that the encoded graph has identifiers
      `{1,…,n(G)}`. We use a relabelled copy of `H`, which lies in `P` because an isomorphism is a covering.
    * The paper's two checks (`deg_H v = deg_G ϕ(v)` and image of neighbours `= N_G(ϕ v)`) are merged into one
      equivalent multiset check.
    * Surjectivity of `ϕ` uses connectivity of the encoded `G`, which follows from `G ∈ P ⊆ F`. The paper leaves
      this implicit.
    * Size `24 n²`.
    * Proved for connected plain graphs with any identifiers, and with identifiers in `[1,n^c]`.
27. **§7.3 (`coLCP(0) ⊆ LogLCP`, unnumbered in the paper; an earlier version of this file called it
    "Theorem 7.3", but 7.3 is a Remark).** The new verifier has horizon `max(r,1)`. The root simulates the `LCP(0)` verifier on the
    empty proof, which is a function of its view (`ViewEq.restrict_radius`). As in the paper.
28. **Not formalized:** Theorem 7.2 (needs a full PN model with leaders / known `n` and DFS-interval identifiers);
    §7.4 (NP/poly); §7.5 (monadic Σ¹₁); §4 (reachability, connectivity, bipartite matching via König/LP duality).

## Verdict calibration

No checked statement is false; all repairs concern proof sketches (gluing typo, edge labels under gluing, the
automorphism step of 6.1, the honest proof of 7.1). These are routine details a referee would accept as
sketched, so the label is ✅. Borderline: item 11 (edge labels). A literal reading inherits only node data.
But the paper's colour `c(a,b)` holds "all auxiliary information ... within distance `2r+1`", and that includes
the label of the junction edge `{a[1], b[1]}`. Giving each new edge this common label makes the paper's
argument work as written. So this is not counted as a genuine repair (🛠️). Also borderline: the 6.1 step
"`ϕ` must swap `G₁` and `G₂`". It is true by a short argument (the unique longest run of degree-2 nodes, see
README), which a referee would accept as "by construction". The formalization avoids it rather than checking it.

## PODC 2011 version

The verdict is for the PODC 2011 paper. Its authors' copy is `https://jukkasuomela.fi/doc/lcp-podc.pdf`, and it
has no numbered theorems.
* §5.2–5.4 make the claims of Theorem 5.1 and §5.4, with the same gluing proof: the same "`i > 1`" typo and
  the same silence about edge labels.
* The cycles `C(a,b)` use a different identifier layout, `a, a+4n, a+6n, …` (identifiers up to about
  `n² + 3n`). This is still polynomial, so our `{1,…,n²}` construction proves the same statement.
* §6.1 and §6.2 are the journal's Theorems 6.1 and 6.3. §6.1 states "if `G₁`, `G₂` are not isomorphic, then `G`
  must be asymmetric" without argument; see the calibration above.
* §7.2 (weak/strong schemes) is the journal's §2.3; §7.3 (`coLCP(0) ⊆ LogLCP`) is the same as the journal's §7.3.
* The PODC §7.1 is the analogue of the journal's Theorem 7.2: a leader or port numbers instead of identifiers.
  It is not formalized.
* The journal's Theorem 7.1 (lifts, PN verifiers) does **not** appear in the PODC version. Our
  `Lifts.theorem_7_1` is therefore extra and does not affect the verdict.
* Table 2 of the PODC version also lists Hamiltonian cycle as `Θ(log n)`. The lower bound is unargued and
  unchecked (item 16).
