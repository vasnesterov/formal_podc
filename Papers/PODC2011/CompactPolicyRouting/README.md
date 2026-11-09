# Compact Policy Routing — PODC 2011

Gábor Rétvári, András Gulyás, Zalán Heszberger, Márton Csernai, József J. Bíró. *Compact policy routing.* PODC 2011.
DOI [10.1145/1993806.1993828](https://doi.org/10.1145/1993806.1993828) (journal version: Distributed Computing
26:309–320, 2013). Formalized version: Chapter 4 of G. Rétvári's D.Sc. dissertation (Hungarian Academy of
Sciences, 2020, [open access](https://real-d.mtak.hu/1294/8/dc_1738_20_doktori_mu.pdf)), which reproduces the
PODC paper with proofs for *delimited* algebras; no open copy of the PODC or journal version was found. Numbering
follows the thesis (Definition 4.1 … Theorem 4.17). The chapter's contribution list (algebraic compact routing,
sublinear-memory characterization, generalized stretch, no constant-stretch scheme for some policies) matches the
journal abstract, but the chapter draws on [175, 176] and two later papers; the mistakes below are in the thesis text
and may be worded differently in the PODC version. The paper's results on non-delimited (BGP) algebras are only
referenced there and were not checked.

**Verdict: 🔧 Easy fix.** All the paper's own theorems hold, mostly with simple proofs. The cited results
(Fraigniaud–Gavoille incompressibility, tree routing, Cowen's landmark selection) are hypotheses. One claim fails as
stated: the generalized Cowen scheme (Theorem 4.14) can need linear-size tables, because of how its balls are
defined. A tie-breaking key fixes it. The stretch-3 routing, the lower bound of Theorem 4.17 and the remaining
proof gaps are all repaired in Lean.

## Mistakes in the paper

### 🔧 Theorem 4.14 (memory of the generalized Cowen scheme)
With the paper's balls `B(u) = {v : w(p*_{uv}) ⪯ w(p*_{u,l_u})}`, the routing tables can hold all `n` nodes,
whatever the landmark set. Example: widest-path routing (delimited, regular, selective) with all edge weights equal
(`paperScheme_table_eq_univ`, `paperScheme_card_table`).

**Impact.** The claimed `O(n^{2/3})` local memory does not follow for the scheme as defined. Stretch 3 and delivery
do hold. The existential statement of Theorem 4.14 is not refuted (in the counterexample, tree routing works); the
flaw is in the scheme of the proof. Once ties are broken by a strict key the tables have the expected structure, and Cowen's landmark selection
(cited, not formalized) applies.

**Details.** With equal weights every preferred weight between distinct nodes is the same, so every node lies in
every ball. Cowen's memory bound needs each ball to be the set of nodes strictly before the first landmark in a
*strict* total order. A plain strict inequality does not help: with non-strict monotonicity the node after `l_v` on
the way to `v` may not be strictly closer to `v`, so it sends the packet back to `l_v`. On the path `0–1–2` with
the bottleneck algebra and `L = {0}` the packet bounces between `0` and `1` forever (`strictBall_loops`). The text
hints at "lexicographic lightest-path algorithms … to obtain unique connected clusters" but gives no definition.

**Repair.** Order nodes for destination `v` by the key `(w(p*_{x,v}), rank of x in the in-tree to v, x)`. Then
the next hop always has a smaller key, routes are paths within stretch 3 (`theorem_4_14`), and each table is
`C(u) ∪ L`. Each ball lies inside the set of nodes whose key is below every landmark's key
(`refinedBall_subset`); this is the input of Cowen's selection.

### ✏️ Slips
- Definition 4.3: (SM), (N) and (C) quantify over `φ` as well, which makes them unsatisfiable or degenerate
  (`φ ≺ w ⊕ φ = φ` is false). They must exclude `φ` (`not_isStrictlyMonotoneLit`, `not_isCancellativeLit`,
  `isCondensedLit_iff`).
- Proof of Lemma 4.12: "every cyclic subsemigroup is of infinite order" fails for `w = φ`. Lemma 4.12 and
  Theorem 4.11 need a finite weight, since the algebra `{φ}` is delimited and vacuously strictly monotone but needs no
  routing memory (`trivial_algebra`).
- Proposition 4.4: the product as written, on `W_A × W_B` with `φ = (φ_A, φ_B)`, is not delimited
  (`litProd_not_isDelimited`), and its monotonicity rule fails at elements `(φ_A, b)` (`litProd_not_isMonotone`).
  The intended product is on the finite parts, as the text's "all link weights are finite" suggests, and there all
  three rules hold (`lexProd_isMonotone_iff`, `lexProd_isIsotone_iff`, `lexProd_isStrictlyMonotone_iff`).
- Table 4.2 lists most-reliable path `R = ((0,1], 0, ∗, ≥)` as SM, but `w ⊕ 1 = w`
  (`mostReliable_not_isStrictlyMonotone`). Only its subalgebra on `(0,1)` is SM (`mostReliableOpen_props`), as the
  text itself says.
- Table 4.2 lists MRWS `= R × WS` as ¬I, but it is isotone (`mostReliableWS_isIsotone`; `R` is cancellative). The text
  says only the last row is non-isotone.

### Typos
- Section 4.3.2: "Theorem 4.12" should be "Lemma 4.12". "Hence, for R and WS … Theorem 4.11 supplies Ω(n)" should
  cite Lemma 4.12 for `R`, which is not itself strictly monotone.

## Proof gaps (statements true)

### 🔧 Lemma 4.10 (converse: maps to a tree ⇒ monotone and selective)
The non-monotone case is dismissed with "obviously … the preferred paths might contain loops", but preferred paths
are paths by definition.

**Impact.** Statement true, even without the delimitedness hypothesis (`lemma_4_10_converse`, `mapsToTree_iff`).

**Details.** If `w₂ ⊕ w₁ ≺ w₁`, take the triangle with weights `w₁, w₂, w₁`. Every spanning tree has a tree path
that a two-hop path strictly beats (`not_mapsToTree_of_not_monotone`). The paper's Fig. 4.1a and 4.1b triangles do
not need delimitedness either (`not_mapsToTree_of_lt_op_self`, `not_mapsToTree_of_lt_op`). Its case (c)
("`w₁ = w₂` and `w₁ ⊕ w₂ ≻ w₂`") is case (a) again.

### 🔧 Theorem 4.14 (stretch 3 of the generalized Cowen scheme)
Lemma 4.16 bounds only the pure landmark route `u → l_v → v`. The real route goes towards `l_v` until the first node
that stores `v`, then follows that node's table, and the proof never analyses it.

**Impact.** Statement true; repaired (`Scheme.delivers`, `theorem_4_14`).

**Details.** For the mixed route, `w(u..x) ⊕ w(p*_{x,v}) ⪯ w(u..x) ⊕ w(p*_{x,l_v}) ⊕ w(p*_{l_v,v}) =
w(p*_{u,l_v}) ⊕ w(p*_{l_v,v}) ⪯ w(p*_{u,v})³`. This needs next hops that are consistent along in-trees. Subpaths of
preferred paths need not be preferred when `A` is not strictly monotone, so the in-trees are built with a Dijkstra
argument (`exists_isHO`, `exists_inTree`). The paper delegates this step to Sobrinho [191, 192].

### 🔧 Theorem 4.17 (the counting of [73])
The graph family as described, with exactly `δ^p` targets carrying distinct words, is a single graph up to
isomorphism, not "`2^{Θ(n²)}` different graphs". In the model of §4.2 the scheme chooses node labels, so a target's
label can carry its word, and this family cannot force `Ω(n)` bits.

**Impact.** Statement true; proved with a family of `p ≈ n/4` centres, `δ = 2` and `q ≈ n/4` targets with
arbitrary words (`theorem_4_17`).

**Details.** The paper's own step is correct: by monotonicity and (4.2), every `c_i – t` path other than the
two-hop one weighs more than `w_i^{2k}` (`Family.weight_gt_of_two_lt_length`). So any stretch-`k` routing function
sends a packet from `c_i` to `t` towards `z_{i, word_i(t)}` (`Family.route_eq_of_implementsStretch`). Counting
(`card_bound`) then gives `2^{pq} ≤ (n^c)^q · 9^p · 2^{bp}`, hence local memory `b ≥ n/8` for large `n`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Static routing: finite connected simple undirected graphs, edge weights `wt : Sym2 V → W` in a routing algebra
  `(W, φ, ⊕, ⪯)`, given as `RoutingAlgebra` with `⪯` the ambient linear order. A walk's weight is the `⊕` of its edge
  weights, computed in `A.Ext = W ∪ {1}`. A preferred path is a minimum-weight *path*.
- Routing functions follow §4.2: injective node labels below `n^c` (`c log n` bits), local ports
  `1..δ(u)` (both chosen by the scheme), local functions `R_u : header ↦ (header, port)`, initial header `L_V(t)`.
  `Implements` asks for a generated preferred path for every pair joined by a traversable path. `ImplementsStretch k`
  asks for a generated path within stretch `k`; routes must be paths.
- Memory: an arbitrary measure `mem : (ℕ → ℕ × ℕ) → ℕ∞`, since the paper does not fix an encoding. `memReq` is
  Definition 4.5, with the maximum also ranging over edge weights. Incompressible means `M_A(n) = Ω(n)`, and
  compressible is its negation, as in the paper. The counting in Theorem 4.17 assumes `CodeLength mem`: fewer than
  `2^b` functions have code length `< b`. This forces `mem f = ⊤` for some `f`, since there are uncountably many
  local functions (`not_codeLength_of_ne_top`), hence the values in `ℕ∞`.
- Cited results are hypotheses: Proposition 4.8 (Fraigniaud–Gavoille, shortest-path routing is incompressible) and
  tree routing with `O(log n)` bits ([74], `TreeRoutingScheme`). `treeRoutingScheme_zero` constructs tree routing in
  the model, so the latter is consistent.
- Theorem 4.14's scheme is modelled as table-based forwarding: a node's table is a set of destinations with next
  hops, and the header is `(v, l_v, next hop of l_v towards v)`. It is not encoded in the bit-level model above.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 4.1–4.3 | `RoutingAlgebra`, `IsMonotone`, `IsIsotone`, `IsRegular`, `IsDelimited`, `IsStrictlyMonotone`, `IsSelective`, … | `Algebra.lean` |
| Proposition 4.4 | `lexProd_isMonotone_iff`, `lexProd_isIsotone_iff`, `lexProd_isStrictlyMonotone_iff` (and `OrdSemigroup.lex_*`) | `Product.lean` |
| Definition 4.5 | `memReq`, `Incompressible`, `Compressible` | `Routing.lean` |
| Lemma 4.10 | `lemma_4_10_mapsToTree`, `exists_preferred_spanningTree`, `lemma_4_10_converse`, `mapsToTree_iff` | `Tree.lean` |
| Theorem 4.9 | `theorem_4_9`, `theorem_4_9_compressible` | `Compressibility.lean` |
| Lemma 4.12 | `lemma_4_12_memReq` (`M_S ≤ M_A`), `lemma_4_12`, `powEmbedding`, `AlgEmbedding.memReq_le_memReq` | `Compressibility.lean`, `Routing.lean` |
| Theorem 4.11 | `theorem_4_11` | `Compressibility.lean` |
| Table 4.2 | `shortestPath_props`, `widestPath_props`, …, `widestPath_compressible`, `shortestWidest_incompressible` | `Product.lean`, `Compressibility.lean` |
| Definition 4.13 | `IsWithinStretch`, `ImplementsStretch` | `Paths.lean`, `NoStretch.lean` |
| Lemmas 4.15, 4.16 | `lemma_4_15`, `lemma_4_16`, `lemma_4_16_paper` | `Cowen.lean` |
| Theorem 4.14 | `theorem_4_14`, `Scheme.delivers`, `refinedBall_subset`, `card_table_le` | `Cowen.lean` |
| Theorem 4.17 | `theorem_4_17`, `Family.route_eq_of_implementsStretch`, `card_bound` | `NoStretch.lean` |
| §4.4.2, shortest-widest path | `shortestWidest_condition_4_2`, `shortestWidest_no_compact_stretch` | `Product.lean`, `Compressibility.lean` |

Remarks: (4.2) is incompatible with monotone and isotone algebras already for `k = 1`; the paper says `k ≥ 2`
(`not_condition_4_2_of_regular`). Delimitedness is used nowhere: not in Lemma 4.10's converse, Theorem 4.14 or
Theorem 4.17.

**Not formalized.** The cited results above: Proposition 4.8, tree routing [74], and Cowen's landmark selection
giving `|C(u)| + |L| = O(n^{2/3})`. Also Proposition 4.6 / Observation 4.7, except that `exists_inTree` is the
regular ⇒ destination-based direction. The non-delimited (BGP) results, which the thesis only references, were not
checked.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `treeRoutingScheme_zero` (tree routing exists in the model), `shortestWidest_condition_4_2` ((4.2) is
satisfiable), `codeLength_top` and `incompressible_memReq_top` (the `CodeLength` and Proposition 4.8 hypotheses
are satisfiable), `paperScheme_card_table_path3` and `strictBall_loops` (concrete instances), and `trivial_algebra`.
Graph theory comes from Mathlib and CSLib's greedy spanner (`IsGreedySpanner.forall_walk`, used for the
cycle-property spanning tree `exists_isTree_forall_walk`).
