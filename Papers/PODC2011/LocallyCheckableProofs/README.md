# Locally Checkable Proofs — PODC 2011

Mika Göös, Jukka Suomela. *Locally Checkable Proofs.* PODC 2011. DOI
[10.1145/1993806.1993829](https://doi.org/10.1145/1993806.1993829). Formalized version: the journal version
*Locally Checkable Proofs in Distributed Computing*, Theory of Computing 12(19), 2016 (33 pp., full proofs);
numbering follows it.

**PODC 2011 version vs. journal version.** The PODC version (authors' copy:
[lcp-podc.pdf](https://jukkasuomela.fi/doc/lcp-podc.pdf)) has no numbered theorems; its results are stated in
the text. Its §5 (the `Θ(log n)` results and the gluing proof), §6.1–6.2 (symmetric graphs, fixed-point-free
symmetric trees) and §7.3 (`coLCP(0) ⊆ LogLCP`) make the same claims as the journal's Theorem 5.1, Theorems 6.1
and 6.3, and §7.3, with the same proofs. The only differences are the identifier layout of the cycles `C(a,b)`
(identifiers up to about `n² + 3n` instead of `n²`; both are polynomial) and an even shorter 6.1 step
("if `G₁`, `G₂` are not isomorphic, `G` must be asymmetric", with no argument). The journal's Theorem 7.1
(properties closed under lifts, port-numbering verifiers) is **not** in the PODC version. We formalized it, but
it does not count towards the verdict for the PODC paper.

**Verdict: ✅ Correct.** Every checked statement is true as written, and the paper's proofs go through. We
formalized:

* the `Ω(log n)` gluing lower bound (Theorem 5.1) for odd `n`, non-bipartiteness, leader election, spanning
  trees and maximum matchings on cycles, together with the matching `O(log n)` spanning-tree schemes of §5.1;
* the `Θ(n²)` bound for symmetric graphs (Theorem 6.1) and the `Θ(n)` bound for trees with a fixed-point-free
  symmetry (Theorem 6.3);
* `coLCP(0) ⊆ LogLCP` (§7.3) and the colouring upper bounds of §2;
* Theorem 7.1 (properties closed under lifts) with its converse (journal version only).

A few proof steps are only sketched and a few details are imprecise. None of them affects a statement.

## Mistakes in the paper

No statement is wrong. Imprecisions and sketched steps, all repaired or confirmed in Lean:

* **Theorem 5.1, gluing step.** The text adds the edges `{b_{i-1}[1], a_i[1]}` "for each `i > 1`". This
  produces a path, not a `kn`-cycle. The definition `b_0 = b_k` and Figure 1c show that every `i` is meant.
  This is a typo. (`glued`)
* **Theorem 5.1, graph problems with edge labels.** The glued instance inherits only node data `L(v)` and
  `P(v)`. For spanning trees and matchings the solution lives on edges, and the paper does not say what
  label the new edges `{b_{i-1}[1], a_i[1]}` get. We store the label of the edge to a node's successor at that
  node, so a new edge inherits the label of the removed edge `{a_i[1], b_i[1]}`, and we put these labels into
  the colour `c(a,b)`. The argument then works as the paper says, and the lower bound holds for weak schemes
  too. (`glue_accept`, `theorem_5_1_spanningTree`, `theorem_5_1_maxMatching`)
* **Theorem 6.1.** The paper says that "by the construction of `G`" every non-trivial automorphism of
  `G₁ ⊛ G₂` swaps `G₁` and `G₂`, and gives no argument. This is true in general, with a short argument (checked
  on paper, not in Lean). The connecting path lies in a run of degree-2 nodes with at least `k` nodes. Every
  other such run lies inside one copy and has fewer than `k` nodes. So `ϕ` fixes or reverses this run. If it
  reverses the run, the two sides have equal size, and `ϕ` maps the `G₁` copy onto the `G₂` copy. If it fixes
  the run, it restricts to automorphisms of `G₁` and `G₂`, which are trivial. We sidestep the step with a smaller family of `G₁`: asymmetric graphs in which any two
  vertices have three common neighbours. In `G₁ ⊛ G₂` the degree-2 nodes are then exactly the path nodes. We
  prove that this family still has at least `2^{C(k,2)}/2` labelled members, replacing the citation of
  Erdős–Rényi. (`symmetric_lcp_lower_bound`, `exists_many_good`)
* **Theorem 7.1.** The honest proof is described as `P(v) = (H, v)`, but the encoded graph must have
  identifiers `{1, …, n(G)}`. One has to use a relabelled copy of `H`, which lies in `P` because isomorphisms are
  coverings. Also left implicit: surjectivity of `ϕ` needs the encoded graph to be connected, which the check
  `G ∈ P ⊆ F` provides. (`theorem_7_1`)
* **Odds and ends.**
  * Table 2 lists `Θ(log n)` for verifying a Hamiltonian cycle, but §5 gives no lower-bound argument for it. The
    cycle gluing does not apply: the glued all-marked `2n`-cycle is a Hamiltonian cycle. Not formalized.
  * §5.1 certifies non-bipartiteness by a counter "along the odd cycle". It certifies only an odd closed walk,
    which also rules out a 2-colouring. Our scheme uses two BFS-like trees instead (`nonBipartite_logLCP`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic, synchronous LOCAL verification with unique identifiers. Nodes *are* their identifiers: an
  instance `Inst L` is a `Finset ℕ` of nodes, a graph on `ℕ` with edges between nodes, marked edges `S ≤ G`
  (0/1 edge labels, for graph problems) and node labels `lab : ℕ → L`.
* Proofs are bit strings `ℕ → List Bool`, and the proof size is the maximum length.
* A verifier with horizon `r` is any function whose output at `v` depends only on the induced radius-`r` view:
  the ball `V[v,r]`, the induced edges and marked edges, labels and proof labels (`IsLocal`). This is
  equivalent to the paper's `A(G,P,v) = A(G[v,r],P[v,r],v)`. There are no computability or resource limits
  (Remark 2.1).
* `AdmitsLCP F P s` is Definition 2.2. Graph problems also come in a weak version, `AdmitsWeakLCP`, where the
  scheme may choose the solution.
* Lower bounds are stated for every family that contains the needed instances, and use the smallest identifier
  ranges the constructions need. Theorem 5.1 needs cycles with identifiers in `{1,…,n²}`; Theorems 6.1 and 6.3
  need identifiers in `{1,…,n}`. Upper bounds use families with identifiers in `{1,…,n^c}`.
* For unlabelled graph properties the family contains only unmarked instances (`Plain`), so the lower bounds
  are not weakened by extra instances.
* Port-numbering verifiers (§7.1) are modelled conservatively: the output depends on the node's own label and
  the multiset of its neighbours' labels (`IsPN`). This is a sub-class of PN algorithms, so Theorem 7.1 with
  it is stronger.
* `Ω`/`o` claims are stated as explicit inequalities `s(n) ≥ c·log n − C`, `s(n) ≥ c·n²`, `s(n) ≥ c·n`, plus
  `¬ s =o(…)`. The constant `c` depends on the horizon `r`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.2, weak/strong schemes (§2.3) | `AdmitsLCP`, `AdmitsWeakLCP`, `AdmitsLCP.weak`, `IsLocal` | `Basic.lean` |
| §2.2: bipartite ∈ LCP(1); χ ≤ k ∈ LCP(⌈log k⌉) | `bipartite_admitsLCP_one`, `colorable_admitsLCP` | `Coloring.lean` |
| §5.3: gluing argument | `glue_accept`, `lowerBound_core`, `lowerBound_bound` | `Gluing.lean`, `LowerBoundCore.lean`, `Theorem51.lean` |
| Thm 5.1: odd `n`, non-bipartite, leader election | `theorem_5_1_oddNodes`, `theorem_5_1_nonBipartite`, `theorem_5_1_leader` | `Theorem51.lean` |
| Thm 5.1: spanning trees; §5.4 max. matching on cycles | `theorem_5_1_spanningTree`, `theorem_5_1_maxMatching` | `Theorem51Edges.lean` |
| §5.1: spanning-tree certificate (KKP) | `TreeOK`, `treeOK_sound`, `treeOK_complete`, `count_root` | `SpanningTree.lean` |
| §5.1: leader election, spanning tree, acyclic, odd `n`, non-bipartite ∈ LogLCP | `leaderElection_logLCP`, `spanningTree_logLCP`, `acyclic_logLCP`, `oddNodes_logLCP`, `nonBipartite_logLCP` | `LogLCP.lean` |
| Tables 1–2: `Θ(log n)` entries | `nonBipartite_theta`, `oddNodes_theta`, `leaderElection_theta`, `spanningTree_theta` | `Summary.lean` |
| §6: any property of connected graphs in `O(n²)` | `Universal.universal_upper` | `Universal.lean` |
| Thm 6.1 (symmetric graphs `Ω(n²)`), Table 1 `Θ(n²)` | `symmetric_lcp_lower_bound`, `symmetric_not_isLittleO`, `symmetric_theta` | `Symmetric.lean`, `Summary.lean` |
| §6.2: any tree property in `O(n)` | `Trees.tree_upper`, `Trees.tree_upper_idBound` | `TreeUpper.lean` |
| Thm 6.3 (FPF-symmetric trees `Θ(n)`) | `fpf_tree_lcp_lower_bound`, `fpfTree_theta` | `FPFTrees.lean`, `Summary.lean` |
| §7.1: PN verifiers are fooled by lifts | `Lifts.IsPN.fooled`, `Lifts.closedUnderLifts_of_admitsPNLCP` | `Lifts.lean` |
| Thm 7.1 (journal only) | `Lifts.theorem_7_1`, `Lifts.theorem_7_1_idBound`, `Lifts.closedUnderLifts_iff_admitsPNLCP` | `Lifts.lean` |
| §7.3 (`coLCP(0) ⊆ LogLCP`; unnumbered) | `coLCP0_logLCP` | `CoLCP0.lean` |

Supporting files: `Cycle.lean` (labelled cycles and the segment gluing lemma), `Star.lean` (the `⊛`
construction), `AsymCount.lean` (counting asymmetric graphs), `LocalTools.lean` (bit encodings of numbers).

**Not formalized.**
* §4: reachability, connectivity, bipartite matching.
* Theorem 6.4 (non-3-colourability `Ω(n²/log n)`). Its fooling-set step is elementary, but the 3-colouring
  gadgets are not formalized.
* Theorem 7.2 (alternative characterizations of LogLCP); §7.4–7.5.
* The `LCP(0)` membership claims; the `O(log n)` upper bound for maximum matching on cycles (Table 2);
  the Hamiltonian-cycle entry of Table 2 (unchecked: no argument is given for its lower bound).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Every lower-bound theorem is paired with a matching upper bound (`*_theta`), so its hypotheses are
  satisfiable.
* The yes-instances used by the gluing arguments are constructed explicitly: odd cycles, spanning paths,
  alternating matchings, the `⊛` graphs.
* Everything is self-contained on top of Mathlib and `Cslib.Foundations.Data.List.BitEncoding`.
* CSLib candidates, marked `-- CSLib candidate` in the code:
  * `exists_mono_rect`: monochromatic `C₄` in a few-coloured `K_{α,β}`.
  * The counting lemmas in `AsymCount.lean`.
  * `isAcyclic_of_unique_lt_adj`, `isPath_map_of_locInj`, `isAcyclic_of_hom_injOn`.
  * The encodings `natCode`, `sbEnc`.
