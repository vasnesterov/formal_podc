# LCLs on Trees Without Knowledge of n — PODC 2026

Alkida Balliu, Sebastian Brandt, Fabian Kuhn, Dennis Olivetti, Timothé Picavet, Gustav Schmid. *The
Distributed Complexity Landscape on Trees Depends on the Knowledge About the Network Size.* PODC 2026.
DOI [10.1145/3796701.3815947](https://doi.org/10.1145/3796701.3815947). Formalized version: arXiv
[2605.12787](https://arxiv.org/abs/2605.12787) v1; numbering follows it.

**Verdict: 🛠️ Proof repaired.** Theorem 1 holds as stated: if the nodes know nothing about `n` and IDs
are arbitrary natural numbers, `k`-hierarchical 2½-colouring needs `Ω(n)` rounds for every `k ≥ 1`.
The paper's induction has a gap: the parity surgery needs the induction hypothesis in the modified
graph `Ĝ`, but the hypothesis is stated only for the lower bound graph `G`. We repaired this by
running the induction over a class of graphs that is closed under the surgery.

## Mistakes in the paper

* **Proof of Theorem 1, property 4: the induction hypothesis is applied in a graph where it was not
  proved.** The induction claims properties 1–4 "by running `A` on `G`", where `G` is the
  `k`-hierarchical lower bound graph. To show property 4 for a level-`i` path, the proof removes a
  path node `z` (with its subtree) and joins its two neighbours. This gives `Ĝ`. Then `u` and `v`
  keep their colours, but the parity of their distance changes, "thus the produced 2-colouring cannot
  be proper". That step needs the `u`–`v` path to be properly 2-coloured in `Ĝ`, and hence needs
  that no node on it outputs `E`. Constraint 4 rules out `E` only if all lower-level neighbours
  output `D` *in `Ĝ`*. The algorithm is run afresh on `Ĝ`, and `Ĝ` is not a `k`-hierarchical lower
  bound graph (one level-`i` path is one node short), so the induction hypothesis says nothing about
  it. Lower-level nodes next to the cut can see the change. The statement is true, and the repair is
  routine once identified: prove the claim for every level-`j` component of the lower bound graph
  embedded in *any* tree of a suitable class (a "host"). The class must be closed under the surgery
  and the levels of the 2½-colouring problem must stay the designed levels in it (`claim`,
  `hostOK_hat`, `emb_hat_child`).
* **Small slips in the same proof** (no effect on the result):
  * `T_i = ℓ_i/10` need not be an integer. The proof uses "distance exactly `T_i + 1`" and round
    counts `≤ T_i`; we use `⌊ℓ_i/10⌋`.
  * Property 2 ("`u`, `v` at distance at least `2T_i + 1`") does not guarantee a node `z` at
    distance `> T_i` from both. The chosen `u`, `v` (at distance `T_i + 1` from the two ends) are
    about `0.8 ℓ_i` apart, so such a `z` exists.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic synchronous LOCAL model on finite trees. A network (`Inst`) is a finite tree whose
  nodes *are* natural numbers: the node names are the unique identifiers. There is no bound on the ID
  space, and no other input; in particular `n` is unknown.
* An algorithm (`Alg`) is given extensionally by the round `time I v` in which node `v` stops and
  its output `out I v`. Locality (`Alg.IsLocal`): whether `v` has stopped by round `t`, and its
  output if so, depend only on the edges incident to nodes at distance `≤ t` from `v` (CSLib
  `Cslib.Local.GAgree … (t+1)`). This is one hop *more* than a node learns in `t` LOCAL rounds, so
  more algorithms are local and the lower bound is (slightly) stronger. Per-node termination is
  modelled, as in the paper.
* `k`-hierarchical 2½-colouring is defined as in Section 2.3: levels by iterated removal of nodes of
  degree `≤ 2` (`levelSet`, `InLevel`), outputs `B, W, E, D`, constraints 1–4 (`IsHierColoring`).
* `Ω(n)` is Knuth's: there are `ε > 0` and `n₀` such that for every `n > n₀` some `n`-node tree has a
  node that runs for `≥ εn` rounds. The algorithm only has to be correct on trees of maximum degree
  `≤ Δ`, for any `Δ ≥ 3`. The hard instances have maximum degree 3.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 | `theorem1` | `Theorem1.lean` |
| Induction of the proof (properties 3, 4), for all hosts | `claim`, `claim_step` | `Theorem1.lean` |
| Property 3 (padding to `N_i` nodes, graph `G''`) | `time_le_of_pad`, `padTree` | `Padding.lean` |
| Parity surgery (graph `Ĝ`) | `hatTree`, `hostOK_hat`, `emb_hat_child`, `gAgree_hat` | `Surgery.lean` |
| Definition 16 (lower bound graph) | `comp`, `topTree` | `Construction.lean`, `Embedding.lean` |
| Observation 17 (upper bound, `c₂ = 3^k`) | `card_comp_le` | `Construction.lean` |
| Levels of the lower bound graph = path levels (implicit in the paper) | `levelSet_eq`, `inLevel_iff`, `hostOK_top` | `Trees.lean`, `Embedding.lean` |
| Observations on 2½-colourings of paths (Section 2.3) | `alternation` | `Theorem1.lean` |
| "`O(n)` is a trivial upper bound" / non-vacuity | `fullAlg`, `theorem1_hyps_satisfiable` | `NonVacuity.lean` |

Proof structure: Definition 16 is encoded with explicit identifiers (`Nat.pair`). Trees are given by
parent pointers with a decreasing rank (`RTree`, proved to be trees with CSLib
`isAcyclic_of_rank`), so the surgeries `G''` and `Ĝ` are pointwise changes of the parent function.
A *host* is a rooted tree with a level labelling `hl` satisfying local degree conditions
(`HostOK`). By `levelSet_eq`, the problem's levels in a host are then `hl`. A component is placed in
a host by an injective renaming of IDs (`Emb`). Distances are bounded below by a 1-Lipschitz
potential, the position along the path (`pot_le_of_edist`, `Emb.pos_close`).

**Not formalized.** Theorem 2 (`k`-rake-and-compress, `Ω(n)`). Its proof is only sketched
("similarly as in the proof of Theorem 1, we can modify `G` and create `Ĝ`…") and we did not find a
direct adaptation. Unlike a 2-colouring, an orientation towards a single sink *can* be locally
consistent: for example, on a path with increasing IDs, every node can point to its larger-ID
neighbour. So property 1 needs an argument the paper does not give. Theorems 3–7 and Section 7
(polynomial bound on `n`, bounded IDs, randomized) are out of scope. Their upper bounds rest on
cited decompositions.

**Trust.** No `sorry`. `theorem1` and `theorem1_hyps_satisfiable` use only `propext`,
`Classical.choice`, `Quot.sound`. The hypotheses of `theorem1` are satisfiable: `fullAlg` (wait for
eccentricity many rounds, then output a fixed solution) is local and correct on every tree. LOCAL
views come from CSLib `Cslib.Computability.Distributed.Local.Locality` (`GAgree`).

**CSLib candidates** (marked `-- CSLib candidate`): `RTree` with `RTree.isTree` (finite trees on
`ℕ` by parent pointers; compare `Podc/Foundations/Combinatorics/SimpleGraph/ParentGraph.lean`),
`levelSet_eq`/`inLevel_iff` (levels of hierarchical 2½-colouring from a level labelling), and
`pot_le_of_edist` (distance lower bound from a 1-Lipschitz potential).
