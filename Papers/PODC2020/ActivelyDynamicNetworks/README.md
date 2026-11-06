# Actively Dynamic Networks — PODC 2020

Othon Michail, George Skretas, Paul G. Spirakis. *Distributed Computation and Reconfiguration in
Actively Dynamic Networks.* PODC 2020. DOI
[10.1145/3382734.3405744](https://doi.org/10.1145/3382734.3405744). Formalized version: arXiv
[2003.03355](https://arxiv.org/abs/2003.03355) v1 (full version with Appendices A–D); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** **Lemma 3.1 is false for GraphToStar as printed**: on the 4-node
line with increasing IDs a pulling committee jumps onto a committee that is merging away in the
same phase, it then merges into a follower, the committees stop being stars, and the output is not
a spanning star. So Theorem 3.8 for GraphToStar, the first of the three distributed algorithms announced in the
abstract, is not established, and neither is the distributed `Ω(n log n)` bound (Theorem 6.4). The basic subroutines
(Propositions 2.1, 2.2, up to a small slip in the bound `⌈log d⌉ ≤ log n`), the centralized lower bounds
(Lemmas 6.1, 6.2) and the matching centralized upper bound on the line (Theorem 6.3, line case) hold and are proved,
while the other two algorithms (Sections 4–5) were not checked.

## Mistakes in the paper

### ❌ Lemma 3.1 (GraphToStar solves Depth-1 Tree), hence Theorem 3.8
On the line `0 - 1 - 2 - 3` with IDs increasing along the line, a pulling committee jumps onto a committee that
is merging away in the same phase, the committees stop being stars, and the output is not a spanning star
(`GraphToStar.lemma_3_1_breaks`, `line4_terminates_wrong`).

**Impact.** Theorem 3.8 (`O(log n)` time, `O(n log n)` activations for GraphToStar), the first of the three
distributed algorithms announced in the abstract, is not established. The bug needs only a pulling chain of
length 3, so it occurs on most inputs: it showed up in about 9% of random connected graphs with up to 9 nodes in
our committee-level simulator.

**Details.**
- Phase 1: every committee selects its right neighbour. `C(2)` pairs with `C(3)` and enters *merging*. `C(1)` and
  `C(0)` selected committees that themselves selected, so they enter *pulling*. `C(3)` was selected and enters
  *waiting*.
- Phase 2: by the pulling rule, `C(1)` jumps to `3`. `C(0)` jumps to `2`, the leader `C(1)` activated an edge with
  in phase 1. But in the same phase `C(2)` merges into `C(3)`, so node `2` is now a follower of `3`.
- Phase 3: "the leader of `C(2)`" did not activate an edge in phase 2, so `C(0)` enters merging.
- Phase 4: `C(0)` merges into node `2`.

Now node `0`'s leader is `2`, whose leader is `3`. The committee invariant ("each committee is a star around its
maximum-ID leader") is broken, and the network is not a spanning star (`0` hangs at distance 2 from `3`). In
phase 5 `C(3)`, now the only committee, enters termination mode while `0` is still attached only to `2`: no rule
ever connects `0` to `3`. The proof's claim that a pulling tree "executes TreeToStar on committees … `C_r`'s
children merge with `C_r` and their children become the new children of `C_r`" overlooks that in TreeToStar no
vertex disappears. Here a depth-3 committee jumps onto a depth-1 committee that is dissolving in the same phase.

**Repair.** When the target merges away, redirect the pointer to the absorbing leader (a potential neighbour
through the former leader, so this costs one extra round). In simulation this repair terminated in
`≈ 2–3 log₂ n` phases on all tested inputs (lines, trees and random graphs, up to 256 nodes). We did not prove
it, so Theorem 3.8 remains unproved.

### ❌ Lemmas 3.2–3.7 (time analysis of GraphToStar)
The time analysis is not a proof: it refers to the broken invariant above, and its formulas and indices are
garbled.

**Impact.** Unestablished and not formalized, so the `O(log n)` time is not saved even for a repaired algorithm. Its
status is unknown, not refuted.

**Details.**
- Lemma 3.2's size formula writes `S(C(u_{s+log i}))` and sums `2^{log(i-1)}` terms equal to `2^{k+i}`, which gives
  about `j·2^k` rather than `2^{k+j}`.
- Lemmas 3.4/3.5 have inconsistent indices (`2^{k+p-4}` vs `2^{k+p-3}`, "phase `p+1`" vs "`s+p+1`").
- Lemma 3.7's "each phase has ≤ 2 rounds" ignores the communication a leader needs to learn its neighbouring
  committees' IDs and modes.

### ❌ Theorem 6.4 / D.12 (distributed `Ω(n log n)` activations)
The proof is a sketch: several notions are undefined or garbled, and its final sum evaluates to "`= Θ(log n)`".

**Impact.** Unestablished, so the "optimal" total of `O(n log n)` activations has no matching bound; the symmetry
argument is plausible but not formalized, and the theorem is not refuted.

**Details.** Undefined or garbled: "corresponding states" (Def. D.7), `i_min`/`i_max` in Lemma D.11, and the
"previous proof" giving `k − log k` rounds. Observation 2 has no proof. The bound concerns *comparison-based*
algorithms on increasing-order rings (stated in §2.1, not in the theorem).

### 🔧 Observation 1 / Lemma D.2 (distance bound off by a factor 2)
"Depth-`log n` tree ⇒ `PO_{u,v} ≤ log n`" should be `2 log n`: two leaves are at distance up to twice the depth.

**Impact.** Bookkeeping only: the bounds of Lemmas 6.1 and 6.2 survive (`lemma_6_1`, `lemma_6_2_total`).

**Details.** The argument mixes information propagation with distances, but the bounds survive with a cleaner
proof: one round at most halves any distance, and each activated edge shortens a distance by at most one.

### ✏️ Slips
- Proposition 2.1 ("`⌈log d⌉ ≤ log n` rounds"): TreeToStar takes exactly `⌈log₂ d⌉` rounds (proved), and on the line
  with `n = 6` nodes, `d = 5`, it needs `3 > log₂ 6` rounds (`ceil_log_depth_le_log_false`, `line6_not_star_two`). So
  `⌈log₂ d⌉` can exceed `log₂ n`, but the bound holds with `⌈log₂ n⌉`.
- Proof of Prop. A.1: "`O(log n)` total edge activations" should be `O(n log n)`.

### Typos
- Prop. 2.2 states maximum degree 3, while its proof and §2.3 say "at most 4". In every snapshot the degree is
  `≤ 3` (proved). The value 4 only appears in the middle of a round, after the activations and before the
  deactivations.

## Proof gaps (statements true)

### 🔧 CutInHalf (App. D.1, Theorem 6.3 / D.5)
CutInHalf only activates edges, so its output is not a tree, although the target is a Depth-`log n` tree.

**Impact.** It becomes one after the deactivations we add, which are free; we prove this for the line
(`CutInHalf.theorem_6_3_line`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The **actively dynamic network** (§2.1) is `Cslib.DynNet.Active` in
  `Podc/Computability/Distributed/DynamicNetworks/ActivelyDynamic.lean`. Snapshots are
  `E : ℕ → SimpleGraph V`. A round is valid (`ValidRound`) iff every new edge joins two nodes with
  a common neighbour at the start of the round; deactivations are free. `validRound_iff` proves
  this equals the paper's `E(i+1) = (E(i) ∪ E_ac) \ E_dac`, with activations only between potential
  neighbours. `numActivated`/`totalActivations` are `|E_ac(i)|` and their sum. The network is
  synchronous and deterministic, with no failures and unique IDs.
* **Lower bounds (Lemmas 6.1, 6.2)** quantify over *all* executions of the model, i.e. every
  centralized strategy, on the spanning line. They only need the final snapshot to have radius
  `≤ d` around some node; the paper's "rooted tree of depth `d`" (`IsDepthTree`) is a special case.
* **Subroutines (Props. 2.1, 2.2)** are modelled by their global effect. Nodes know their parent
  (orientation). A moving node activates the edge to its grandparent and deactivates the one to its
  parent, so a round is a *pointer jump* `jump P S` of the parent map (`PointerJumping.lean`). We
  prove this is a valid round of the model. For TreeToStar the mover set is "parent ≠ root", so
  after `t` rounds the parent is `parent^[2^t]`. For LineToCompleteBinaryTree it is "parent ≠ root
  and grandparent has < 2 children", with the closed form `i ↦ i − 2^{min(t, kk i)}`
  (`LineArith.lean`). The message exchange needed to learn the grandparent and its number of
  children is not modelled: it fits in the same round.
* **GraphToStar** is modelled at the committee/phase level, rule by rule (`GraphToStar.lean`),
  with synchronous phases and all decisions taken on the state at the start of the phase. This is
  enough to exhibit the failure. The model works on the 3-node line (`line3_ok`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Model §2.1 (activation at distance 2, deactivation) | `Cslib.DynNet.Active.ValidRound`, `validRound_iff` | `Podc/…/ActivelyDynamic.lean` |
| Prop. 2.1 / A.1 (TreeToStar: star after exactly `⌈log₂ d⌉` rounds, `≤ 2n−3` active edges, `≤ (n−2)⌈log₂ d⌉` activations) | `TreeToStar.proposition_2_1`, `TreeToStar.star_iff` | `TreeToStar.lean` |
| Prop. 2.1: `⌈log d⌉ ≤ log n` false (`n = 6`) | `ceil_log_depth_le_log_false`, `line6_not_star_two` | `TreeToStar.lean` |
| Prop. 2.2 / A.2 (LineToCompleteBinaryTree: valid, `≤ ⌈log₂ d⌉` rounds, complete binary tree of depth `⌊log₂ n⌋`, degree `≤ 3`, `≤ 2n−3` active edges, `≤ (n−2)⌈log₂ d⌉` activations) | `LineToBinaryTree.proposition_2_2`, `final_edist`, `exec_succ_ne` | `LineToBinaryTree.lean` |
| Lemma 3.1 false for GraphToStar as printed | `GraphToStar.lemma_3_1_breaks`, `line4_phase2`, `line4_terminates_wrong` | `GraphToStar.lean` |
| Lemma 6.1 / D.2 (`n − 1 ≤ 2^{T+1}·d`; `⌊log n⌋ ≤ 2T + 7` for depth `≤ log n + 1`) | `lemma_6_1`, `lemma_6_1_log`, `lemma_6_1_asymp` | `LowerBounds.lean` |
| Lemma 6.2 / D.3–D.4 (`n − 1 ≤ total + 2d`; `n − 1 ≤ T·(max per round) + 2d`) | `lemma_6_2_total`, `lemma_6_2_perRound` | `LowerBounds.lean` |
| Thm. 6.3 / D.5, line case (CutInHalf: `⌊log₂(n−1)⌋` rounds, `≤ n−1` activations, depth `≤ ⌈log₂ n⌉`) | `CutInHalf.theorem_6_3_line` | `CutInHalf.lean` |

**Not formalized.** The time analysis of GraphToStar (Lemmas 3.2–3.7, Theorem 3.8), §§4–5
(GraphToWreath, GraphToThinWreath, Theorems 4.2, 5.1), Theorem 6.3 for general graphs (Euler tour
of a spanning tree), and the distributed lower bound Theorem 6.4 / D.12.
- §§4–5 were not examined. They use a different merging mode instead of pulling, and the abstract's second and third
  algorithms rest on them.
- Theorem 6.3 for general graphs: the Euler-tour line has up to `2n` nodes, so the depth would be `log(2n)`, not
  `log n`. We only noted this in passing.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The GraphToStar counterexample and its sanity check are evaluated by
`decide +kernel`. The lower-bound hypotheses are satisfiable: TreeToStar and LineToCompleteBinaryTree
on the line and CutInHalf are concrete executions from `pathGraph n`, and CutInHalf shows that
Lemmas 6.1 and 6.2 are tight. Shared code: `Podc/Computability/Distributed/DynamicNetworks/ActivelyDynamic.lean`
(model, distance-halving and distance-minus-activations lemmas) and
`Podc/Foundations/Combinatorics/SimpleGraph/ParentGraph.lean` (graphs of parent maps are trees, edge
count, depth = distance, jumps). Both are CSLib candidates. The model reuses CSLib's
`SimpleGraph.RootedTree`, `edist_le_mul_of_adj` and `le_add_edist_of_lipschitz`.
