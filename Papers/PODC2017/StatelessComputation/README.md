# Stateless Computation — PODC 2017

Danny Dolev, Michael Erdmann, Neil Lutz, Michael Schapira, Adva Zair. *Stateless Computation.*
PODC 2017. DOI [10.1145/3087801.3087854](https://doi.org/10.1145/3087801.3087854). Formalized
version: arXiv [1611.10068](https://arxiv.org/abs/1611.10068) v1 (the only version); numbering
follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** Theorem 3.1 (two stable labelings rule out label `(n−1)`-stabilization), its tightness
example, Propositions 2.1–2.3, Theorem 5.10, Theorem 6.2 and Corollaries 6.3–6.4 hold after local repairs to their
proofs. The label covers only these: the hardness of verifying stabilization (Section 4) and the `L/poly` and
`P/poly` characterizations (Section 5), which are also main results, were not checked.

## Mistakes in the paper

### ✏️ Slips
- Theorem 3.1 fails on graphs with self-loops: on the complete digraph with loops on 2 nodes, the protocol in
  which each node copies its loop label to all its outgoing arcs has 4 stable labelings but is label
  `r`-stabilizing for every `r` (`SelfLoops.thm_3_1_false_with_loops`). A node with a self-loop can store its state
  on that loop, which the stateless model is meant to rule out. The paper excludes self-loops only implicitly (a
  node communicates with "another node", and processors "cannot store information"). With loop-free graphs the
  theorem holds; we assume them.
- Corollary 6.3 for odd `n`: the paper's `EQ_n` is constantly 0, so a protocol with a single label computes it,
  with label complexity `0 < (n−2)/8` (`FoolingSet.cor_6_3_false_odd`). The paper defines `EQ_n = 1` only for even
  `n`. For even `n` the corollary holds, and in the stronger form `L_n ≥ n/8` (`FoolingSet.cor_6_3`).

### Typos
- In the proofs of Corollaries 6.3/6.4 the names `C` and `D` are swapped.

## Proof gaps (statements true)

### 🔧 Theorem 3.1, final paragraph of the proof (`H`-successors)
The paragraph after Lemma 3.4 claims that the `H`-successors of the critical state are *all* activation sets with
`|T| ≥ 2` containing the node with countdown 1, which is false.

**Impact.** Statement true; repaired (`not_labelStabilizing`, `exists_nonconvergent_run`). Lemmas 3.3 and 3.4
themselves are fine.

**Details.** The proof works in the state space `H` of (labeling, countdown) pairs whose sorted countdown vector
dominates `(1, 2, …, r−1, r, r)`. Take `n = 5`, `r = 4` and countdowns `(2,2,4,4,4)`. Activating two of the nodes
with countdown 4 gives `(1,1,4,4,3)`, which is not in `H`. So the step that finds `S` and `S ∪ {i}` in different
attractor regions is not justified as written.

**Repair.** It is enough that the admissible activation sets are *upward closed*, so that any two of them are
connected through "activate everybody" by single-node insertions.

### 🔧 Theorem 3.1, attractor regions and the proof of Lemma 3.2
The paper never says whether attractor regions are defined by paths in `H` or in the full state graph: Lemma 3.4
and the final step need `H`, but Lemma 3.2's proof activates a single node, and that step leaves `H`.

**Impact.** Statement true; repaired (`Impossibility.exists_biv`).

**Repair.** We take valency in `H`. Lemma 3.2 then follows from Lemma 3.3 along a chain of hybrid labelings. We
checked the counting step of Lemma 3.3 (activating `j` and the minimum-countdown node `j'` stays in `H`) in Lean.

### 🔧 Theorem 5.10 (quantifier over `Σ`)
The proof counts protocols for one fixed `Σ`, but the statement needs one function that is hard for *all* small
`Σ` simultaneously.

**Impact.** Statement true; we prove it for `n ≥ 6` (`exists_hard_function`).

**Repair.** Sum the same count over all sizes up to the bound.

### 🔧 Theorem 5.10 (algebra step)
The step `log n + log(2|Σ|^k) + log log(2|Σ|^k) ≥ n ⇒ log n + 2k log|Σ| ≥ n` fails for `k log|Σ| < 3`.

**Impact.** Statement true; a different estimate in the same chain keeps the bound (`exists_hard_function`).

### 🔧 Corollary 6.3 (fooling set violates Theorem 6.2's conditions)
The fooling set `{(x,x) : x₁ = 1}` of the proof violates the bullet conditions of Theorem 6.2,
for example at the arc `(m, m+1)`.

**Impact.** Statement true (for even `n`): the proof of Theorem 6.2 never uses the bullet
conditions `xᵢ = x'ᵢ` (arcs of `C`) and `yᵢ = y'ᵢ` (arcs of `D`), and we prove the theorem without
them (`FoolingSet.card_le_of_isFoolingSet`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`)
* A finite set of nodes `V` and a digraph `G : Digraph V`. Each arc carries a label from `L` (the
  paper's `Σ`).
* A protocol is one reaction function per node, `δ i : (incoming labels) → X → (outgoing labels) × Y`.
  It is deterministic, and nodes have no other state. Inputs `X` and outputs `Y` are arbitrary;
  the paper uses `{0,1}`.
* Asynchrony is a schedule `σ : ℕ → Finset V`. An activated node applies `δ` to its current
  incoming labels.
* `IsRFair r σ`: every step activates a nonempty set, and every node is activated in every
  window of `r` consecutive steps (the shared `BoundedFair r` of `Cslib/Computability/Distributed/SelfStabilization/Daemon.lean`).
  Initial labelings and initial outputs are arbitrary
  (self-stabilization). There are no failures and no randomness.
* `LabelStabilizing r P`, as in the paper: for every input, initial labeling and `r`-fair schedule,
  the outputs converge and so do the labelings.
* Part II (Section 2.3 and Sections 5–6) uses synchronous executions (`syncRun`), with
  `SyncLabelStabilizing` and `SyncComputes f` (outputs converge to `f x` from every initial
  labeling). These are weaker than any `r`-fair notion, so the lower bounds are stronger than the
  paper's.
* Theorem 3.1 holds for arbitrary (also infinite) label types and graphs that need not be strongly
  connected. It requires only that `G` has no self-loops.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3.1 (also for every `r ≥ n−1`) | `not_labelStabilizing`, `exists_nonconvergent_run` | `Impossibility.lean` |
| Lemmas 3.2, 3.3, 3.4 (repaired) | `Impossibility.exists_biv`, `common_val`, `exists_critical` | `Impossibility.lean` |
| Theorem 3.1 fails with self-loops | `SelfLoops.thm_3_1_false_with_loops` | `SelfLoops.lean` |
| Example 1 (tightness: label `(n−2)`- but not `(n−1)`-stabilizing) | `Example1.or_tight` | `Example1.lean` |
| Proposition 2.1 (radius `≤ R_n`) | `exists_center` | `Basics.lean` |
| Proposition 2.2 (`R_n ≤ |Σ|^{|E|}`) | `Protocol.out_const_of_converges`, `Protocol.syncRun_const_of_converges` | `Basics.lean` |
| Proposition 2.3 (`L_n = n+1`, `R_n ≤ 2n`) | `UpperBound.prop_2_3`, `UpperBound.card_lbl` | `UpperBound.lean` |
| Theorem 5.10 (`L_n ≥ n/(4k)` for some `f`; `n ≥ 6`) | `exists_hard_function`, `exists_hard_function_logb` | `Counting.lean` |
| Theorem 6.2 (fooling sets) | `FoolingSet.card_le_of_isFoolingSet`, `FoolingSet.logb_le_of_isFoolingSet` | `FoolingSet.lean` |
| Corollary 6.3 (even `n`; false for odd `n`) | `FoolingSet.cor_6_3`, `cor_6_3_logb`, `cor_6_3_false_odd` | `FoolingSet.lean` |
| Corollary 6.4 | `FoolingSet.cor_6_4`, `cor_6_4_logb` | `FoolingSet.lean` |

**Informal proofs, made precise.**
* Example 1 (tightness of Theorem 3.1): the argument ignores initial labelings in which a node's outgoing arcs
  carry different bits. The claim is true (`Example1.or_tight`).
* Proposition 2.1: the proof is informal, and neither the round-complexity off-by-one nor the radius of a digraph
  is defined. The statement is true under a precise reading (`exists_center`).

**Not formalized.**
* Section 4: communication complexity `2^{Ω(n)}` and PSPACE-completeness of deciding
  `r`-stabilization.
* The complexity-class characterizations of Section 5 (`L/poly`, `P/poly`), the counter protocols
  of Claims 5.5–5.6 (the notion of a counter is informal), and Corollaries 5.7–5.9.

**Trust.**
* No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity:
  - Example 1 exhibits a protocol with two stable labelings that is label `(n−2)`-stabilizing.
  - `prop_2_3` gives, for every `f`, a protocol satisfying the hypotheses of the lower bounds.
  - The synchronous schedule is `r`-fair for every `r ≥ 1` (`isRFair_sync`).
* A brute-force search over random small protocols (3–4 nodes) found no counterexample to
  Theorem 3.1. Example 1 was also brute-force checked for `n = 3, 4`.
* The model is in `Model.lean`; the stone-age model in CSLib does not fit, since its nodes have
  states. Shared notions: `BoundedFair` (`Cslib/Computability/Distributed/SelfStabilization/Daemon.lean`),
  `Converges` is Mathlib's `Filter.EventuallyConst` (`converges_iff`), `WalkLen` is
  `Relation.RelatesInSteps` of the arcs, strong connectivity is `Digraph.StronglyConnected`
  (`stronglyConnected_iff`, `Cslib/Foundations/Combinatorics/Digraph/Walk.lean`). CSLib candidates:
  - the stateless-protocol model with `r`-fair schedules (`Model.lean`);
  - the countdown-graph encoding of `r`-fair schedules (`Impossibility.HPath.fair`);
  - BFS trees in digraphs (`UpperBound.exists_trees`).
