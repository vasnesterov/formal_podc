# Optimal Dynamic Distributed MIS — PODC 2016

Keren Censor-Hillel, Elad Haramaty, Zohar Karnin. *Optimal Dynamic Distributed MIS.* PODC 2016.
DOI [10.1145/2933057.2933083](https://doi.org/10.1145/2933057.2933083). Formalized version: arXiv
[1507.04330](https://arxiv.org/abs/1507.04330) v2.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** Theorem 1 (`E_π|S| ≤ 1` for every single topology change) and Theorem 7
(Algorithm 2: expected `O(1)` rounds and broadcasts, `O(min(log n, deg))` for abrupt deletion) hold in the
synchronous model. The repairs are all local: the recursion defining the layers `S_i` is ill-formed as
written, rule 4 of Algorithm 2 needs one condition, Lemma 3 as stated ("`= 1/|P|`") is false for edge
changes but its own proof concludes the `≤` that Theorem 1 needs, and several proofs have small gaps. The
asynchronous model, the deterministic lower bound and history independence of Algorithm 2 were not
checked.

## Mistakes in the paper

### 🔧 Recursion (1) (the layers `S_i`)
The rule for `M̄`-nodes is cumulative ("every `v ∈ I(u) ∩ M` is in `S_0 ∪ … ∪ S_{i−1}`"), so taken literally a node
that enters some `S_i` by this rule is in every later `S_j`, `i_u = max{i | u ∈ S_i}` is undefined, and Algorithm
1's loop "until `S_i = ∅`" never terminates when `S` contains such a node (`mem_layer_of_inMbar`).

**Impact.** Notational: Theorem 1 concerns only `|S| = |⋃ S_i|`.

**Details.** In the paper's own example, `u2` lies in every `S_i` with `i ≥ 1`, not just `S_1` and `S_4`.

**Repair.** We use `S` as the least set closed under the two rules (`Influenced`).

### 🔧 Algorithm 2, rule 4 (graceful node deletion)
Algorithm 2 never says that a gracefully deleted node, which keeps participating, must not enter `M`.

**Impact.** The pseudocode needs one condition; Theorem 7 is proved for it (`Alg2.theorem7_graceful`).

**Repair.** We add this to rule 4: only active nodes enter `M`.

### ✏️ Slips
- **Lemma 3 ("`= 1/|P|`" for edge changes).** Lemma 3's equality is false for edge changes: on the path
  `v* – z – v**`, inserting or deleting the edge `{v*, v**}` with any order `z < v** < v*` gives
  `S′ = P = {v*, z, v**}` and conditional probability `0`, not `1/3`, that `v*` is first in `P`
  (`lemma3_eq_counterexample`). The paper's proof handles this case ("clearly 0") and concludes only
  `≤ 1/|P|`, which is all Theorem 1 needs. In the counterexample `π(v**) ≤ π(v*)`, so the probability
  that `v*` is first in `P`, given this event, is `0`. For node changes (`v** = v*`) equality does hold.
  As a by-product we get `E|S| = 1` *exactly* for effective node insertions and deletions, which is
  stronger than Theorem 1's `≤ 1` (`theorem1_node_eq`).

## Proof gaps (statements true)

### 🔧 Lemma 12, second part (entries into `C`)
The claim that each entry of `v` into `C` "can be associated with a different `v_i*`" is argued incompletely: the
paper itself concedes that the new path may pass through `v_i*`.

**Impact.** Statement true; repaired (`abrupt_card_entries_le`).

**Repair.** The missing fact: the root of the entry at `t₂` stays in `C` throughout `[0, 2t₂+1]`, whereas the root
of the entry at `t₁` is already final by time `t₂ − 1 − t₁`, so the two roots differ.

### 🔧 Lemma 2, proof
The proof mixes states computed for `π` and for `π′`.

**Impact.** Statement true; repaired (`lemma2`).

**Details.** We prove `S = S′` whenever `S ≠ ∅` (the paper states `S ⊆ S′`).

### 🔧 Claims 4–5, as used in Lemma 3
Claims 4–5 are stated for `π|P = σ|P`, which fixes `v*`'s position, but Lemma 3 applies them to orders that agree
only on `P \ {v*}`.

**Impact.** Statement true; the repair is one condition, because `S′` does not depend on `π(v*)`.

**Details.** The end of Lemma 3 rests on an independence claim. It is true, and we replace it by a counting
argument: swapping `v*` with its successor in `P` is an injection.

### 🔧 Lemma 11, final claim (abrupt deletion)
Correctness of the final MIS after an abrupt deletion is asserted without argument ("straightforward to verify"),
although the modified start makes several nodes enter `C` at once.

**Impact.** Statement true; proved by two invariants (`abrupt_stableFrom`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A configuration is a simple graph on a finite vertex type plus a set of present nodes. All four
  changes (edge/node insertion/deletion) are covered, with no validity hypotheses; vacuous changes
  give `S = ∅`.
* `π` is a uniformly random bijection `V ≃ Fin |V|`, and expectations are finite averages. The
  adversary is oblivious: the change is fixed before `π`. The MIS is the greedy MIS for `π`.
* Corollary 6 and Section 4 are synchronous only. The direct implementation is a SET-LOCAL algorithm
  in CSLib's LOCAL model (`run_directAlg`, via `Algorithm.run_semiconj` of
  `Cslib/Computability/Distributed/Local/Identifiers.lean`; `t`-locality: `directAlg_isLocal`). Algorithm 2 runs in synchronous broadcast rounds, with its four rules
  encoded literally. Ranks replace the real IDs `ℓ_v`, and message sizes are not modelled.
* "Rounds" = stabilisation time; "broadcasts" = (node, round) pairs where the visible state changes.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| **Theorem 1** `E_π\|S\| ≤ 1`; also for actual adjustments | `theorem1`, `expected_adjustments_le_one` | `Theorem1.lean` |
| Lemma 2 (`S = S′`) | `lemma2` | `Lemma2.lean` |
| Lemma 3 (`≤`; `=` for node changes) | `Cslib.RandomOrder.sum_card_first_le`, `sum_card_first_eq` | CSLib `Cslib/Probability/RandomOrder/FirstInSet.lean` |
| Lemma 3 with `=` is false | `lemma3_eq_counterexample` | `Lemma3Counterexample.lean` |
| `E\|S\| = 1` for node changes (new) | `theorem1_node_eq` | `Lemma2.lean` |
| Corollary 6 (synchronous) | `corollary6_rounds`, `corollary6_changing_subset` | `Corollary6.lean` |
| Lemmas 8, 9 (non-abrupt) | `graceful_changes_le_three`, `graceful_run_eq`, `graceful_broadcasts_le` | `Alg2Graceful.lean` |
| Lemmas 11–13 (abrupt deletion) | `abrupt_stableFrom`, `abrupt_entry_spacing`, `abrupt_broadcasts_le` | `Alg2Abrupt.lean` |
| **Theorem 7** | `Alg2.theorem7_graceful`, `Alg2.theorem7_abrupt` | `Theorem7.lean` |

The Section 4 bounds come out slightly better than the paper's: stabilisation by round `3|S|`
(paper: `3|S|+2`), and Lemma 12's spacing `t₂ ≥ 3t₁ + 2` in paper rounds (paper: `3t + 1`).

**Not formalized.**
* The asynchronous model of Corollary 6, the deterministic lower bound, correlation clustering and
  the `O(1)`-bit ID encoding.
* Node insertion with announcement rounds (§4.1, Lemma 10) is not modelled separately; unmuting stands
  in for it.
* Section 5 (history independence): only a weak, almost trivial version is proved, for the direct
  implementation (`historyIndependent`).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The proof of Theorem 1 goes through a three-valued greedy evaluation with `v*` unknown,
whose undetermined set is shown equal to the paper's closure `S` (`influenced_iff`). Greedy MIS,
Claims 4–5 and random-order lemmas are in CSLib
(`Cslib/Foundations/Combinatorics/SimpleGraph/{GreedyMIS,RandomGreedyMIS}.lean`,
`Cslib/Probability/RandomOrder/FirstInSet.lean`).
