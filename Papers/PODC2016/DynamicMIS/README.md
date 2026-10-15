# Optimal Dynamic Distributed MIS (PODC 2016)

Keren Censor-Hillel, Elad Haramaty, Zohar Karnin. *Optimal Dynamic Distributed MIS.*
PODC 2016, pp. 217–226. DOI [10.1145/2933057.2933083](https://doi.org/10.1145/2933057.2933083),
full version arXiv:1507.04330.

## Status

The main result, **Theorem 1**, is formalized and verified with no `sorry`. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`. Also formalized:
- Lemma 2;
- Claims 4–5;
- Lemma 3, in its correct form `≤ 1/|P|` (`=` holds for node changes);
- Corollary 6 in the synchronous model;
- a weak version of history independence (Section 5), for the direct implementation only;
- the counterexample to Lemma 3 as literally stated (with `= 1/|P|`).

- **Section 4: Algorithm 2 and Theorem 7**, both for non-abrupt changes (Lemmas 8, 9, 11) and
  for abrupt deletion (Lemmas 11, 12, 13).

We found no error that breaks a main result. We did find imprecise or wrong statements (details in
[differencies.md](differencies.md)):
- the recursion (1) for `S_i` makes the layers non-decreasing, so Algorithm 1's loop need not
  terminate (a notational flaw);
- Lemma 3's equality fails for edge changes (Lean counterexample): a genuine misstatement, but
  harmless, since its own proof only concludes `≤`;
- the arguments in Lemma 2, Claim 4 and the end of Lemma 3 are informal.

All of these are repaired. As a by-product, `E|S| = 1` exactly for node insertions and deletions.

## Model and assumptions

- **Graphs.** A configuration is a `SimpleGraph` on a finite type `V` plus a set of present nodes;
  the network is the induced graph. Node changes alter the present set; edge changes alter the
  graph. There are four changes: edge insertion, edge deletion, node insertion, node deletion.
- **Randomness.** The order `π` is a uniformly random bijection `V ≃ Fin |V|`. Expectations are
  finite averages `𝔼 π, …` (no measure theory). The adversary is oblivious: the change is fixed
  before `π` is drawn.
- **MIS.** The MIS is the greedy MIS for `π` (the paper's "MIS invariant"): `SimpleGraph.greedyMIS`.
- **`S` and `S′`.** `S` (`infl`) is the closure of the paper's recursion (1). It is empty when the
  invariant still holds at `v*`. `S′` is the influenced set with `v*` moved to the front
  (`influencedFirst`).
- **Distributed model (Corollary 6, Section 4).** Synchronous rounds; every node knows its
  neighbours' ranks and current states (broadcast on change). The direct implementation is a
  SET-LOCAL algorithm in the CSLib `Cslib/Computability/Distributed/Local` model. The asynchronous model is not formalized.

## Main results ↔ Lean

| Paper | Lean | File |
|---|---|---|
| recursion (1), `S = ⋃ S_i` | `Influenced`, `layer`, `mem_layers_iff`, `mem_layer_of_inMbar` | `Basic.lean` |
| `S(G_old, G_new, π)` | `infl` | `Basic.lean` |
| closure = three-valued influenced set | `influenced_iff` | `Basic.lean` |
| **Theorem 1** `E_π|S| ≤ 1` | `DynamicMIS.theorem1` (sum form `sum_ncard_infl_le`) | `Theorem1.lean` |
| adjustments `≤ |S|`, `E ≤ 1` | `adjustments_subset_infl`, `expected_adjustments_le_one` | `Theorem1.lean` |
| Lemma 2 | `lemma2` (also `infl_eq`) | `Lemma2.lean`, `Theorem1.lean` |
| Claims 4–5 | `SimpleGraph.partialGreedy_eq_of_reorder`, `influencedFirst_eq_of_reorder` | `Cslib/Foundations/Combinatorics/SimpleGraph/GreedyMIS.lean`, `Cslib/Foundations/Combinatorics/SimpleGraph/RandomGreedyMIS.lean` |
| Lemma 3 (summed form) | `Cslib.RandomOrder.sum_card_first_le`, `sum_card_first_eq`; `SimpleGraph.sum_card_influenced_le`/`_eq` | `Cslib/Probability/RandomOrder/FirstInSet.lean`, `Cslib/Foundations/Combinatorics/SimpleGraph/RandomGreedyMIS.lean` |
| Lemma 3 with `=` is false | `lemma3_eq_counterexample` | `Lemma3Counterexample.lean` |
| `E|S| = 1` for node changes (new) | `theorem1_node_eq` | `Lemma2.lean` |
| Corollary 6 (synchronous) | `corollary6_rounds`, `directAfter_eq_of_le`, `corollary6_changing_subset`, `run_directAlg` | `Corollary6.lean` |
| Section 5, Definition 14 (weak version, direct implementation with `|V|` rounds per change, same initial and final `Config`) | `maintained_eq_greedyMIS`, `historyIndependent`; for Algorithm 2 only the per-change `Alg2.alg2_run_eq_of_le` | `HistoryIndependence.lean`, `Theorem7.lean` |
| Algorithm 2 (model) | `Alg2.step`, `Alg2.run`, `netOf`/`initOf`, `netAbrupt`/`initAbrupt` | `Alg2Defs.lean` |
| Lemma 8 (≤ 3 changes per node) | `Alg2.graceful_changes_le_three` | `Alg2Graceful.lean` |
| Lemma 9 (correctness, only `S` changes, `≤ 3|S|` broadcasts) | `graceful_run_eq`, `graceful_eq_of_notMem_infl`, `graceful_broadcasts_le` | `Alg2Graceful.lean` |
| Lemma 11 (stable by round `3|S|+2`) | `graceful_stableFrom(_add_two)`, `abrupt_stableFrom(_add_two)`, abstract `stableFrom_three_mul` | `Alg2Graceful.lean`, `Alg2Abrupt.lean`, `Alg2Rounds.lean` |
| Lemma 12 | `abrupt_entry_spacing` (`t₂ ≥ 3t₁+4`), `abrupt_card_entries_le` | `Alg2Abrupt.lean`, `Alg2Roots.lean` |
| Lemma 13 | `abrupt_broadcasts_le`, `abrupt_run_eq`, `abrupt_eq_of_notMem_infl` | `Alg2Abrupt.lean` |
| **Theorem 7** | `Alg2.theorem7_graceful`, `Alg2.theorem7_abrupt` | `Theorem7.lean` |

## Proof idea of Theorem 1 (as formalized)

1. Let `H` be the graph without the changed edge (or with the changed node).
2. Evaluate the greedy MIS of `H` in three-valued logic with `v*` unknown. The `none`-set is the
   influenced set. Every state vector that obeys the greedy rule away from `v*` agrees with the
   determined values, so the paper's closure `S` equals this set.
3. If the invariant breaks at `v*`, then `v*` is in the greedy MIS of `H`, and `S` is the
   influenced set of `v*` (`infl_eq`).
4. `v*` is in the greedy MIS iff `v*` is `π`-first in `S′`, and then `S = S′`.
5. `S′` is invariant under reorderings that keep the relative orders inside `S′ \ {v*}` and
   outside `S′`.
6. A swap-with-successor injection on orders gives
   `E[|S′| · 1{v* first} · 1{v** before v*}] ≤ Pr[v** before v*]`.
7. Sum over the two orientations of the changed edge.

## Infrastructure (migrated to CSLib)

- `Cslib/Foundations/Combinatorics/SimpleGraph/GreedyMIS.lean`: the greedy MIS for a rank function, the three-valued evaluation
  `partialGreedy` and `influenced`, determinacy, congruence, move-first, reorder invariance.
- `Cslib/Foundations/Combinatorics/SimpleGraph/RandomGreedyMIS.lean`: the expectation bounds for random greedy MIS
  (`sum_card_influenced_le`/`_eq`).
- `Cslib/Probability/RandomOrder/FirstInSet.lean`: "first in a random set" under uniform random orders.

## Files

- `Basic.lean`: configurations, changes, `v*`, the invariant, recursion (1) (`layer`, `Influenced`),
  `infl`, `influenced_iff`.
- `Theorem1.lean`: reduction to the base graph (`FlipData`, `infl_eq`), adjustments, Theorem 1.
- `Lemma2.lean`: Lemma 2, `E|S| = 1` for node changes.
- `Lemma3Counterexample.lean`: Lemma 3 with `=` is false.
- `Corollary6.lean`: the direct synchronous implementation (`directRun`, as a CSLib `Cslib/Computability/Distributed/Local`
  algorithm), convergence in `|S|` rounds, Corollary 6.
- `HistoryIndependence.lean`: Section 5, a weak version for the direct implementation (see
  differencies.md item 11).
- `Alg2Defs.lean`: the model of Algorithm 2 (Section 4).
- `Alg2Basic.lean`: one-round lemmas, the invariants J0–J2 and correctness at termination.
- `Alg2Rounds.lean`: an abstract version of Lemma 11 via rank-count potentials.
- `Alg2Roots.lean`: the roots of trigger chains, Lemma 12 spacing, counting C-entries and
  broadcasts.
- `Alg2Graceful.lean`, `Alg2Abrupt.lean`: the two instances.
- `Theorem7.lean`: the expected complexities.

## Section 4

The model (`Alg2Defs.lean`) is a synchronous broadcast network.
- States: `M`, `M̄`, `C` (with an age), `R`. The paper's four rules are encoded literally.
- "`u` changes to `C`" means `u` is in `C` with age 0. "Changed to `C` at least 2 rounds ago"
  means age `≥ 1`.
- A gracefully deleted node keeps participating but is not *active*, so it ends in `M̄`.
- Node unmuting = `insertNode`. The node-insertion variant of Section 4.1 (two extra announcement
  rounds) is not modelled separately.

Proved deterministically, with `S` the influenced set:
- only nodes of `S` ever change;
- the run is stable from round `3|S|` (paper: `3|S|+2`) at the new greedy MIS;
- non-abrupt changes: each node changes at most 3 times and there are at most `3|S|` broadcasts;
- abrupt deletion: C-entries of a node satisfy `t₂ ≥ 3t₁+4`, the number of entries is at most
  `min(log₃(|S|+1)+1, deg x)`, and there are at most `3|S|·min(…)` broadcasts.

With Theorem 1 this gives Theorem 7:
- `E[adjustments] ≤ 1`;
- `E[rounds] ≤ 3`;
- `E[broadcasts] ≤ 3` for non-abrupt changes, and `≤ 3·min(log₃(n+1)+1, deg x)` for abrupt
  deletion.

## Token spend

About 0.75M tokens in total:
- paper agent: about 0.42M;
- subagent "random orders" (`Cslib/Probability/RandomOrder`): about 85k;
- subagent "Algorithm 2" (Section 4): about 0.25M.
