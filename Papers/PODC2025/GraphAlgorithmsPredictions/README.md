# Distributed Graph Algorithms with Predictions — PODC 2025

Joan Boyar, Faith Ellen, Kim S. Larsen. *Brief Announcement: Distributed Graph Algorithms with Predictions.*
PODC 2025. DOI [10.1145/3732772.3733530](https://doi.org/10.1145/3732772.3733530). Formalized version: the brief
announcement; the proof of Theorem 4.1 is taken from the full version, arXiv
[2501.05267](https://arxiv.org/abs/2501.05267) (Lemmas 4 and 5 there).

**Verdict: ✅ Correct.** Theorem 4.1 (every deterministic component-size bounded MIS algorithm needs `(n − 5)/2`
rounds on an `n`-node line) holds, by the paper's own Ramsey proof. The 3-round pruning algorithm, the round bound
`n` of the Distributed Greedy MIS Algorithm, consistency, and the `η + 3` round bound of "pruning, then greedy on
every error component" all hold. The same Ramsey argument applied directly to MIS gives the slightly better bound
`(n − 4)/2`.

## Mistakes in the paper

No mistakes in the checked statements. Small remarks:

* **Theorem 4.1 is not tight in its constant.** Applying Ramsey directly to the MIS outputs gives three
  consecutive middle nodes with the same output: all three in the MIS contradicts independence, none in the MIS
  contradicts maximality. This needs a window of `2T + 5` nodes and gives `T ≥ (n − 4)/2`. The paper's detour
  through 3-colouring (Lemma 5 of the full version) loses one round. (`mis_lowerBound_sharp`)
* **Lemma 4 of the full version holds for any finite number of colours**, not only 3: the Ramsey argument never
  uses the number of colours. (`lemma_4`)
* **Round counting of the pruning algorithm.** The paper's third round only tells the remaining active nodes that
  the neighbours of `I` have terminated. With the usual "send, receive, compute" round convention (CSLib's
  locally-iterative model) this message is part of the next round, and 2 rounds suffice. This is a counting
  convention, not an error: we prove the paper's 3 (round 3 is idle in our model).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous, fault-free, deterministic LOCAL. Nodes are named by distinct identifiers (the convention of CSLib's
  `Cslib.Local`), so comparisons of identifiers are comparisons of node names.
* **Lower bound** (`Line.lean`, `LowerBound.lean`). A `T`-round algorithm is any function
  `f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β` with `Cslib.Local.IsLocal T f`: the output of a node depends only on
  the edges at distance `< T` and the labels at distance `≤ T`. An `n`-node line is an injective placement
  `id : Fin n ↪ ℕ`; the label of a node holds the identifiers of its left and right neighbours (so after `T` rounds
  a node knows the identifiers up to distance `T + 1`, and the orientation). The algorithm may depend on `n` (nodes
  know `n`), and must be correct for every placement of arbitrary natural identifiers, i.e. its round count does
  not depend on the identifier domain. Every component-size bounded algorithm is such an algorithm, and algorithms
  that ignore the orientation or see less are special cases, so the lower bound covers them. The `*_bounded`
  variants show that identifiers below an explicit `D(n, T)` already suffice ("`d` is a sufficiently large
  function of `n`").
* **Algorithms** (`Algorithm.lean`, `Greedy.lean`, `Main.lean`). CSLib's locally-iterative model
  (`Cslib.LocallyIterative.Algorithm`): in each round a node updates its state from its own state and the set of
  its neighbours' states. A state holds the identifier, the prediction bit and the status (active / output 1 /
  output 0). `pruneAlg` = prune rule, then "output 0 if a neighbour output 1"; `greedyAlg` = local-maximum rule in
  odd rounds, "output 0" rule in even rounds; `predAlg = pruneAlg.seq 3 greedyAlg`. Graphs are finite
  (`Fintype V`), identifiers linearly ordered.
* The error measure `η` is the paper's: the maximum number of nodes of an error component, i.e. a connected
  component of the subgraph induced by the nodes the pruning algorithm leaves active (`eta`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 4.1 (= full version Lemma 5): MIS on the `n`-line needs `≥ (n − 5)/2` rounds | `theorem_4_1` | `LowerBound.lean` |
| Full version Lemma 4: 3-colouring the `n`-line needs `≥ (n − 3)/2` rounds (any finite colour set) | `lemma_4`, `lemma_4_bounded` | `LowerBound.lean` |
| Full version Lemma 5, reduction MIS (`T` rounds) → 3-colouring (`T + 1` rounds) | `misToColour_isLocal`, `misToColour_solves` | `LowerBound.lean` |
| Ramsey step of Lemma 4 | `exists_homogeneous_window` | `LowerBound.lean` |
| Sharper bound `≥ (n − 4)/2` (not in the paper) | `mis_lowerBound_sharp`, `mis_lowerBound_bounded` | `LowerBound.lean` |
| Full version Thm 3: finite Ramsey theorem for `k` colours | `Cslib.exists_homogeneous_finite` | `Podc/Foundations/Combinatorics/HypergraphRamsey.lean` |
| §3: `I` ∪ neighbours is an extendable partial solution; agrees with the prediction | `pruneSet_extendable`, `pruneSet_agrees`, `isMIS_union_of_extendable` | `Main.lean`, `Basic.lean` |
| §3: the variant initialization (larger `I`) is extendable | `pruneSet'_extendable`, `pruneSet_subset_pruneSet'` | `Main.lean` |
| §3: state after the 3 pruning rounds | `pruneAlg_status` | `Main.lean` |
| §3: consistency (correct prediction ⇒ `η = 0`, output = prediction after 3 rounds) | `predAlg_consistent` | `Main.lean` |
| §4: Distributed Greedy MIS terminates within `n` rounds (within the component size), output is an MIS | `greedy_round_complexity`, `greedy_decided`, `greedy_isMIS` | `Main.lean`, `Greedy.lean` |
| §5: pruning + greedy terminates within `η + 3` rounds with an MIS (`η`-degrading) | `predAlg_terminates`, `predAlg_correct` | `Main.lean` |
| the algorithm is a LOCAL algorithm | `predAlg_isLocal` | `Main.lean` |

**Not formalized.** The framework definitions (consistent/robust/smooth as asymptotic notions), the generic
compositions of Section 5 with black-box algorithms (`2f(η)`-degrading composition with a clean-up algorithm,
the fault-tolerant parallel composition), the coloring-based algorithms and the cited results ([2], [7], [8]).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity of Theorem 4.1: `exists_mis_algorithm` gives an `n`-round MIS algorithm for `n`-node lines (parity of
the distance to the left end), so the class of algorithms is not empty and the bound is tight up to a factor 2.
Models come from CSLib (`Cslib.Local.IsLocal`, `Cslib.LocallyIterative`); the `k`-colour Ramsey theorem was added
to the staged `Podc/Foundations/Combinatorics/HypergraphRamsey.lean` (CSLib candidate).

**CSLib candidates.** `Line.lean` (oriented line in the LOCAL model, window lemma) and the `k`-colour Ramsey
theorems `Cslib.exists_homogeneous_lt` / `Cslib.exists_homogeneous_finite`; also `IsMIS`/`IsMISOn` and the
extendability lemma in `Basic.lean`.
