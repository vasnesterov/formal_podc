# On the Power of the Congested Clique Model — PODC 2014

Andrew Drucker, Fabian Kuhn, Rotem Oshman. *On the Power of the Congested Clique Model.* PODC 2014. DOI
[10.1145/2611462.2611493](https://doi.org/10.1145/2611462.2611493). Formalized version: the 10-page author copy
(no arXiv version; the "full version" cited for several proofs is not online).

**Verdict: ⚠️ Minor statement issues.** The headline results hold: the circuit simulation (Theorem 2, after
repairing a factor-2 counting error in its proof), the reduction from set disjointness (Lemma 13), and the lower
bounds for cliques (Theorem 15) and cycles (Theorem 19). The degeneracy upper bound (Claim 6, Theorem 7) holds for
connected `H`. The `K_{ℓ,m}` lower-bound gadget in the proof of Lemma 21 is wrong for every `ℓ ≠ m`, so Lemma 21
and Theorem 22 are unestablished there. Lemma 21 only claims that *some* lower-bound graph exists, and that claim
is not refuted (other gadgets exist in the smallest case), so this is a broken proof, not a false statement. The
statements that are false hold only in degenerate cases: Theorem 22 for `ℓ = 1` (stars), and Lemma 18 for `ℓ = 5`,
`N = 4`, where every graph on `N < ℓ` vertices is `C_ℓ`-free.

## Mistakes in the paper

### ⚠️ Lemma 21 and Theorem 22 for `ℓ ≠ m` (the `K_{ℓ,m}` lower-bound gadget)
The construction in the proof of Lemma 21 contains unintended copies of `K_{ℓ,m}` for every
`ℓ ≠ m`, so Lemma 21 and Theorem 22 are unestablished there (`lemma_21_counterexample`).

**Impact.** A broken proof, not a refuted statement: Lemma 21 only claims that *some* lower-bound
graph exists, and in the smallest case other gadgets exist. The case `ℓ = m` and all other lower
bounds (cliques, cycles) are unaffected.

**Details.** The proof claims that each side of a copy of `K_{ℓ,m}` contains at least two nodes of
`V_A ∪ V_B`, "as `|W^L| = ℓ − 2` and `|W^R| = m − 2` (and no mixing between `W^L, W^R` is
possible)". But in a non-induced copy, nodes of `W^R` can sit on the `ℓ`-side. Smallest case
`ℓ = 2`, `m = 3`, so `W^L = ∅` and `W^R = {w}`. Take `F` = the path `i – k – i'` with `i, i' ∈ L`
and `k ∈ R` (bipartite, `C₄`-free, 2 edges, at least `ex(3, C₄)/2`). Then
`{w, u_k} × {u_i, u_{i'}, v_k}` is a `K_{2,3}`: `w` is adjacent to `φA(L) ∪ φB(R)`, `u_k` to its
`F_A`-neighbours and to `v_k`. Its four nodes in `V_A ∪ V_B` are not of the form `φA(e) ∪ φB(e)`,
so condition II of Definition 10 fails. The copy uses only Alice's edges and fixed edges, so with
Bob's input empty the reduction graph contains `K_{2,3}`: Observation 11, and with it the
reduction, breaks.

The same happens for every `m = ℓ ± 1` as soon as `F` has a vertex of degree 2 on the relevant
side, which every `F` with `≥ ex(N, C₄)/2 = Θ(N^{3/2})` edges does for large `N` (counting argument,
not formalized). For `|ℓ − m| ≥ 2` there is even a copy of `K_{ℓ,m}` avoiding all of `F_A` and
`F_B`, so every input looks "intersecting". We do not know whether a lower-bound graph exists for
`ℓ ≠ m` in general. For the 2-edge `F` above, a brute-force search finds valid
`(K_{2,3}, F)`-lower bound graphs on `2N + ℓ + m − 4 = 7` vertices, so that instance of the lemma is
true. Brute force found no problem with the paper's construction for `ℓ = m`.
(`lemma_21_counterexample`, `lemma21_fails_succ`, `lemma21_fails_succ'`, `lemma21_fails_free`)

### ⚠️ Claim 6 and Theorem 7 for disconnected `H`
The proof of Claim 6 needs `H` connected, but the paper also applies Theorem 7 to forests.

**Impact.** Proved for connected `H` with at least one edge, which covers cycles, cliques and
complete bipartite graphs (`claim_6`, `theorem_7`). For disconnected `H` (including forests) the
claim is unestablished: our brute force found no counterexample, and we have no proof.

**Details.** The proof uses that `ex(n, H)` is non-decreasing in `n` and that
`ex(2n, H) ≥ 2 ex(n, H)` (two disjoint copies of an extremal graph). Both fail for disconnected
`H`, e.g. `H = K₂ ∪ K₁` has `ex(2, H) = 1 > ex(3, H) = 0` (`extremalNumber_edge_plus_point`). For
forests the doubling step fails too: `ex(3, 2K₂) = 3` (a triangle) but `ex(6, 2K₂) = 5` (a star).

### ⚠️ Theorem 22 for `ℓ = 1` (stars)
Theorem 22 is stated "for any `ℓ, m ≥ 1`", but for `ℓ = 1` (and, symmetrically, `m = 1`) one round
with one-bit messages suffices, not `Ω(√n/b)` (`theorem_22_false_of_l_eq_one`, `starAlg`).

**Impact.** Degenerate: `K_{1,m}` is a star, and `G` contains it iff some node has degree `≥ m`.
Lemma 21 assumes `ℓ, m ≥ 2`, so this is evidently a typo.

### ⚠️ Lemma 18 for `ℓ = 5`, `N = 4` (lower-bound graphs for cycles)
Lemma 18 claims an *extremal* `C_ℓ`-free `F` with a `(C_ℓ, F)`-lower bound graph for every even
`N`; for `ℓ = 5`, `N = 4` none exists (`lemma_18_false`, `no_lowerBoundGraph_C5_K4`).

**Impact.** Degenerate corner: for `N < ℓ` every graph on `N` vertices is `C_ℓ`-free, and
Theorem 19 (asymptotic in `n`, `ℓ` fixed) never uses it. Theorem 19 is proved from a corrected
Lemma 18.

**Details.** For odd `ℓ` the proof takes `F = K_{N/2,N/2}` "since `ex(N, C_ℓ) = N²/4`". That holds
only for large `N`. For `ℓ = 5`, `N = 4` the unique extremal `C₅`-free graph is `K₄`, and no
`(C₅, K₄)`-lower bound graph exists on any number of vertices. The witness cycle for an edge
`{u, v}` has a single vertex outside `V_A ∪ V_B`, so it contains a direct edge `A_x B_y` with
`x, y ∈ {u, v}`. Two such edges for the disjoint edges `{0,1}` and `{2,3}` of `K₄` close a 5-cycle
through three vertices of `V_A`, which violates condition II. Whether the lemma also fails for some
`N ≥ ℓ` (where `ex(N, C_ℓ) > N²/4` can still hold for odd `ℓ`) is not checked.
(`not_lemma18Statement`)

**Repair.** With "extremal" replaced by "`C_ℓ`-free, with all edges between the two halves when
`ℓ` is odd" the construction is correct for all `N`; we prove this (including condition II for
every cycle, which the paper does not argue) and derive Theorem 19 from it. (`lemma_18`)

### Typos and slips
- Lemma 14's construction connects `u_1, …, u_{ℓ−1}` to everything; it should be `u_{ℓ−4}`.
- Lemma 18's index ranges for the path nodes `u_{i,j}` give `⌊ℓ/2⌋` (resp. `⌈ℓ/2⌉`) internal
  nodes; it should be `⌊ℓ/2⌋ − 2` (resp. `⌈ℓ/2⌉ − 2`), consistent with the stated path lengths and
  the `(ℓ−4)N/2` extra nodes.
- Lemma 18 also claims "`ex(N, C_ℓ) = Ω(N^{3/2})`" for every even `ℓ`; for `ℓ ≥ 6` this contradicts
  Bondy–Simonovits (`ex(N, C_{2k}) = O(N^{1+1/k})`), but it is never used.
- Lemma 21's proof says "assume `n = 4N + ℓ + m − 4`"; it should be `2N`.
- Theorem 4 says "depth `c·R`" with `c > 1`; the simulation gives depth `R / c`.
- After Theorem 7 the paper says that for a fixed tree or forest `ex(n, H) = O(1)`. It is `O(n)`,
  which is what the stated running time `O(log(n)/b)` needs.

## Proof gaps (statements true)

### 🛠️ Theorem 2 (circuit simulation)
The proof's count of heavy gates is off by a factor 2: the total weight is `2N`, not `≤ n² s`.

**Impact.** Statement true; repaired with adjusted thresholds (`theorem_2`).

**Details.** The proof calls `G` heavy if `w(G) = |in G| + |out G| ≥ ns` (`N = n² s` wires) and
claims that "the number of heavy gates cannot exceed `n`". It also claims that the greedy
assignment of light gates never gets stuck with load `2ns`. Both rest on "total weight `≤ n² s`",
but the total weight is `2N`. With `n = 2`, `s = 1`, a path of 5 gates has `4 = n² s` wires and 3
heavy gates (`heavy_count_counterexample`).

**Repair.** Heavy iff `w ≥ n(2s + 1)` (counting input gates with weight `+1`) and light load
`≤ 2n(2s + 1)`. With these thresholds the simulation runs with bandwidth `b + 4s + 3` in `2D + 4`
rounds. We use oblivious routing (König splitting) instead of Lenzen's algorithm; all communication
patterns are fixed in advance. (`theorem_2`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CLIQUE-UCAST (Section 2): deterministic synchronous rounds on `n` players with known identities, no failures, free
  local computation. A program is a sequence of communication steps (`Prog`, staged in `Podc/`). A step whose longest
  per-pair message has `w` bits costs `⌈w/B⌉` rounds at bandwidth `B` (`Prog.roundsAt`). Each player starts with its
  own input bits; the protocol may depend on the circuit and the input partition.
* CLIQUE-BCAST (Section 3): synchronous rounds; every node broadcasts `b` bits per round (`Bcast.Algorithm`, staged).
  The input of a node is its incident edges. Randomized algorithms get private coins, uniform over a finite set.
* CONGEST-UCAST: CSLib's deterministic CONGEST (`Cslib.Congest.Algorithm`) on the input graph.
* Detection convention: all nodes accept iff the input graph is `H`-free. Copies of `H` are Mathlib `Copy`s, i.e.
  not necessarily induced subgraphs, as in the paper.
* Randomized lower bounds take the randomized communication complexity of set disjointness as a hypothesis
  (`RandDisjLB`). Deterministic bounds are unconditional (CSLib's `CC(DISJ_K) ≥ K`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1, circuits | `Separable`, `Circuit`, `Circuit.eval` | `Circuit.lean` |
| Theorem 2 (bandwidth `b+4s+3`, `2D+4` rounds) | `theorem_2` | `CircuitSim.lean` |
| Theorem 2, proof: "≤ n heavy gates" is false | `heavy_count_counterexample` | `Circuit.lean` |
| Theorem 2, repaired gate assignment | `Circuit.exists_assignment` | `CircuitAssign.lean` |
| Theorem 4 | `theorem_4` | `CircuitSim.lean` |
| Claim 6 (connected `H`) | `claim_6`, `claim_6_isDegenerate` | `Claim6.lean` |
| Claim 6, proof step false for `K₂ ∪ K₁` | `extremalNumber_edge_plus_point` | `Claim6.lean` |
| Theorem 7 (connected `H`) | `theorem_7`, `thm7Rounds_mul_le` | `Theorem7.lean` |
| reconstruction algorithm of [2] (our sketch version) | `exists_independent`, `eq_of_sketch` | `Sketch.lean` |
| Definition 10, Observation 11, Definition 12 | `LowerBoundGraph`, `observation_11`, `LowerBoundGraph.IsSparse` | `LowerBoundGraph.lean` |
| Lemma 13 (BCAST) | `lemma_13_bcast`, `lemma_13_bcast_rand` | `Lemma13.lean` |
| Lemma 13 (CONGEST) | `lemma_13_congest`, `lemma_13_congest_sparse`, `lemma_13_congest_rand` | `Lemma13.lean` |
| Lemma 14 | `lemma_14` | `Cliques.lean` |
| Theorem 15 | `theorem_15`, `theorem_15_real`, `theorem_15_rand` | `Theorem15.lean` |
| Lemma 18 false (`ℓ = 5, N = 4`) | `lemma_18_false`, `not_lemma18Statement`, `no_lowerBoundGraph_C5_K4` | `CyclesCounterexample.lean` |
| Lemma 18 (corrected), even/odd forms | `lemma_18`, `lemma_18_even`, `lemma_18_odd` | `CyclesLemma18.lean` |
| Lemma 18, the construction and condition II | `CycleLB.lowerBoundGraph`, `card_cut_le` | `CyclesConstruction.lean` |
| Theorem 19 (BCAST, CONGEST) | `theorem_19_bcast`, `theorem_19_congest` | `Theorem19.lean` |
| Lemma 21 fails (`ℓ = 2, m = 3`) | `lemma_21_counterexample` | `Bipartite.lean` |
| Lemma 21 fails (general `ℓ ≠ m`) | `lemma21_fails_succ`, `lemma21_fails_succ'`, `lemma21_fails_free` | `Bipartite.lean` |
| Theorem 22 false for `ℓ = 1` | `theorem_22_false_of_l_eq_one` | `Star.lean` |

**Not formalized.** Section 2.1 (matrix multiplication and triangles), Remark 3, the threshold/ACC consequences,
Lemma 8 and Theorem 9 (sampling), Theorem 22 for `ℓ = m` (it needs `ex(N, C₄) = Ω(N^{3/2})`), and Section 3.6
(triangles vs. 3-party NOF disjointness).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `andCircuit_ucast` runs Theorem 2 on a concrete circuit. `theorem_7`'s algorithm satisfies the detection
hypothesis of Lemma 13 and Theorems 15/19 (for connected `H`). Staged shared code (CSLib candidates):
`Podc/Computability/Distributed/CongestedClique/Broadcast.lean` (CLIQUE-BCAST, two-party simulation, one-shot
broadcast) and `Bandwidth.lean` (bandwidth cost, oblivious routing at bandwidth `B`). It builds on the staged phase
programs and oblivious routing (`Phases.lean`, `Oblivious.lean`) and on CSLib's `Cslib.Congest` and
`Cslib.CommunicationComplexity`. Further CSLib candidates in this folder: `Sketch.lean`, the greedy assignment in
`CircuitAssign.lean`, `isContained_sum_of_connected` and the `ex(n, H)` monotonicity lemmas in `Claim6.lean`.
