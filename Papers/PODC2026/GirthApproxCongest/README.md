# Girth Approximations in the CONGEST Model — PODC 2026

Shiri Chechik, Gur Lifshitz, Doron Mukhtar. *Girth Approximations in the CONGEST Model.* PODC 2026.
DOI [10.1145/3796701.3815933](https://doi.org/10.1145/3796701.3815933). Formalized version: arXiv:2603.27601v1, §6 (lower bounds).

**Verdict: ❌ False claim.** The lower bounds of §6 hold as stated: Theorem 6.1 and its asymptotic form (`(3 − ε)`-approximation needs
`Ω̃(n^{3/5})` rounds, unconditionally) and Theorem 6.2 under the Erdős–Simonovits hypothesis, for directed and for undirected
weighted graphs, deterministic and randomized, on networks of diameter `O(log n)`. Claim 6.2(1) gives a slightly wrong value
for the weighted girth. The error is off by 2 and harmless, because the proof only uses an upper bound, but the claim is false
as written. A literature bound quoted in §6 has an off-by-one exponent.

## Mistakes in the paper

* **Claim 6.2(1) gives the wrong value (false as stated, harmless).** For intersecting inputs the claim says the weighted girth
  *equals* `2q/ε · (1 + ε) = 2q + 2q/ε`. The proof counts `2q` pipe edges of weight 1, but each pipe `r_1 → … → r_q` has only
  `q − 1` edges. The directed Claim 6.1 counts this correctly. The cycle through a shared edge therefore weighs
  `2(q − 1) + 2q/ε`, which is 2 less than claimed, so the girth is strictly below the stated value. The reduction only needs
  `girth ≤ 2q/ε · (1 + ε)`, which still holds, so Theorem 6.2 is unaffected. We prove the corrected upper bound and that the
  stated value is strictly too large. (`uGraph_mwc_of_inter`, `claim_6_2_value_lt`)
* **Proof gap in the weighted disjoint case (Claim 6.2(2)).** The proof projects a minimum cycle onto `H`, says this "yields a
  cycle in `H`" and concludes there are at least 6 input edges. This step fails for undirected graphs. A cycle may enter the
  pipe of `l` at both ends, using two Alice edges at `l_1` and two Bob edges at `l_q`, and then the projection visits `l`
  twice. In general the projection is only a closed *trail* in `H` (no repeated edges, because the inputs are disjoint), not a
  cycle. The claim is still true: a non-empty closed trail is at least as long as the girth. The case of a cycle with no
  input edge at all (inside one pipe) also has to be excluded. We prove the claim, for every `k`, with this argument.
  (`uGraph_mwc_of_disj`, `egirth_le_card_of_stutter`)
* **The black-box communication lower bound is correct here, but not via a fixed cut (checked, not a mistake).** The paper invokes Das Sarma et al.
  (Lemma 4.1 of [9]) "on the underlying undirected communication network consisting of the pipes and the shortcut tree".
  This network is not literally theirs: the inputs are edges inside layers `1` and `q`. Every *fixed* cut separating
  Alice's input nodes from Bob's cuts all `2a` pipes, so a fixed-cut simulation only gives `T = Ω(m / (aB)) = Ω(√a / B)`. We formalized the moving-cut simulation in general
  and checked it for this network. Alice's simulated set shrinks by one column per round, and per round only one arc per
  tree level crosses into each shrinking set, so `T` rounds cost `2T(⌈log₂ q⌉ + 1)B + 2` bits as long as `2T + 2 ≤ q`.
  The black box is therefore correct here. (`MovingCutFamily.simulation`, `gadgetFamily`, `card_toA_le`)
* **Slips** (none affects a result):
  - §6, "Before presenting …": the paper attributes `ex(n, C_{<2k}) = O(n^{1+1/k})` to Bondy–Simonovits and calls it
    conjecturally tight. For graphs with no cycle shorter than `2k` (girth `≥ 2k`) the right exponent is `1 + 1/(k−1)`.
    The cited bound is for `C_{2k}` alone. For `k = 3`, girth-6 bipartite graphs with `Ω(n^{3/2})` edges exist, so
    `O(n^{4/3})` is false. The rest of §6 uses the correct exponent (`z(n^{2/5}, C_{<6}) = Θ(n^{3/5})`,
    `m = Θ(a^{1+1/(k−1)})`), and "known for `k ∈ {3, 4, 6}`" matches the corrected exponent. (`ex_bound_misquoted`)
  - "The total number of vertices is `n^{2/5} · n^{3/5} = n`" ignores the about `2q` tree vertices. Our parameter choice
    accounts for every vertex and pads to exactly `n`.
  - The output convention ("each node computes an approximation") and the randomized communication bound (public coins
    are needed, since middle pipe nodes are simulated by both players) are left implicit. See the model below.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous deterministic CONGEST (`Cslib.Congest.Algorithm`) on an arbitrary node type `V` with `|V| = n`. Node names are
  the IDs. Messages have `B` bits per edge, direction and round. There are no failures. The network is the underlying
  undirected unweighted graph. Node `v`'s input is its incident arcs with their directions (`WDigraph.view`), or its incident
  edges with their weights (`WGraph.view`).
* Girth (`mwc`) is the minimum weight (directed: length) of a simple cycle, `∞` if there is none. These are the definitions of
  the companion formalization `Papers/PODC2024/MinWeightCycleCongest`.
* Output convention `ApproxOutput`, the weakest one: every node outputs `none` or an estimate, at least one node outputs, and
  every estimate lies in `[girth, α · girth]`. Algorithms only have to be correct on unweighted digraphs (directed case) or on
  weighted graphs with positive integer weights in `{1, …, Wm}`, `Wm ≥ kMn` (undirected case), of diameter `≤ 2 log₂ n + 4`. So the theorems
  also cover weighted directed algorithms and the small-diameter claim.
* Randomized algorithms give each node a private random string. Since nodes in the middle are simulated by both Alice and
  Bob, the simulation yields a *public-coin* protocol. The randomized bounds are therefore conditional on the public-coin
  randomized lower bound for set disjointness (Razborov / Kalyanasundaram–Schnitger), which enters as the hypothesis
  `PubRandDisjLB δ κ`. That hypothesis quantifies over nonempty finite coin spaces with `κ : ℝ`. It is not formalized.
* `H` is any bipartite graph of girth `≥ 2k`; the paper takes an extremal one. The shortcut tree is a balanced binary
  (segment) tree of depth `d ≥ log₂ q`. Pendant padding vertices on the root make the node count exactly `n`.
* Theorem 6.2's hypothesis `DenseHighGirth k` is the bipartite form of the Erdős–Simonovits conjecture: for every `a` there
  is a bipartite graph with sides of size `a`, girth `≥ 2k` and `≥ c · a^{1+1/(k−1)}` edges. We **prove** it for `k = 3`
  with the points–lines incidence graph of the affine plane over `ZMod p` and Bertrand's postulate. The cases `k = 4, 6`
  (generalized polygons) are not formalized.
* Explicit bounds. Fixed parameters: `q ≤ 2T + 1` or `|E(H)| ≤ 2T(d + 1)B + 2` (randomized: `κ|E(H)| ≤ …`). Asymptotic:
  `C · n^{k/(2k−1)} ≤ (T + 1)(B + 1)(log₂ n + 2)`, i.e. `T = Ω(n^{k/(2k−1)} / (B log n))`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Claim 6.1(1) (`girth = 2q`) | `dGraph_mwc_of_inter` | `Cycles.lean` |
| Claim 6.1(2) / §6.2 (`girth ≥ 2kq`) | `dGraph_mwc_of_disj` | `Cycles.lean` |
| Claim 6.2(1), corrected (`≤ 2(q−1) + 2W`); the stated value is too large | `uGraph_mwc_of_inter`, `claim_6_2_value_lt` | `Cycles.lean`, `Theorems.lean` |
| Claim 6.2(2) / §6.2 (`girth ≥ 2kW`) | `uGraph_mwc_of_disj` | `Cycles.lean` |
| Shortcut tree: diameter `≤ 2(d + 1)` | `ediam_le` | `Network.lean` |
| Das Sarma et al. simulation (moving cut), general | `Cslib.Congest.MovingCutFamily.simulation`, `rand_simulation` | `Podc/…/Congest/MovingCut.lean` |
| …for this network (`≤ d + 1` arcs per round) | `gadgetFamily`, `card_toA_le`, `card_toB_le`, `cover` | `Network.lean` |
| Theorem 6.1 (fixed parameters, any `k`; det. / rand.) | `theorem_6_1`, `theorem_6_1_rand` | `Theorems.lean` |
| §6.1 weighted version (det. / rand.) | `theorem_6_1_weighted`, `theorem_6_1_weighted_rand` | `Theorems.lean` |
| Theorem 6.1: `Ω̃(n^{3/5})`, unconditional (directed / weighted) | `theorem_6_1_directed_asymp`, `theorem_6_1_weighted_asymp` | `Theorems.lean` |
| Theorem 6.2 (directed / weighted; det. / rand.) | `theorem_6_2_directed`, `theorem_6_2_weighted`, `…_rand` | `Theorems.lean` |
| Erdős–Simonovits for `k = 3` (girth-6 graphs with `a^{3/2}/9` edges) | `denseHighGirth_three` | `PointsLines.lean` |
| §6 quoted bound `ex(n, C_{<2k}) = O(n^{1+1/k})` is false for `k = 3` | `ex_bound_misquoted` | `Theorems.lean` |

**Not formalized.** The upper bounds of §§3–5, which are randomized w.h.p. algorithms. The unconditional cases `k = 4, 6` of
Theorem 6.2. The remark on Lazebnik–Ustimenko–Woldar graphs. The randomized communication complexity of set disjointness.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: full-information flooding outputs the exact girth of every graph of diameter `≤ D` in `D` rounds
(`gather_approx_directed_diam`, `gather_approx_undirected_diam`), so the algorithm hypotheses of Theorem 6.2 can be met with
`T = 2 log₂ n + 4` (`NonVacuity.lean`). `DenseHighGirth 3` is proved, so the `k = 3` theorems are unconditional.
`PubRandDisjLB` requires nonempty coin spaces. Without that requirement it would force `κ ≤ 0`, the pitfall documented for
`RandDisjLB` in the companion folder. The CONGEST model, protocols and the fooling-set bound `CC(DISJ_K) ≥ K` come from CSLib
(`Cslib.Computability.Distributed.Congest`). The moving-cut simulation is new: `Podc/Computability/Distributed/Congest/MovingCut.lean`.

**CSLib candidates.** `Podc/Computability/Distributed/Congest/MovingCut.lean` (moving-cut simulation, public-coin protocols).
`approx_movingCut_lowerBound`, `approx_movingCut_rand_lowerBound` and `PubRandDisjLB` (`LowerBound.lean`). `stutterWalk` and
`egirth_le_card_of_stutter`: a closed sequence with distinct non-stutter steps gives a circuit, so `egirth ≤` the number of
steps (`Cycles.lean`). `bipGraph_even_length_iff` and `six_le_egirth_bipGraph` (`PointsLines.lean`).
