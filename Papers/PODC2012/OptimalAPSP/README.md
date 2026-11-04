# Optimal Distributed APSP — PODC 2012

Stephan Holzer, Roger Wattenhofer. *Optimal Distributed All Pairs Shortest Paths and Applications.* PODC 2012.
DOI [10.1145/2332432.2332504](https://doi.org/10.1145/2332432.2332504). Formalized version: the authors' "preliminary
full version" of 22.05.2012 (38 pp., with proofs; no arXiv version); numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The headline results hold: Algorithm 1 computes APSP in `O(n)` CONGEST rounds (Lemma 1,
Theorem 1, Lemmas 2–6), and the diameter lower bounds (Theorems 4, 8, 9 with Lemmas 8, 9, 15 and the exact parts
of Lemmas 10, 11, 16, Theorem 11) are proved. **Theorem 5 is false**: Algorithm 2, the S-SP algorithm, computes
wrong distances already on a triangle, and still does so with any tie-breaking rule and any neighbour numbering.

## Mistakes in the paper

### ❌ Theorem 5 (Algorithm 2 computes S-SP in time `O(|S| + D)`)
Algorithm 2 outputs wrong distances: on the graph with edges `1-3, 1-4, 3-4, 2-4` and `S = {2, 3, 4}`, node `3` ends
with `δ[4] = 2` although `3` and `4` are adjacent (`Alg2.exB_wrong`, `Alg2.theorem5_false`).

**Impact.** Theorem 5, as a claim about Algorithm 2, is false, and running the algorithm longer does not help
(`Alg2.not_eventuallyCorrect`). Theorem 6, Corollary 4 and Theorem 7 (the `(×, 1+ε)` approximations of
eccentricities, diameter, radius, center, peripheral vertices and girth) use Algorithm 2 and are therefore not
established by the paper. Their bounds are still plausible, because a correct `O(|S| + D)` algorithm for S-SP is
known from later work, for example Lenzen–Peleg's source detection (PODC 2013). The headline APSP result does not
use Algorithm 2.

**Details.** In round 1 nodes `3` and `4` send their own IDs to each other. The smaller ID wins the edge, so ID `4`
does not cross. Node `4` then sends the smaller ID `2` to node `3` first. Meanwhile ID `4` crossed the edge `4 → 1`,
and node `1` forwards it to `3` in round 2 with `δ = 2`. When the direct copy finally arrives, `3` already knows ID
`4` and ignores it. The run has no ties, and `Alg2.exB_wrong` checks all 24 neighbour numberings, both for the
paper's rule (the lowest neighbour index wins) and for "take the smallest `δ` received in the round". The proof
of Theorem 5 assumes that the same smaller IDs delay ID `u` on every path. That is false: whether a message is
delayed on an edge depends on what the other endpoint sends at that moment.

The minimal counterexample is the triangle `{1, 2, 3}` with `S = {1, 3}`. ID `3` reaches node `1` in round 2
simultaneously from `2` (with `δ = 2`) and from `3` (with `δ = 1`). If node `1` numbers its neighbours by
increasing ID, the lower index (node `2`) wins, so `δ[3] = 2` (`Alg2.triangle_wrong`). The round budget `|S| + D'` with `D' = 2·ecc(1)` is also too small. On `K₄` with a pendant
node `5` attached to `1` and `S = {1, 2, 3, 4}`, node `5` has no `δ` for ID `4` after the 6 rounds
(`Alg2.exC_late`).

**Repair.** None formalized. A correct algorithm forwards tokens in order of (distance, ID), not by ID alone.

### Typos and slips
- §5.2: the bit index `k(n)·(μ − k(n) + 1) + ν` of the edge `(l_ν, l_μ)` is out of range `[k(n)² − 1]`, and
  Figure 1 uses a third indexing. Any bijection works; Lean indexes the inputs by `Fin k × Fin k`.
- §7.1: in Theorem 9's proof "`i ∈ [n − 1]`" should be `i ∈ [k(n)² − 1]`; in `E_b` "`i ∈ [n − 4k(n) + 1]`" should
  be the index range of `V_b`'s fill-up nodes (and with `[k] = {0, …, k}`, `V_b`'s "`[n − 4k(n) − 2]`" is one too
  many); the prose on p. 28 writes the lower clique as "`{k(n), …, k(n) − 1}`" (the formal `E_a` has
  `{k(n), …, 2k(n) − 1}`); Figure 2's caption uses a different bit indexing than `E_a`.
- Lemma 16's proof says "diameter 2 from graphs of diameter 2" (meant: 3). Theorem 11's proof says
  "`n − 1`" nodes in the 2-neighbourhood (meant: `n`, since `v ∈ N₂(v)`).
- Claim 2 says `p + 3 = d/2 + 2` is "less than `d`". It equals `d` for `d = 4`; "at most" is what is used.

## Proof gaps (statements true)

### 🛠️ Lemma 9 (disjoint ⇔ diameter `d`) and Theorem 4
For disjoint inputs the proof only shows `diam ≤ d`; that the diameter is not smaller (so *exactly* `d`) is never
argued.

**Impact.** Statement true; repaired (`lemma9`). It needs `k(n) ≥ 1`, which follows from `n ≥ d + 6`.

**Repair.** For disjoint inputs the two path ends `l'_ν` (upper) and `r'_μ` (lower) are at distance exactly
`2p + 2 = d`. The lower bound is proved with a potential that changes by at most one along edges.

### 🛠️ Lemma 8 (non-disjoint ⇒ diameter `d + 2`)
The upper-bound part says that any two nodes of `G_a` are within `p + 3` "via `c₀`", which is false for `p ≥ 2`
(two path ends `l'_ν, l'_ν'` are at distance `2p + 2`).

**Impact.** Statement true. The bound actually needed, `≤ d + 2 = 2p + 4`, holds (`lemma8`, `claim2`).

### 🛠️ Theorem 4 (construction for odd `n`)
Each side receives `n/2` nodes, which is impossible for odd `n`, although the theorem claims every `n ≥ d + 6`.

**Impact.** Statement true; the Lean construction splits the fill-up nodes `⌊r/2⌋ / ⌈r/2⌉` (`theorem4`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous CONGEST, deterministic, no failures, CSLib's `Cslib.Congest.Algorithm V I σ B`. Vertex names are the
  IDs. Each round, every node sends a `B`-bit message to each neighbour and updates its state.
- Upper bounds are written with typed messages (`Cslib.Congest.TAlgorithm`, staged in
  `Podc/Computability/Distributed/Congest/Typed.lean`). They are compiled to `⌈log₂ |M|⌉`-bit messages with the
  same executions (`run_toAlgorithm`).
- Algorithm 1 uses the paper's assumptions: `n` is known (`V` is a `Fintype`), there is a known root `r` (the node
  "with ID 1"), and IDs are ordered (`LinearOrder V`, used for the smallest child). The input is ignored, since
  nodes learn their neighbours from messages.
- Algorithm 1 runs in three stages switched by a round counter:
  - rounds `1…n`: BFS from `r` builds `T₁`;
  - from round `n + 1`: depth-first pebble plus BFS waves, all distances known after `5n` rounds;
  - from round `5n`: max/min flooding of eccentricities, so after `6n` rounds every node knows the diameter and
    the radius.

  Since nodes know `n`, `T₁` is built in `n` rounds rather than `O(D)`. This only changes constants.
- Messages carry at most one tree message, one pebble bit, one BFS token `(ID, distance)` and two numbers `< n + 1`.
  That is `≤ 5⌈log₂(n+1)⌉ + 2` bits (`msgBits_le`).
- The pebble (`Pebble.lean`) is analysed as a global transition system and then shown to be followed by the
  distributed run (`pebble_corr`). Remark 3's `O(n)` traversal is `firstVisit_le`: at most `3n − 1` slots including
  the waiting slots. It is proved with a potential that grows by one per slot.
- Lower bounds use CSLib's two-party simulation (`LBFamily`, node input = adjacency row) and the proved
  deterministic bound `CC(DISJ_K) ≥ K`. Algorithms only need to be correct on connected graphs inside the paper's
  promise: diameter in `{d, d+2}`, resp. `{2, 3}`.
- The paper states ε-error, public-coin randomized lower bounds. Lean proves the deterministic versions outright.
  The randomized versions (`theorem4_randomized`, `theorem8_randomized`) use private coins and are conditional on
  a hypothesis `RandDisjLB` (randomized CC of disjointness ≥ κK, Kalyanasundaram–Schnitger/Razborov), which is not
  proved.
- Output conventions:
  - "each node knows X" means the value is a field of the node's state after `T` rounds;
  - lower bounds use per-node read-outs. A node accepts iff its local value passes a threshold, and CSLib's
    "all nodes accept" replaces the paper's `O(D)` aggregation.
- Algorithm 2 (`Algorithm2.lean`) is modelled literally on `Fin n`, with the pseudocode's neighbour index order. A
  received ID that is already known is ignored and not removed from `L_i`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Remark 3 (traversal in `O(n)`) | `PState.firstVisit_le`, `PState.iter_done` | `Pebble.lean` |
| Lemma 1 | `PState.lemma1`, `arr_sep` | `Pebble.lean`, `Algorithm1.lean` |
| Theorem 1 | `theorem1` (`theorem1_dist`, `msgBits_le`) | `Algorithm1.lean` |
| Lemmas 2–6 | `lemmas2to6` (`lemma2` … `lemma6`) | `Algorithm1.lean` |
| Theorem 5 (false) | `Alg2.theorem5_false`, `Alg2.exB_wrong`, `Alg2.triangle_wrong`, `Alg2.exC_late`, `Alg2.not_eventuallyCorrect` | `Algorithm2.lean` |
| Lemma 8, Lemma 9, Claim 2 | `lemma8`, `lemma9`, `claim2` | `DiamApproxLB.lean` |
| Theorem 4 | `theorem4`, `theorem4_bound` (`⌊(n−4)/(d+2)⌋ ≤ 4TB + 2`), `theorem4_randomized` (conditional) | `DiamApproxLB.lean` |
| Lemma 10, `(+,1)` parts | `lemma10_eccent_plusOne`, `lemma10_apsp_plusOne` | `DiamApproxLB.lean` |
| Lemma 15, Theorem 9 | `Diam23.shape`, `Diam23.diam_eq_two_iff`, `Diam23.radius_eq_two`, `Diam23.center_eq_univ_iff` | `Diam23LB.lean` |
| Theorem 8 | `theorem8`, `theorem8_accepts`, `theorem8_linear` (`n ≤ 16TB + 13`), `theorem8_randomized` (conditional) | `Diam23LB.lean` |
| Lemma 10, exact parts | `lemma10_apsp`, `lemma10_eccentricity`, `lemma10_peripheral` | `Diam23LB.lean` |
| Lemma 11, exact part | `lemma11_center` | `Diam23LB.lean` |
| Lemma 16, Theorem 11 | `lemma16`, `theorem11` | `Diam23LB.lean` |

**Proof remarks.**
- Lemma 1 needs only that the pebble walks along graph edges and waits one slot at a first visit. Revisits need no
  wait.
- With the "wait one slot" rule, `BFS_u` reaches `w` exactly in round `arr u + d(u, w)`, and these rounds are
  pairwise distinct for fixed `w` (`bfs_inv`). So a message never has to carry two tokens.
- The `(+,1)` part of Lemma 10 needs no `O(D)` aggregation either: a node rejects if its own estimate is `≥ d + 2`.

**Not formalized.**
- The `+D` terms of the lower bounds, odd `d` in Theorem 4 (Remark 5), and the `(×, 3/2−ε)` and `(+,1)` parts of
  Lemma 11. Of these, the proof of the `(+,1)` center part is only a sentence ("for a similar reason"). In the
  Theorem 4 graphs with `k(n) ≥ 2` the radius is `p + 2` whether or not the inputs are disjoint (brute force for
  small `k`, `p`), so a `(+,1)`-approximate center does not obviously reveal the diameter; the claim is neither proved
  nor refuted here.
- Lemma 7 / Claim 1 (girth), Lemmas 12–14, Theorems 6, 7, 10, Corollaries 1–4, and the parts of Lemma 10 that
  cite [22].

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- Non-vacuity of the lower-bound hypotheses: flooding / gathering algorithms satisfy them for large `B`
  (`theorem4_hyp_satisfiable`, `lemma10_apsp_plusOne_hyp_satisfiable`, `theorem8_nonvacuous`, `lemma16_nonvacuous`,
  …).
- The algorithm of `theorem1` is concrete (`apsp`).
- Models come from CSLib `Cslib.Computability.Distributed.Congest.{LowerBound, Randomized, Gather}` and
  `Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree`.
- `Algorithm2.lean`'s counterexamples are checked by kernel evaluation (`decide +kernel`).

**CSLib candidates.**
- `Cslib.Congest.TAlgorithm` / `toAlgorithm` / `run_toAlgorithm` (staged in `Podc/`).
- The generic pebble traversal `PState` (any rooted tree; `firstVisit_le`, `dist_pos_le`).
- The graph lemmas in the lower-bound files marked `-- CSLib candidate`: `le_edist_of_lipschitz`,
  `edist_le_of_descent`, `hom_edist_le`, `edist_comap_equiv`, `ediam_comap_equiv`, `eccent_comap_equiv`,
  `withOut`.
