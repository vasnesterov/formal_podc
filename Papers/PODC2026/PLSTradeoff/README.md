# Near-Resolution of the Tradeoff Conjecture for PLS — PODC 2026

Arnold Filtser, Orr Fischer. *Near-Resolution of the Tradeoff Conjecture in Distributed Proof
Labeling Schemes.* PODC 2026. DOI
[10.1145/3796701.3815966](https://doi.org/10.1145/3796701.3815966). Formalized version: arXiv
[2605.19078](https://arxiv.org/abs/2605.19078) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The two tradeoff theorems hold with explicit constants: for connected graphs, a 1-PLS of
cost `p` gives an `O(t log n)`-PLS of cost `O(⌈p/t⌉)` (Theorem 1.2), for every graph the warm-up gives an
`O(t log n)`-PLS of cost `O(⌈p/t⌉ + log n)` (Corollary 4.7), and the lower bound of Theorem 1.6 also holds. What
fails is repaired locally: Lemma 5.6 when `n` is small compared with the string length, and the proofs of Lemmas
4.5, 5.1 and 5.2. Theorem 1.4, the minor-free result, was checked only assuming the padded decompositions of
Conroy–Filtser.

## Mistakes in the paper

### 🔧 Lemma 5.6 (sharing an `r`-bit string with `O(1)` bits per node)
Lemma 5.6 is false when `n < r/O(1)`: with `c` bits per node a graph on `n` nodes can carry fewer than
`2^{(c+1)n}` distinct labelings, so it fails once `r > (c+1)n`.

**Impact.** The correct cost is `O(1 + r/n)` (`exists_stringShare`). Theorem 1.2 only shares `r ≈ 2 log n` bits, so
it is unaffected.

**Details.** The lemma promises the sharing for every `r`. The proof's Lemma B.1 indeed assumes `|V| > r`.

### ✏️ Slips
- Theorem 1.6: the claim that every `t`-ball of `G_{t,m}` contains `Ω(|V|)` nodes, for all `t, m ≥ 1`, is false for
  `t = 1`: a node of an even layer has only two neighbours, so its 1-ball has 3 nodes while `|V| = 2m + 3`
  (`Layered.ball_t1_counterexample`). For `t ≥ 2` the claim holds with constant `1/3` (`Layered.ball_large`), and
  the cost lower bound `Ω(m/t)` is not affected.
- Lemma 5.5 (Newman's trick): the union bound undercounts the graphs whose identifiers come from `[poly(n)]`. It
  still works. (`exists_good_family`)
- "Cost `O(⌈p/t⌉)`" should read `O(⌈p/t⌉ + 1)` when `p = 0`.

### Typos
- Lemma 4.2 and Theorem 1.4 need `t ≥ 2/δ` (the paper writes "`t = Ω(1)`").

## Proof gaps (statements true)

### 🔧 Lemma 4.5 (radius of the TS certification)
The proof claims a `(3t+2)`-PLS, but a node reconstructs clusters `{w ∈ B_{3t+2}(u) | …}` for nodes `u` at
distance up to `3t+4`, which needs radius about `6t+6`.

**Impact.** Statement true; repaired with radius `3t+2` (`exists_tsCert`).

**Repair.** We search for cluster mates within radius `2t`, which suffices (the diameter checks show `Ĉ_u = Ĉ_v`
for `u ∈ Ĉ_v`), and then radius `3t+2` is enough.

### 🔧 Lemma 5.1 (last inequality)
The final inequality `(1+1/t)^{t log n} > n` only gives `≥ n`, which is not enough for the contradiction.

**Impact.** Statement true; repaired (`card_bad_le`).

**Repair.** The missing strict factor comes from the first bad radius.

### 🔧 Lemma 5.2 and Corollary 5.4 (case `n < 2t log n`)
Lemma 5.2 and Corollary 5.4 assume `n ≥ 2t log n`, while Theorem 1.2 does not, and the case `n < 2t log n` is never
treated.

**Impact.** Statements true; repaired (`card_not_allClustered`).

**Repair.** Our counting covers every `n`, using that a radius-`k` ball in a connected graph has `≥ min(n, k+1)`
nodes.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Nodes and configurations.** Nodes form a fixed finite type `V`. Its linear order gives the
  identifiers, and `n = |V|` is known to everybody. A configuration is a graph `G : SimpleGraph V`
  with inputs `I : V → ι`. A family is a set of graphs `𝒢` together with all inputs.
- **Labels.** Labels are bit strings, and the cost is the honest prover's maximum label length on
  yes-instances.
- **Locality.** An `R`-PLS verifier is any function whose output at `v` depends only on the
  `R`-round LOCAL view of `v` (`ViewEq`/`IsLocal`): edges incident to nodes at distance `< R`, and
  inputs and labels at distance `≤ R`. For `R = 1` this is the classical PLS view. `ViewEq` and
  `IsLocal` are the shared notions of `Cslib/Computability/Distributed/Local/OnlineLocalLocality.lean` (`Cslib.Local.ViewEq`,
  `Cslib.Local.IsLocal`) applied to the labelling `u ↦ (I u, ℓ u)`; `viewEq_iff` and `isLocal_iff`
  state them in the paper's form. Verifiers are deterministic and need not be computable, as in
  the paper.
- **Randomness.** Section 5's randomness is replaced by counting over all radius assignments.
- **Connectivity.** Theorem 1.2 assumes connected graphs, as the paper does.
- **Identifiers and `n`.** All graphs of a family live on the same node set `V`, so the identifier
  space is exactly the node set (identifiers `[n]`), and the verifier formally knows it. This is a
  special case of the paper's model, where identifiers come from `[poly(n)]`. Theorem 1.2 uses it:
  the Newman family of radius assignments (`exists_good_family`) is a function on `V`, and the
  counting runs over the graphs on `V` only. The paper's setting needs the same counting over
  graphs on all `n`-subsets of `[poly(n)]`, which still works (see differencies.md, item 6) but is
  not formalized.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1 (`t`-PLS) | `PLS`, `PLS.CostLE`, `IsLocal` | `Basic.lean` |
| Definitions 2–4, Lemmas 3.1, 3.3, 3.4 | `TSPartition`, `ClusterDegenerate`, `TSCert`, `TSPartition.ofDegenerate`, `exists_ball_subset`, `hset_disjoint` | `TSPartition.lean` |
| Lemma 3.5 | `sound_of_good` | `Tradeoff.lean` |
| Lemma 3.2 (TS partition ⇒ tradeoff) | `tradeoff_of_tsCert` | `Tradeoff.lean` |
| Lemma 4.5 (`O(log n)` TS certification) | `exists_tsCert` | `CertifyTS.lean` |
| Warm-up `(O(t log n), 1/t)`-TS partition | `exists_degenerate_partition`, `exists_tsPartition` | `BallCarving.lean` |
| Corollary 4.7 | `warmup_tradeoff` | `WarmUp.lean` |
| Definition 6, Lemmas 4.2, 4.3 | `PaddedDecomp`, `exists_cluster_of_padded`, `exists_tsPartition_of_padded` | `Padded.lean` |
| Theorem 1.4 (assuming [CF25]) | `tradeoff_of_padded` | `Padded.lean` |
| Lemmas 5.1, 5.2, 5.3, 5.5 | `card_bad_le`, `card_not_allClustered`, `isDegenerate_of_allClustered`, `exists_good_family` | `RandomCarving.lean` |
| Lemma 5.6 (+ B.1) | `exists_stringShare` | `StringShare.lean` |
| Lemmas 5.7–5.12 | `tsCertGeneral` | `GeneralTS.lean` |
| **Theorem 1.2** | `tradeoff_general` | `GeneralGraphs.lean` |
| Lemmas 6.3, 6.4, **Theorem 1.6** | `Layered.lemma_6_3`, `Layered.lemma_6_4`, `Layered.theorem_1_6` | `LowerBound.lean` |

The explicit bounds are as follows (`K = t⌈log₂ n⌉`):

| Result | Radius | Cost |
|---|---|---|
| Theorem 1.2 | `40K + 32` | `2⌈(2p+1)/t⌉ + 64` |
| Corollary 4.7 | `12K + 14` | `4⌈log₂ n⌉ + 2⌈(2p+1)/t⌉ + 10` |
| Theorem 1.4 (conditional, `t ≥ 2/δ`) | `3t + 2` | `4⌈log₂ n⌉ + 2⌈2β(2p+1)/t⌉ + 10` |

For Theorem 1.6 the bound is `m ≤ 4(t+1)p` for every `t`-PLS.

**Not formalized.**
- The padded decompositions of Conroy–Filtser (Theorem 4.1) and Bartal (Theorem 4.6). Theorem 1.4
  takes them as a hypothesis.
- Corollary 1.3 (MST), which needs Korman–Kutten.
- Planarity of `G_{t,m}`.
- Lemma 6.1 is not formalized as such; a direct fooling-set argument replaces it.
- The closing remarks of Section 5 on removing the knowledge of `n` and the connectivity assumption.

**CSLib candidates** (marked `-- CSLib candidate`):
- the PLS model (`PLS`, `Basic.lean`); views, locality and the localization trick (`loc`, `mask`)
  are in the shared `Cslib/Computability/Distributed/Local/OnlineLocalLocality.lean`;
- the string encoding (`encList`/`decList`, `chunk`) is now shared code in CSLib,
  `Cslib/Foundations/Data/List/BitEncoding.lean` (namespace `Cslib.BitEncoding`);
- ball sizes in connected graphs (`card_ball_ge`, `RandomCarving.lean`); the fibre counting along
  the identifier order and the union bounds of Lemmas 5.2/5.5 use the shared
  `Cslib/Probability/Finite/Uniform.lean` (`pow_mul_card_filter_forall_le`,
  `card_filter_exists_le`);
- generic carving into a cluster-degenerate partition (`exists_degenerate_of_carve`);
- induced subgraphs on all of `V` and connected sets of any size (`zG`, `zG_edist_le_ncard`,
  `exists_connSet`, `StringShare.lean`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
- *The hypotheses can be met.* `Layered.lemma_6_3` exhibits a 1-PLS, and `exists_tsCert` exhibits
  a TS certification on every graph family.
- *The constructions do work.* The warm-up and the random carving produce actual TS partitions
  (`exists_tsPartition`, `exists_good_family`).
