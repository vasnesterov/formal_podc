# Deterministic Lower Bound for Dynamic Balanced Graph Partitioning — PODC 2020

Maciej Pacut, Mahmoud Parham, Stefan Schmid. *Brief Announcement: Deterministic Lower Bound for
Dynamic Balanced Graph Partitioning.* PODC 2020. DOI
[10.1145/3382734.3405696](https://doi.org/10.1145/3382734.3405696). Formalized version: the 3-page
brief announcement (no arXiv version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** Theorem 2.1 (every deterministic online algorithm for the
learning model is `Ω(kℓ)`-competitive, `k ≥ 3`, `ℓ ≥ 2`) holds, even with a slightly better
constant: `((k-2)(ℓ-1)-2)/2` instead of `((k-2)(ℓ-1)-4)/2`. But the adversary in the paper does not
work as written. It assumes that the algorithm always keeps the revealed ground sets together, and
it gets stuck when the pivot is the one node of `B`'s home cluster outside `B`. Both gaps are easy to
fix. The paper gives no proofs for Theorem 2.2 (PPL is `O(kℓ)`-competitive) and Lemma 3.1 (for
`k = 3` a repartition needs at most two swaps). We prove both: Theorem 2.2 with ratio `2(kℓ-1)` in
the static learning model. Theorem 3.2 (ALG3 is `O(ℓ)`-competitive) has no proof in the paper and
is not formalized.

## Mistakes in the paper

* **Theorem 2.1, proof gap: the algorithm is assumed to keep every ground set in one cluster.** The
  proof says "Any competitive algorithm under the learning model maintains a perfect partition of
  ground sets" and builds its adversary on that. A deterministic algorithm may split a revealed
  ground set, for example by moving a node of `B` away for a while, and nothing in the proof covers
  this. The statement is still true. We add *repair requests*: whenever the algorithm's current
  configuration splits a ground set, the adversary requests a split pair, which costs the algorithm
  at least `1` (it pays for the request or migrates). The adversary moves on to the next pivot step
  only when all ground sets are back together. Between two such moments the algorithm migrates at
  least two nodes (`LB.two_le_dist`; this also covers an algorithm that moves `B` instead of the
  pivot). If the algorithm never puts the ground sets back together, the repair requests alone
  make its cost large enough. (`theorem_2_1`)
* **Theorem 2.1, proof gap: the pivot step is undefined when the pivot is `z`.** Let `z` be the
  node of `B`'s home cluster that is not in `B`. The paper does not control `z`: during the
  requests inside `B` the algorithm may move `z` away, so `x₀ ≠ z`, and later choose `z` as a new
  pivot. Then the only other ground set with `z`'s origin is `B` itself, and `B` is in the same
  cluster as `z`. So the required "ground set of the same origin residing in a different cluster"
  does not exist. Following the text literally, the adversary would request `(z, b)` with
  `b ∈ B`. That request is internal, and `B ∪ {z}` then fills the cluster, so no pivot is left and
  the construction stops after `O(1)` swaps. Fix: make `z` part of the first pair `{x₀, y₀}`. In
  our adversary `B` is never requested before the first pivot step, so `x₀ = z`, and `y₀` comes
  from another cluster. Every later pivot then has an origin other than `B`'s home cluster. With
  `k ≥ 3` it always has a partner of the same origin (`LB.grow_shape`).
* **Theorem 2.1: the competitive-ratio notion is left implicit.** In the learning model every
  sensible algorithm has bounded total cost (PPL pays at most `2(n-1)α·n`). So no lower bound is
  possible if the additive constant `β` may depend on `α`. The bound holds for strict
  competitiveness, or for `β` independent of `α` (letting `α → ∞`). We prove
  `c ≥ ((k-2)(ℓ-1)-2)/2 - β/(4α)` for every `(c, β)`-competitive algorithm with `c ≥ 0`.
  (`theorem_2_1_competitive`, `theorem_2_1_omega`)
* **Theorem 2.2 is stated without proof; it is true.** PPL never pays for a request. While
  `D = dist(init, P*)` for a perfect partition `P*`, every configuration PPL visits is within `D`
  of `init`. Each repartition merges two components, so there are at most `n - 1` of them, and each
  costs at most `2αD`. Any offline algorithm with finite cost ends in a perfect partition and pays
  at least `αD`. This uses "pairs communicate forever": on a *finite* sequence OPT may simply pay
  for the requests (one request: OPT = 1, PPL ≥ 2α). Section 2 makes "communicate forever" part
  of the model, so this does not contradict Theorem 2.2. (`theorem_2_2`, `theorem_2_2_kl`)
* **Lemma 3.1 is stated without proof; it is true.** For clusters of size `3`, if a balanced
  configuration respecting the merged components exists, one exists at distance at most `4` (two
  swaps). The hard case is when `a` and `b` are singletons sitting next to pairs. A counting
  argument then finds a cluster made of three singletons (`K3.exists_triple`).
  (`K3.lemma_3_1`, `K3.lemma_3_1_closest`)
* **Slips.** In the final count of the proof of Theorem 2.1, `B` contributes `|B| - 1 = k - 2` to
  `Σ(|C*| - 1)`, but the proof subtracts `k - 1`. It also stops at `< ℓ + 3` isolated nodes, while
  `< ℓ + 2` suffices, because `B`'s home cluster has no isolated node. Both slips only weaken the
  bound. The pigeonhole step needs only `ℓ` isolated nodes, not `ℓ + 1`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Not a distributed model: online algorithms against an adaptive adversary. `n` nodes, `ℓ`
  clusters (`Fin ℓ`) of capacity `k`. A configuration `V → Fin ℓ` is balanced if every cluster has
  at most `k` nodes; with `n = kℓ` this means exactly `k`. There is no resource augmentation.
* Serving request `(u, v)` costs `1` if the configuration in which it is served separates `u` and
  `v`. Migration costs `α ≥ 1` per moved node. Before serving a request the algorithm may
  repartition.
* A deterministic online algorithm (`OnlineAlg`) is a map from the requests revealed so far to a
  balanced configuration. Adaptivity of the adversary is automatic. `OPT` (`optCost`) is the
  minimum over all balanced offline schedules starting in the initial configuration.
* Learning model, finite form (`IsLearningInput`): the requests admit a perfect partition. Static
  form (`IsStaticLearningInput`, Section 2): an infinite sequence that admits a perfect partition,
  in which every communicating pair communicates infinitely often. The lower bound is proved in
  both forms. Theorem 2.2 needs the static form (see above).
* Lower-bound instance: nodes `Fin ℓ × Fin k` (cluster of origin, index), initial partition
  `Prod.fst`. A lower bound for one instance is a lower bound for the problem.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (`1 ≤ OPT ≤ 4α`, `ALG ≥ 2α((k-2)(ℓ-1)-2)`) | `theorem_2_1` | `Main.lean` |
| Theorem 2.1, ratio forms | `theorem_2_1_ratio`, `theorem_2_1_competitive`, `theorem_2_1_paper`, `theorem_2_1_omega` | `Main.lean` |
| Theorem 2.1, static infinite input | `theorem_2_1_static` | `Main.lean` |
| "holds also in the general model" | `theorem_2_1_general` | `Main.lean` |
| The adversary, perfect partition `P*` | `LB.lower_bound_core`, `LB.exists_perfect` | `LowerBound.lean` |
| Theorem 2.2 (PPL is `O(kℓ)`-competitive) | `theorem_2_2`, `theorem_2_2_kl` (ratio `2(kℓ-1)`) | `PPL.lean` |
| OPT lower bound in the static model | `schedule_lb` | `PPL.lean` |
| Lemma 3.1 (`k = 3`: at most two swaps) | `K3.lemma_3_1`, `K3.lemma_3_1_closest` | `Lemma31.lean` |

**Not formalized.** Theorem 3.2 (ALG3 is `O(ℓ)`-competitive for `k = 3`): the paper gives no proof
and does not fully specify ALG3's phases. The matching `Ω(ℓ)` lower bound for `k = 3` in the
general model is `theorem_2_1_general` with `k = 3`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `theorem_2_1_static` builds static learning inputs, so the hypothesis
of Theorem 2.2 is satisfiable. PPL is a concrete `OnlineAlg` (`ppl`). The model (`Model.lean`) is
self-contained on top of Mathlib. The generic online-algorithm and cost definitions are a CSLib
candidate.
