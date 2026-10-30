# Uniform Local Algorithms via Pruning — PODC 2011

Amos Korman, Jean-Sébastien Sereni, Laurent Viennot. *Toward More Localized Local Algorithms: Removing
Assumptions Concerning Global Knowledge.* PODC 2011. DOI
[10.1145/1993806.1993814](https://doi.org/10.1145/1993806.1993814). Formalized version: arXiv
[1512.03306](https://arxiv.org/abs/1512.03306) v1 (journal version, Distributed Computing); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The main transformers hold: Theorem 1, Theorem 2 (randomized: weak Monte-Carlo
to Las Vegas), Theorem 3 (deterministic case) and Theorem 4. They need a `+1` in their `O(·)` bounds
(degenerate case `f* < 1`), and the proofs of Theorems 2 and 3 need repairs. Observation 3.3 is false:
the maximal-matching pruning algorithm `P_MM` does not satisfy gluing for the paper's own encoding of
matchings. With matchings encoded by partner identities it is a pruning algorithm, so Corollary 1(vi) survives.

## Mistakes in the paper

* **Observation 3.3 is false.** In the paper, `u` and `v` are *matched* if they are adjacent, output the
  same value, and no other neighbour of `u` or `v` outputs that value. Take the path `v₀ — u₀ — u — v`
  with tentative output `(5, 5, 1, 2)`. `P_MM` prunes `W = {v₀, u₀}` (they are matched; `u` and `v` are
  neither matched nor surrounded by matched nodes). The residual edge `u — v` is correctly solved by
  `(5, 5)`. The combined output `(5, 5, 5, 5)` matches nobody, so gluing fails. A solution of the
  residual graph may reuse the values of pruned nodes, and the paper's "matched" notion looks at
  neighbours' values. This fails for any new inputs the pruning algorithm might assign
  (`observation_3_3_false`). Fix: output the partner's identity. The same pruning rule is then a pruning
  algorithm, and it needs 2 rounds instead of 3 (`observation_3_3_repaired`). Corollary 1(vi) holds for
  this encoding (`corollary_1_vi`).
* **Theorem 3: the proof's inverse functions are undefined.** The proof sets
  `g_j⁻¹(x) = min g_j⁻¹({x})` and uses `g_j(g_j⁻¹(x)) = x`. An ascending `g_j` need not take the value
  `x`, and the argument mixes reals with integer coordinates. Repair: take `g_j⁻¹(x) = max {y : g_j(y) ≤ x}`.
  We prove Theorem 3 by a direct reduction to Theorem 1: guesses for the correctness parameters `Γ`
  are computed from guesses for the time parameters `Λ`. This needs only `Λ`-monotone pruning, not
  `Λ ∪ Γ` (`theorem_3`).
* **Theorem 2: an unjustified step in the expected-time bound.** The proof claims `α_{i+1} ≤ K·α_i`
  "since `s_f` is moderately slow", where `α_i` is the number of rounds of the first `i` iterations of
  `τ`. This does not follow: only `|S_f(2^j)| ≤ s_f(2^j)` is known, and the actual sizes can be far
  smaller for some `j` and then jump. Repair: use the upper bound `α_{s+i} ≤ C·s_f(2^s)·2^s·(2a)^i`
  (`a` is the moderate-slowness constant). With the failure bound `(1−ρ)^{i(i+1)/2}` the series still
  converges, so the claimed bound holds (`theorem_2`).
* **Corollaries 3 and 4 apply the theorems to families that are not closed under inclusion.**
  Section 2 requires every family to be closed under inclusion, and a pruning algorithm must map the
  family into itself. The families `F_large`, `F_med` and "arboricity `o(√log n)`" are not closed
  (deleting isolated nodes lowers `n`). The bounds can be recovered by working on all graphs; we
  sketch this for Corollary 3 in [differencies.md](differencies.md) but did not formalize it. Corollary 4
  also needs the cited algorithm's time bound `f(ñ)` to hold for *every* good arboricity guess,
  including `ã = ñ`. The paper does not argue this; our `corollary_4` assumes it.
* **Degenerate cases and slips.**
  * Theorems 1–4 claim `O(f*·s_f(f*))` and `O(f_min)`. Both fail when `f* < 1`, since the transformed
    algorithm always spends at least one iteration. We prove `C·(f*·s_f(⌊f*⌋) + 1)` and `C·(f_j + 1)`.
  * Observation 3.2 needs `β ≥ 1`. The `(2,0)` case is degenerate.
  * Observation 3.3 says "monotone with respect to any parameter". It should say any *non-decreasing*
    parameter.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* LOCAL model with unique identifiers, synchronous and fault-free, with simultaneous wake-up. The
  identifiers are the elements of a type `V`.
* An instance is `(G, x : V → Option α)`. Its nodes are those with `x v ≠ none`, and its graph is the
  induced subgraph `res G x`. Pruned nodes get `none`, so residual instances live on the same type.
* An algorithm (`Alg`) gives every node's output after `t` rounds (`none` = not yet terminated). That
  output is a function of the radius-`t` view (CSLib `Cslib.Local.IsLocal`), and outputs are final.
  "Running time `≤ T`" means all nodes of the instance have output a solution by round `T`.
* A non-uniform algorithm is a family `A g` of such algorithms, one per guess vector `g`. It is
  required to work only for good guesses (`DependsWithTime`).
* Pruning algorithms (`Pruning`) run in constant time and satisfy solution detection and gluing
  (Section 3.2).
* The alternating algorithm (`Pruning.alg`) runs fixed-length stages known to every node, so all nodes
  stay synchronized and no synchronizer (Observation 2.1) is needed. A node outputs at the end of the
  iteration in which it is pruned.
* Randomness (Theorem 2): every node has a private random tape, i.i.d. with law `ν`. A randomized
  algorithm is an `Alg` on inputs `(x v, ω v)`. Outputs must be measurable in the tapes, inputs and
  outputs come from countable sets, and instances are finite. Every sub-iteration of `τ` reads a fresh
  coordinate of the tape `ℕ → R` (joint law: nested `Measure.infinitePi`). Las Vegas means correct
  for every tape whenever all nodes have output; the expected running time is a `lintegral` of the
  first round at which all nodes have output.
* The cited non-uniform algorithms ([4], [6], [19], [22], [34]) are hypotheses of the corollaries.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Observation 3.1(2) | `observation_3_1_2` | `Pruning.lean` |
| Observation 3.2 (`(2,β)`-ruling sets, MIS) | `rulingPruning`, `observation_3_2` | `Pruning.lean` |
| Observation 3.3: **false** | `observation_3_3_false` | `Pruning.lean` |
| Observation 3.3, repaired (partner encoding) | `mmPruning`, `observation_3_3_repaired` | `Pruning.lean` |
| Observation 3.4 (alternating algorithm correct, with running time) | `Pruning.runList_correct`, `Pruning.solvesWithin_of_runList_empty` | `Model.lean` |
| Observation 4.1 (additive: `s_f = 1`; product: `⌈log i⌉ + 1`) | `observation_4_1_additive`, `observation_4_1_product` | `Observation41.lean` |
| Theorem 1 | `theorem_1` | `Theorem1.lean` |
| Theorem 2 (weak Monte-Carlo → Las Vegas, expected time) | `theorem_2` | `Theorem2.lean` |
| Theorem 3 (deterministic) | `theorem_3` | `Theorem3.lean` |
| Theorem 4 | `theorem_4` | `Theorem4.lean` |
| Corollary 2 (MIS in `O(Δ + log* n)` and `O(g(n))`) | `corollary_2_delta`, `corollary_2_n` | `Corollaries.lean` |
| Corollary 1(vi) (maximal matching, partner encoding) | `corollary_1_vi` | `Corollaries.lean` |
| Corollary 4 | `corollary_4` | `Corollaries.lean` |
| Corollary 1(i) (Theorem 4 step) | `corollary_1_i` | `Corollaries.lean` |

**Not formalized.** The randomized case of Theorem 3, Section 5 (Theorem 5 and the coloring parts of Corollary 1), Corollary 3, the
synchronizer discussion of Section 2, and Section 6.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. `weakMonteCarlo_ignoreTape` (in `Theorem2.lean`) shows that the hypotheses of
`theorem_2` can be met (any deterministic algorithm, with ρ = 1). `NonVacuity.lean` instantiates every hypothesis of `theorem_1` on a toy problem and applies
the theorem. The MIS and matching pruning algorithms are non-trivial instances of `Pruning`.
The locality notions come from CSLib `Cslib.Computability.Distributed.Local.Locality`.

**CSLib candidates.** The terminating-algorithm model, the induced sub-instances and the
alternating-algorithm machinery in `Model.lean`. From `Theorem2.lean`: the stage-process failure bound
`measure_stageRun_mem_le`, the swap of nested `infinitePi` (`map_swap_tapes`, `iIndepFun_tapeAt`) and
`lintegral_le_of_phases`. All are marked `-- CSLib candidate`.
