# Lower bounds for MIS and bounded-outdegree dominating sets in trees — PODC 2021

Alkida Balliu, Sebastian Brandt, Fabian Kuhn, Dennis Olivetti. *Improved Distributed Lower Bounds for MIS
and Bounded (Out-)Degree Dominating Sets in Trees.* PODC 2021. DOI
[10.1145/3465084.3467901](https://doi.org/10.1145/3465084.3467901). Formalized version: arXiv
[2106.02440](https://arxiv.org/abs/2106.02440) v1; numbering follows it.

**Verdict: ⚠️ Minor statement issues.** The whole deterministic port-numbering part (§3) is correct: the
round-elimination step `Π_Δ(a, x) → Π_Δ(⌊(a−2x−1)/2⌋, x+1)` (Lemmas 6, 8, 9, Corollary 10), Lemmas 5, 11,
12 and the sequence of Lemma 13 (with an explicit condition in place of "`Δ` large enough") are all
formalized; Lemma 8 is proved in its "at most `max{T−1, 0}`" form, which is what its proof gives. Together with a Lean proof of the forward
direction of round elimination (Theorem 3), they give the `Ω(log Δ)` port-numbering lower bound for
`k`-outdegree dominating sets, `k ≤ Δ^ε`, with `ε = 1/6`. The only false statement is Lemma 15 (randomized
0-round failure probability ≥ `1/Δ⁸`), and only in the degenerate case `Δ = 1`.

## Mistakes in the paper

* **Lemma 15 is false for `Δ = 1` (degenerate case).** The lemma claims that for all `x ≤ Δ − 1` and
  `a ≥ 1`, every randomized 0-round algorithm for `Π_Δ(a, x)` fails with probability at least `1/Δ⁸`.
  For `Δ = 1` this bound is `1`. On the 1-regular tree `K₂`, output `M` or `A` with probability `1/2`
  each (both are node configurations of `Π_1(1, 0)`). The algorithm fails only on `MM` or `AA`,
  i.e. with probability `1/2`. The proof gives a failure probability of at least `1/(3Δ)²` and then
  uses `1/(3Δ)² ≥ 1/Δ⁸`, which needs `Δ ≥ 2`. The paper only uses large `Δ`, so nothing downstream is
  affected. We prove the lemma for `Δ ≥ 2`, with the better bound `1/(36Δ²)` that also covers
  algorithms whose outputs are not always valid configurations (`lemma_15`, counterexample
  `lemma_15_false_delta_one`).
* **Typos and tiny slips (no effect).**
  * §2.3, definition of `R̄`: `Σ_{Π''}` is "the sets that appear in the configurations of `E_{Π''}`",
    but `E_{Π''}` is defined from `Σ_{Π''}`. It should say `N_{Π''}`. Also "`Σ_{Π''} =⊆ …`".
  * Lemmas 5 and 11 implicitly need `k ≤ Δ` and `x ≤ Δ`. Without them the configuration
    `M^{Δ−x}X^x` does not exist. This is consistent with the paper's convention `0 ≤ a, x ≤ Δ`
    for the family.
  * In the proof of Lemma 8, the step "each `Yᵢ` contains `B`" does not need the earlier fact
    `Yᵢ ⊆ OUABPQ`: a right-closed set without `B` already lies in `PQ`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Deterministic port-numbering model** on the infinite `Δ`-regular tree. The tree is the Cayley graph
  of CSLib's free Coxeter group `FreeCox Δ`, so its edges come with a proper `Δ`-edge colouring.
  Port numbers equal colours at both endpoints, as in the graph family of Lemmas 12 and 15. The colours
  are known, so arbitrary port numbers would carry no extra information.
* **Input: an edge orientation**, i.e. the paper's edge port numbering `{1, 2}`. Correctness is
  required for every orientation.
* **Algorithms** are functions of the radius-`t` view (`IsLocal`). The view contains the orientation
  of every edge whose two endpoints are within distance `t`. So a 0-round algorithm sees no
  orientation, which is the paper's convention in Lemma 12 ("they do not even see the port numbering
  of the edges").
* **Problems and operators.** Node-edge-checkable problems (`Problem`): node configurations as
  colour-indexed tuples, plus a symmetric edge relation. `R` and `R̄` are defined exactly as in §2.3,
  including maximality and the derived alphabets.
* **0-round reductions** ("`Π'` is solvable in 0 rounds given a solution of `Π`, given the colouring",
  `ZeroRoundReduction`) are maps between colour-indexed configurations.
* **`k`-outdegree dominating set** (`SolvesODS`): each node outputs membership in `S` and one direction
  bit per edge. `S` must be dominating, every edge inside `S` must be claimed by exactly one endpoint,
  and every node of `S` has outdegree `≤ k` inside `S`.
* **Theorem 3, forward direction.** The paper imports Brandt's round elimination theorem ([13],
  Thm 4.3). We only need "`T` rounds for `Π` ⇒ `T−1` rounds for `R̄(R(Π))`", and we prove it in this
  model (`RoundElim.lean`). Being on the full infinite tree with free inputs, the proof needs no
  independence hypothesis. The orientation is used exactly once: both endpoints of an edge must extend
  their label pair to the same maximal edge configuration.
* **Randomized model (Lemma 15).** A randomized 0-round algorithm is one output distribution, sampled
  independently at every node.
* **Strength of the result.** This setting (tree, colouring, orientation) is the strongest one in which
  the paper proves its port-numbering bound. The paper also allows arbitrary port numbers; as argued
  above, this changes nothing.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| §2.3 `R(Π)`, `R̄(Π)` | `Problem.R`, `Problem.Rbar` | `Problem.lean` |
| Observation 4 (labels of `R̄` are right-closed) | `Problem.nodeMax.mem_of_stronger`, `Problem.mem_of_mem_alphRbar`, `Problem.R_nodeStronger` | `Problem.lean` |
| Theorem 3, (1) ⇒ (2) | `Problem.SolvableIn.Rbar_R`, `Problem.SolvableIn.Rbar_R_sub` | `RoundElim.lean` |
| `Π_Δ(a, x)`, `Π⁺_Δ(a, x)`, `k`-ODS | `Pi`, `PiPlus`, `SolvesODS`, `ODSSolvableIn` | `Family.lean` |
| Lemma 5 | `lemma_5` | `Lemmas.lean` |
| Lemma 6 | `alphR_Pi`, `edgeMax_toSet`, `R_Pi_node` | `Lemma6.lean` |
| Lemma 8 (relaxation; `Π_rel` ≅ `Π⁺`) | `lemma_8_relax`, `toRel_edge`, `lemma_8_reduction` | `Lemma8.lean` |
| Lemma 8 (time complexity) | `lemma_8` | `Main.lean` |
| Lemma 9 | `lemma_9` | `Lemma9.lean` |
| Corollary 10 | `corollary_10` | `Main.lean` |
| Lemma 11 | `lemma_11` | `Lemmas.lean` |
| Lemma 12 | `lemma_12` (and `solvableIn_zero_iff`) | `Lemmas.lean`, `Model.lean` |
| Lemma 13 (explicit condition `8^t (k+t+1) ≤ Δ`) | `lemma_13` | `Main.lean` |
| §1.1/§3.5: `Ω(log Δ)` PN lower bound for `k ≤ Δ^ε` | `odsLowerBound`, `odsLowerBound_log` | `Main.lean` |
| Lemma 15 (`Δ ≥ 2`); false for `Δ = 1` | `lemma_15`, `lemma_15_false_delta_one` | `Lemma15.lean` |

`odsLowerBound_log`: for all `Δ` and `k ≤ 2^{⌊log₂Δ/6⌋}`, every algorithm computing a `k`-ODS needs at
least `⌊log₂Δ/6⌋` rounds. `odsLowerBound` is the non-asymptotic form, `t ≤ T` whenever
`8^t (k+t+1) ≤ Δ`.

**Not formalized.** Theorem 1 and Corollary 2 in the LOCAL model, which need the lifting Theorem 14
imported from [4, 5, 15] (IDs, randomization, the `log_Δ n` terms). The converse direction of Theorem 3
is not needed.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `odsSolvable` (`NonVacuity.lean`) shows that in this model an MIS, and hence a
`k`-ODS for every `k`, can be computed in `2^Δ` rounds. It reads the direction bits of the incident
edges as a proper `2^Δ`-colouring and runs greedy MIS. So the lower bound concerns a solvable problem:
`⌊log₂Δ/6⌋ ≤ T ≤ 2^Δ`. The tree, `gen`, `len` and `startsWith` come from CSLib
(`Cslib/Computability/Distributed/ColourSystem/FreeCoxeter.lean`).

CSLib candidates (`-- CSLib candidate`): the round-elimination operators with Observation 4
(`Problem.lean`), the oriented-tree PN model (`Model.lean`) and the forward round-elimination theorem
(`RoundElim.lean`). The last two are a non-bipartite counterpart of `Papers/PODC2020/TightBipartiteMatching/`.
