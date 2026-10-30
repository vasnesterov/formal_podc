# Demand-Aware vs. Demand-Oblivious Throughput — PODC 2026

Matthias Bentert, Chen Avin, Stefan Schmid. *A Separation Between Optimal Demand-Oblivious and
Demand-Aware Network Throughput.* PODC 2026. DOI
[10.1145/3796701.3815941](https://doi.org/10.1145/3796701.3815941). Formalized version: arXiv
2605.04699 v1; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** All the main results hold, and we prove them without
assumptions. This includes the separation theorem (Theorem 5: throughput `5/8 − ε` is achievable for
large `n`), together with the two results from the literature it uses: dependent rounding (Theorem 3)
and the Chernoff bound under negative correlation (Theorem 4). Propositions 1–4, Lemma 1,
Observations 1–4 and Theorem 6 also hold. The statement-level slips are typos with evident intent:
the problem box of Demand-Aware Weak Direct Throughput asks for the *direct* throughput, and
Proposition 3 names the wrong matrix. Several proofs need small repairs.

## Mistakes in the paper

* **Theorem 5's proof feeds a non-integer number of variables into Theorem 4 (proof repair).** For
  each row it applies Theorem 4 "with `t = n + Y_i`" variables: the `n` rounding variables plus
  `Y_i = ∑_j (1 − b'_ij)` constant ones of weight `1`. But `Y_i` is not an integer in general. The
  fix is local: add `n` constant variables of weight `1 − b'_ij ∈ [0, 1]` instead. The mean, `δ` and
  the bound `e^{-2nε²/3}` stay the same. (`line_bad_prob_le`)
* **Theorem 5's proof only checks the conditions on `n_κ` at `n_κ` itself (routine gap).** `n_κ` is
  "the smallest positive integer such that `n_κ ≥ 6/(16ε) + 1` and `e^{-2ε²n_κ/3} < 1/(2n_κ)`", but
  the proof then uses both conditions for every `n ≥ n_κ`. The second condition is not monotone in
  general. It does hold for all `n ≥ n_κ`, because `2n·e^{-cn}` is decreasing beyond its maximum and
  is `> 1` up to it. We take `n_κ` from "eventually" statements instead. (`eventually_large`)
* **Proposition 1's proof has an arithmetic slip and a gap (statement true).** In the displayed
  computation, `5/6 − 5ε/12 − ε²/2` is set equal to `5/6 − 5ε/6 + ε − ε − ε²/2`, which is false. The
  final inequality `< κ(1 − ε)` still holds. Separately, the graphs with `≤ 1` self-loop are
  dismissed with "cannot host `(5/6)M_κ` since `1 − ε > 2/3`", which is not an argument. We replace
  the graph-by-graph reasoning with two cut inequalities that hold for every flow on two nodes:
  `D_ab ≤ A_ab` and `D_ab + D_aa + D_bb ≤ A_ab + A_aa + A_bb`. Proposition 1, Proposition 4 (first
  part) and the `M₂` example follow by arithmetic. (`two_node_bounds_rel`, `proposition_1`)
* **Typos and small slips.**
  - Proof of Theorem 5: "Let `ε = κ − 5/8 > 0`" should be `ε = 5/8 − κ` (since `κ < 5/8`).
    "Hence `b_ij < (2n−1)κ a_ij`" fails when `a_ij = 0` (then they are equal; this is harmless).
    "`b_ij < min(a_ij, d_ij)`" should read `b_ij < d_ij`.
  - The problem box for Demand-Aware Weak Direct Throughput asks whether "the direct throughput
    of `G` … is at least `κ`"; it should say "weak direct throughput" (defined in §1.1). Read
    literally, the problem coincides with Demand-Aware Direct Throughput, and Theorem 6 would then
    contradict Proposition 3 for `n ≥ 2`. The intent is clear from the name, §1.1, Observation 4
    and the proof of Theorem 6. Together with the next item, this is behind the ⚠️ (R3).
  - Proposition 3 constructs `M_κ` but says "`(M, κ)` is a no-instance"; it should be `(M_κ, κ)`.
  - Numerical remark after Theorem 5: by the proof's own two conditions, `κ = 0.6` needs
    `n ≥ 26068`, not 26000. The other three numbers (≈ 700, 2250, ≈ 27 million) check out.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
- A network on `Fin n` is a directed multigraph given by an `ℕ`-adjacency matrix `A`. It is
  `(2n−1)`-regular if all row and column sums are `2n − 1`. Arcs have capacity `1/(2n−1)`;
  equivalently, as in the paper, capacity `1` with demand `(2n−1)·θ·M`.
- A flow is a finite family of non-empty paths (walks with at least one arc, so self-demand uses a
  self-loop or a closed walk) with non-negative amounts. It must serve exactly the demand of every
  ordered pair.
- "Throughput of `G` for `M` is at least `κ`" is rendered as "`G` hosts `θM` for some `θ ≥ κ`". The
  four problems are `DAThroughput`, `DADirectThroughput`, `DAWeakThroughput` and
  `DAWeakDirectThroughput`.
- **Capacity semantics.** The paper charges a path once per multigraph arc it uses.
  - Constructions (yes-instances) use the stricter rule `CanRoute`: a path is charged once per
    traversal of the pair `(u, v)`.
  - No-instances are proved for the weaker rule `CanRouteRel`: a path through `(u, v)` is charged
    once.
  - The paper's semantics lies between the two, so both kinds of results transfer to it. Direct
    routing is the same under all three rules.
- Randomness is used only in proofs. It lives on finite sample spaces: a distribution is a
  non-negative weight function with total `1` (`FinDist`). This is not a distributed-computing
  model: there are no processes, failures or adversaries.

**Main results in Lean.** (namespace `Podc.DemandAwareThroughput`)

| Paper | Lean | File |
|---|---|---|
| Theorem 5 (and Theorem 2): `κ < 5/8` ⇒ yes-instance for all `n ≥ n_κ` | `theorem_5`, `theorem_2` | `Main.lean` |
| Theorem 5 from Theorem 3 as a hypothesis | `theorem_5_of_rounding` | `Separation.lean` |
| Theorem 3 (dependent rounding, Gandhi et al.) | `dependentRounding` | `DependentRounding.lean` |
| Theorem 4 (Chernoff under negative correlation) | `negCorrChernoff` | `Chernoff.lean` |
| Proposition 1 (upper bound `5/6`, `n = 2`) | `proposition_1`, `proposition_1_rel` | `TwoNodes.lean` |
| Proposition 2 (direct throughput `n/(2n−1)` achievable) | `proposition_2` | `Direct.lean` |
| Proposition 3 (direct throughput `> n/(2n−1)` not achievable) | `proposition_3` | `Direct.lean` |
| Observations 1, 2, 3 | `observation_1_direct`, `observation_1_weak`, `observation_2`, `observation_2_direct`, `observation_3` | `Model.lean`, `Direct.lean` |
| Observation 4 | `observation_4` | `Weak.lean` |
| Lemma 1 | `lemma_1` (via `exists_rounding_ge`) | `Lemma1.lean` |
| Theorem 6 (weak direct `(7n−4)/(8n−4)` achievable) | `theorem_6` | `Lemma1.lean` |
| Proposition 4 (weak `8/9` for `n = 2`; weak direct `(7n−4)/(8n−4)` / `(7n−3)/(8n−4)`) | `proposition_4_weak`, `proposition_4_weak_rel`, `proposition_4_direct` | `Weak.lean` |
| §2 examples (Figure 2) | `example_M1_throughput`, `example_M1_not_weakDirect`, `example_M2_weakDirect`, `example_M2_not_throughput` | `Examples.lean` |

Some of our proofs differ from the paper's:
- Proposition 2: we pad `⌈n·M⌉` to a regular matrix (CSLib `Matrix.exists_regular_above`) instead
  of analysing the greedy algorithm.
- Observation 3: we derive it from Proposition 2 instead of the external Theorem 1 (Keslassy et al.).
- Theorem 3 and Lemma 1: we obtain the cycle direction by linear algebra (`exists_cycle_direction`,
  `exists_circulation`) rather than by walking along a cycle.

**Not formalized.**
- Theorem 1 (Keslassy et al.; not needed).
- Propositions 5 and 6 (running times O(n³) and O(n⁴ log n)), and the paper's greedy proof of
  Proposition 2. Randomized tests (n ≤ 4) found the greedy optimal.
- Theorem 7 (NP-hardness).

**Trust.**
- No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- Theorems 3 and 4 are proved, not assumed, so Theorem 5 is unconditional.
- The two-node and §2 examples show that the definitions are not vacuous: there are both
  yes-instances and no-instances.

CSLib candidates (marked `-- CSLib candidate`):
- `FinDist` and its union-bound lemmas;
- `negCorrChernoff`;
- `dependentRounding`;
- `CycleDirection.lean` (`exists_circulation`, `exists_cycle_direction`);
- `exists_rounding_ge` (pipage rounding).

The model uses Mathlib's `doublyStochastic` and CSLib's `Matrix.exists_regular_above`
(`Cslib/Foundations/Combinatorics/Matrix/Birkhoff.lean`).
