# Iterative Approximate Byzantine Consensus in Directed Graphs — PODC 2012

Nitin H. Vaidya, Lewis Tseng, Guanfeng Liang. *Iterative Approximate Byzantine Consensus in Arbitrary
Directed Graphs.* PODC 2012. DOI [10.1145/2332432.2332505](https://doi.org/10.1145/2332432.2332505).
Formalized version: arXiv [1201.4183](https://arxiv.org/abs/1201.4183) v2 (technical report with all appendices).

**Verdict: ✅ Correct.** The tight characterization (Theorems 1–3: an iterative algorithm exists iff the
graph satisfies the partition condition, and Algorithm 1 then works) and all of Section 6 hold as stated,
under the paper's standing assumption `n ≥ 2`. The necessity proof has one unjustified step, which we
repair; the rest are minor slips.

## Mistakes in the paper

* **Gap in the necessity proof (Theorem 1); statement true.** For a node `i ∈ L`, the paper argues that
  if all values `i` receives from fault-free nodes equal `m`, then validity (1) forces `v_i[1] = m`. But
  (1) bounds `v_i[1]` by `μ[0]` and `U[0]`, the extremes over *all* fault-free nodes, including nodes
  of `C ∪ R` that `i` cannot hear and that start at `M`. So (1) gives only `v_i[1] ≤ M`. This
  already fails in the simplest case `F = N'(i) = ∅` with `R ≠ ∅`. The argument needs a *different*
  execution in which the nodes outside `i`'s in-neighbourhood start in `[m, m]`; since `Z_i` sees only
  in-neighbours, `i` cannot tell the two apart. The induction to `t > 1` uses the same step, plus the
  fact that `Z_i` does not depend on `t`. We prove this "local validity" property separately
  (`IterAlg.localValid`) and derive Theorem 1 from it. The paper's auxiliary values `m⁻ < m`,
  `M⁺ > M` turn out to be unnecessary. (`condition_of_correct`)
* **Minor slips and remarks.**
  * Corollary 2 (`n > 3f`) needs `n ≥ 2`: for `n = 1` the condition holds vacuously. This is not a
    slip: the paper assumes `n ≥ 2` in §2.1 and its proof starts from `2 ≤ n ≤ 3f`
    (`Condition.three_mul_lt_card`).
  * Corollary 3: the proof takes `R = V − F − {i}` without checking `R ≠ ∅`, which Corollary 1
    requires. It follows from Corollary 2 (`|R| ≥ 2f ≥ 1`).
  * Theorem 2 (validity) does not need Corollary 3; trimming being possible suffices. Lemma 2 does
    not need `A`, `B` non-empty.
  * Theorem 3 iterates Lemma 5 with phase lengths `l(s) ≤ n − f − 1` and leaves the uniform bound
    implicit; we use phase length `n` throughout.
  * Typo at the end of the proof of Claim 4 (Appendix A): `v_i[s + τ]` should be `v_i[s + τ + 1]`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finite node set `V` with a directed graph (Mathlib `Digraph`, self-loops ignored); synchronous
  lock-step iterations; every node sends its state on all outgoing links.
* Static Byzantine set `F`, `|F| ≤ f`; faulty nodes may send arbitrary, different reals to different
  out-neighbours in every iteration. Authenticated links. Correctness quantifies over every `F`, all
  real inputs and all Byzantine messages.
* *Iterative algorithms* (`IterAlg`): one fixed function `Z i (received vector) (own state)` per node,
  seeing only in-neighbours, with no clock and no other memory; the state is the output. This is the
  paper's `Z_i(r_i[t], v_i[t−1])`, and the impossibility depends on exactly this restriction.
* Validity both as "outputs in the hull of fault-free inputs" and as the per-iteration form (1); we
  prove them equivalent for iterative algorithms (`IterAlg.correct_iff_correctStep`). Convergence is
  `U[t] − μ[t] → 0`.
* Algorithm 1's "ties broken arbitrarily" is quantified universally: Theorems 2–3 hold for every run of
  the step relation `alg1Step`, where the trimming may be chosen anew (even adversarially) each
  iteration; every deterministic tie-breaking rule gives an `IterAlg` (`TieBreak.alg`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorems 1–3 combined | `exists_correct_iff` (and `exists_correctStep_iff` for validity (1)) | `Main.lean` |
| Theorem 1 (necessity) | `condition_of_correct` | `Necessity.lean` |
| Corollaries 2, 3 | `Condition.three_mul_lt_card`, `Condition.inDegree` | `Condition.lean` |
| Lemma 2 | `Condition.propagates_or` | `Condition.lean` |
| Theorem 2 (validity) | `alg1_validStep` | `Algorithm.lean` |
| Lemma 5, Theorem 3 (convergence) | `lemma5`, `alg1_converges`; explicit rate `alg1_spread_le` | `Convergence.lean` |
| Algorithm 1 correct (all tie-breaks) | `alg1_run_correct` | `Main.lean` |
| §6: complete graph, core network, hypercube, chord | `condition_complete_iff`, `IsCoreNetwork.condition`, `not_condition_hypercube`, `not_condition_chord_7_2`, `condition_chord_5_1` | `Applications.lean` |

The explicit rate is `(1 − αⁿ/2)^⌊t/n⌋ (hi − lo)`. The chord case `n = 5, f = 1`, which the paper
states without proof, is checked by kernel computation.

**Not formalized.** Section 7 (asynchronous variants: announced without proofs) and the conjecture on
the minimal edge count of core networks.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `alg1_complete` (on the complete graph with `n > 3f`, tie-breaking rules
exist and Algorithm 1 is correct), plus concrete examples on `Fin 4` / `Fin 3` with `f = 1`. The
model (`IterAlg`, validity notions, trimming `IsTrim`) lives in CSLib
`Cslib/Computability/Distributed/ApproxConsensus/{Iterative,Trim}.lean`.
