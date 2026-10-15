# Differences between the formalization and the paper

Paper: Vaidya, Tseng, Liang, *Iterative Approximate Byzantine Consensus in Arbitrary Directed
Graphs*, PODC 2012 / arXiv:1201.4183v2.

**Verdict:** the characterization (Theorems 1–3) and all of Section 6 hold as stated, under the
paper's standing assumption `n ≥ 2`. One step of the necessity proof is not justified as written (§2
below); it is fixable. The other points are minor slips, imprecisions or generalizations.

## 1. Model and specification (made precise)

* **Algorithm class.** The paper describes "iterative algorithms" informally: `v_i[t] = Z_i(r_i[t],
  v_i[t-1])`, the output is the state, and there is "no sense of time". We formalize this as
  `IterAlg`: one fixed function `Z i : (V → ℝ) → ℝ → ℝ` per node. It sees only the values of
  in-neighbours (other entries are forced to `0`) and its own state. It is time-independent and has
  no other memory.
* **Validity.** The paper starts with "outputs in the convex hull of the fault-free inputs" and then
  says that for its algorithm class this "becomes" (1). Without a sense of time the two are
  equivalent. We define both (`ValidHull`, `ValidStep`) and prove them equivalent for every
  iterative algorithm, quantified over all scenarios (`IterAlg.correct_iff_correctStep`). The main
  characterization holds for either (`exists_correct_iff`, `exists_correctStep_iff`).
* **Convergence.** The paper's "outputs converge to an identical value" is restated as
  `lim (U[t] - μ[t]) = 0`. We use the latter, as an ε-statement (`Converges`). With validity (1) it
  implies a common limit (`ValidStep.exists_tendsto`). Algorithm 1 satisfies both
  (`alg1_run_correct`).
* **Correctness quantifies over every scenario:** every Byzantine set with `|F| ≤ f`, all real
  inputs, and all Byzantine messages (which may differ per receiver and per iteration).
* **Ties broken arbitrarily.** We quantify over all tie-breaks:
  * Theorems 2 and 3 are proved for every run of the step relation `alg1Step`. There the trimming
    may change in every iteration and may be chosen adversarially.
  * Every deterministic rule (`TieBreak`) yields an `IterAlg` whose runs are such runs.
* **Graphs.** The paper uses a simple digraph with no self-loops. We use Mathlib's `Digraph` and
  ignore self-loops in `inNbrs`.
* **Node set.** The paper assumes `n ≥ 2`. `exists_correct_iff` holds for every finite `V`: for
  `n ≤ 1` the condition holds vacuously, and the identity algorithm is correct (`id_correct`).

## 2. Gap in the proof of Theorem 1 (necessity)

The paper argues per node `i ∈ L`, for example: "from i's perspective, it is possible that all the
nodes in `N'(i)` are faulty … the values sent to node `i` by the fault-free nodes are all `m`, and
therefore `v_i[1]` must be set to `m` as per the validity condition (1)".

Validity (1) is a statement about `U[0]` and `μ[0]`, the extremes over **all** fault-free nodes. In
the execution under consideration, the nodes of `(C ∪ R) \ N'(i)` are fault-free and have states up
to `M`. So (1) only gives `v_i[1] ≤ M`, not `v_i[1] ≤ m`. This already fails in the first case
(`F = N'(i) = ∅`): there all received values are `m`, but `U[0] = M` whenever `R ≠ ∅`.

The argument needs a *different* execution: one in which the nodes that `i` cannot hear have their
inputs changed to values in `[m, m]`. Because `Z_i` sees only in-neighbours, this execution is
indistinguishable for `i`. The paper leaves this step implicit.

The same tacit step is used for times `t > 1` ("these conditions are identical to the initial
conditions; by induction"). There it also uses that `Z_i` does not depend on `t`.

**Fix:** `IterAlg.localValid`. If `A` is correct, the received values outside a set `B` of at most
`f` in-neighbours lie in `[lo, hi]`, and the own value lies in `[lo, hi]`, then
`Z i r v ∈ [lo, hi]`. Proof: take validity at `t = 1` in the scenario where `B` is faulty and every
other node starts at its received value, or at `v` if `i` cannot hear it. Because `Z` does not depend
on time, this applies at every iteration.

Also, the auxiliary messages `m⁻ < m` and `M⁺ > M` of the faulty nodes are unnecessary. Our proof
lets `F` send `m` to `L ∪ C` and `M` to `R`, with `m = 0`, `M = 1`, and `C` starting at `0`.

## 3. Minor slips and imprecisions

* **Corollary 2** (`n > 3f`) needs `n ≥ 2`. For `n = 1` the condition holds vacuously. This is the
  paper's standing assumption; our `Condition.three_mul_lt_card` has the hypothesis
  `2 ≤ Fintype.card V`.
* **Corollary 3.** The proof sets `R = V − F − {i}` but does not check `R ≠ ∅`, which Corollary 1
  requires. It follows from Corollary 2: `|R| ≥ 3f + 1 − f − 1 = 2f ≥ 1`. We use exactly this.
* **Theorem 2** uses Corollary 3 (`|N_i⁻| ≥ 2f + 1`). Validity needs only that trimming is possible
  (`|N_i⁻| ≥ 2f`). `alg1_validStep` has no graph hypothesis at all. The case `≥ 2f + 1` is needed
  only in Claim 1, second sub-case, where a value that is *not* eliminated is required.
* **Lemma 1 / Lemma 2.** In Lemma 2 the hypotheses "`A`, `B` non-empty" (and disjointness) are not
  needed (`Condition.propagates_or`). Appendix B's monotonicity argument is replaced by a shorter
  closure argument; see README "Proof notes".
* **Definition 3.** The paper's propagating sequences require `A_τ ⇒ B_τ` at every step before
  `B_l = ∅`. We define propagation as "the iteration `S ↦ S ∪ in(S ⇒ X \ S)` from `A` reaches
  `A ∪ B`" (`Propagates`). For the first such `l` the paper's extra condition holds automatically,
  because otherwise the iteration is stuck at a fixpoint. This equivalence is stated in a docstring,
  not proved, because only our form is used.
* **Lemma 5 / Claims 1–4** are proved with arbitrary bounds `lo ≤ x s j ≤ hi` (and `[m, M]` for
  `R`) instead of the exact `μ[s]`, `U[s]`, `min_R`, `max_R`. The paper's statements are the special
  case. Lemma 5 is stated as "there are bounds `lo' ≤ hi'` at time `s + l` with
  `hi' - lo' ≤ (1 - α^l/2)(hi - lo)`", which implies the paper's inequality (7). Claim 1 holds for
  every `τ`, not only `τ ≤ l`.
* **Typo**, end of the proof of Claim 4 (Appendix A): `U[s] − v_i[s + τ] ≥ α^{τ+1}…` should read
  `v_i[s + τ + 1]`.
* **Theorem 3.** The paper iterates Lemma 5 with the variable lengths `l(s) ≤ n − f − 1` and leaves
  "choose `i` large enough" implicit; this needs the uniform bound on `l(s)`. We use the uniform
  length `n = |V|` in every phase (`contraction`). This gives the explicit rate
  `|x t i − x t j| ≤ (1 − αⁿ/2)^⌊t/n⌋ (hi − lo)` (`alg1_spread_le`), slightly weaker than with
  `n − f − 1` but with the same qualitative conclusion. `α` may be any value in `(0, 1]` below all
  weights `aᵢ`; `alpha G f = min aᵢ` is the paper's choice.
* **`α ≤ 1` and `0 < α`** are used implicitly by the paper (stated as `0 < aᵢ ≤ 1`). We prove them
  (`alpha_pos`, `alpha_le_one`).

## 4. Section 6

* **Complete graph.** We prove `Condition ⊤ f ↔ n > 3f` for `n ≥ 2` (`condition_complete_iff`).
  The paper only cites [5, 12] for sufficiency.
* **Core network (Def. 4).** The claim "it is easy to show" is proved
  (`IsCoreNetwork.condition`). Only the edges from `K` to all nodes are used. The conjecture about
  minimal edge count is not formalized.
* **Hypercube.** Proved for every `d ≥ 1`, `f ≥ 1` (`not_condition_hypercube`).
* **Chord networks.** `n = 7, f = 2` fails, with the paper's witness (`not_condition_chord_7_2`).
  `n = 5, f = 1` satisfies the condition (`condition_chord_5_1`; the paper gives no proof). Checked by
  kernel computation. Definition 5's side condition `n > 3f` is not part of the `chord` graph; it
  holds in both instances.
* Section 7 (asynchronous and partially asynchronous generalizations) announces results without
  proofs and is not formalized.
