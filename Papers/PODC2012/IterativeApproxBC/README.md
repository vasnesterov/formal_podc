# Iterative Approximate Byzantine Consensus in Arbitrary Directed Graphs

Nitin H. Vaidya, Lewis Tseng, Guanfeng Liang. *Iterative Approximate Byzantine Consensus in
Arbitrary Directed Graphs.* PODC 2012, pp. 365–374. DOI
[10.1145/2332432.2332505](https://doi.org/10.1145/2332432.2332505), arXiv
[1201.4183](https://arxiv.org/abs/1201.4183) (v2, the technical report with all appendices; used here).

## Status

**Done. No `sorry` or `axiom`.** `lean_verify` on the main theorems (`exists_correct_iff`,
`alg1_run_correct`, `alg1_spread_le`, `alg1_complete`, `condition_chord_5_1`) shows only
`propext`, `Classical.choice` and `Quot.sound`. The modules build with
`lake build Papers.PODC2012.IterativeApproxBC.Main`.

All results of Sections 3–6 are formalized: the tight characterization (Theorems 1–3), Corollaries
1–3, Lemmas 1–5, Claims 1–4, and the applications of Section 6. Section 7 (asynchronous networks)
only announces results and is not formalized.

**The main result is correct.** No claim of the paper is false. There is one real gap in the
necessity proof. In the case "both `F` and `N'(i)` non-empty", validity (1) is applied with the global
`U[0]`, which also contains states of nodes that `i` cannot hear. We close it by a local-validity
lemma (`IterAlg.localValid`) that changes the inputs of those nodes. There are also minor slips:
Corollary 3 does not check that `R ≠ ∅`, Corollary 2 needs `n ≥ 2`, and a few hypotheses are
unnecessary. Details are in `differencies.md`.

Rough token spend: about 0.4M tokens (paper agent and one subagent for Section 6).

## Model (explicit choices)

* **Network.** A finite node type `V` (`n = |V|`) with a Mathlib `Digraph V`. The in-neighbours are
  `inNbrs G i = {j | G.Adj j i, j ≠ i}`. Self-loops are ignored, and every node always uses its own
  state.
* **Synchrony.** Lock-step iterations. In iteration `t+1` every node sends its state on all outgoing
  links. Fault-free nodes then update.
* **Faults.** A static Byzantine set `F` with `|F| ≤ f`. Faulty nodes may send arbitrary and
  *different* reals to different out-neighbours in every iteration (`Scenario.adv t j i`). The
  adversary's data is a function fixed in advance. For deterministic algorithms this is the same as
  an adaptive, omniscient adversary. For nondeterministic runs the theorems quantify over all pairs
  (adversary, run), which also covers adaptivity. Links are authenticated: `i` knows the sender of
  each value.
* **Algorithm class ("iterative algorithms").** `IterAlg V` is a transition function
  `Z i r v` that maps the received vector and the own state to the new state. The state is the output.
  There is no round counter and no other memory ("output constraint", "no sense of time"). `Z i` sees
  only in-neighbours, because `r j = 0` is enforced for `j ∉ N_i⁻`. `Z i` may depend on the topology.
  The paper's `Z_i(r_i[t], v_i[t-1])` is exactly this.
* **Specification.** All definitions are in `Cslib/Computability/Distributed/ApproxConsensus/Iterative.lean`.
  * Validity in the paper's primary form (`ValidHull`): fault-free outputs stay in the convex hull of
    the fault-free inputs.
  * Validity in the per-iteration form (1) (`ValidStep`): `μ[t-1] ≤ v_i[t] ≤ U[t-1]`.
  * Convergence (`Converges`): `U[t] - μ[t] → 0`, written as an ε-statement.
  * `IterAlg.Correct G f A` asks for validity and convergence in **every** scenario with `|F| ≤ f`.
    `CorrectStep` is the same with (1). The two are equivalent for iterative algorithms
    (`IterAlg.correct_iff_correctStep`), which formalizes the paper's remark that, without a sense of
    time, validity becomes (1).
  * Common limit: validity (1) and convergence give a common limit of all fault-free states
    (`ValidStep.exists_tendsto`). The algorithm satisfies this too.
* **Algorithm 1, "ties broken arbitrarily".** `IsTrim N f r Low Mid High` (in
  `Cslib/Computability/Distributed/ApproxConsensus/Trim.lean`) says that `Low` and `High` are `f`-subsets of `N`, that
  `Mid = N \ (Low ∪ High)`, and that `r(Low) ≤ r(Mid) ≤ r(High)`. This holds iff the triple comes
  from some sorting of `N` by `r`. Tie-breaking is quantified in two ways:
  1. `alg1Step G f` is a *step relation*. Any trimming may be chosen, anew in every iteration, even
     adversarially. Theorems 2–3 are proved for **all runs** of it (`alg1_run_correct`).
  2. `TieBreak G f` is any deterministic rule. `TieBreak.alg` is the iterative algorithm `Z_i` of
     the paper, and its runs are runs of `alg1Step` (`TieBreak.isRun`). Rules exist when every
     in-degree is at least `2f` (`TieBreak.nonempty`, using `IsTrim.exists`).
* `Scenario` / `run` are a new small model in `Cslib/Computability/Distributed/ApproxConsensus/`, not CSLib's `LockStep`. See
  "Infrastructure" for why.

## Theorem ↔ Lean map

Files: `Condition.lean`, `Necessity.lean`, `Algorithm.lean`, `Convergence.lean`,
`Applications.lean`, `Main.lean`. Infrastructure: `Cslib/Computability/Distributed/ApproxConsensus/{Iterative,Trim}.lean`.
Namespace `IterativeApproxBC`; infrastructure in `ApproxConsensus`.

| Paper | Lean |
|---|---|
| Model §2.3, Zᵢ | `Cslib.ApproxConsensus.IterAlg`, `IterAlg.run`, `Scenario`, `recv`, `IsRun` |
| Validity / convergence, (1) | `ValidHull`, `ValidStep`, `Converges`, `IterAlg.Correct`, `IterAlg.CorrectStep`, `IterAlg.correct_iff_correctStep` |
| "no sense of time" | `IterAlg.run_add` |
| Algorithm 1 | `alg1Step` (any tie-breaks), `TieBreak`, `TieBreak.alg`, `IsTrim`, `tmean`, `weight` (= `aᵢ`), `alpha` (= `α`, eq. (3)) |
| Definition 1 (`A ⇒ B`) | `Arrow G f A B` |
| **Theorem 1** (necessity) | `condition_of_correct` (statement of the condition: `Condition G f`) |
| Corollary 1 | `Condition.corollary1` |
| Corollary 2 (`n > 3f`) | `Condition.three_mul_lt_card` (needs `n ≥ 2`) |
| Corollary 3 (in-degree `≥ 2f+1`) | `Condition.inDegree`; also `Condition.two_mul_le_inDegree` |
| Definition 2 (`in(A ⇒ B)`) | `inArrow` |
| Definition 3 (propagation) | `propStep`, `Propagates`, `propagates_iff_iter_card` |
| Lemma 1 | `Condition.propagates_of_not_arrow` |
| Lemma 2 (+ Appendix B) | `Condition.propagates_or` (simpler closure proof) |
| **Theorem 2** (validity) | `alg1_validStep` |
| Lemma 3 / Lemma 4 (+ App. C) | `alg1_lower_step` / `alg1_upper_step` (core: `tmean_sub_ge`, `sub_tmean_ge`, `IsTrim.exists_correct_le`, `IsTrim.exists_le_mid`, …) |
| Claim 1 / Claim 3 (= Claim 4, App. A) | `claim1` / `claim3` (Claim 2 is `claim1` at `τ = l`) |
| Lemma 5 | `lemma5` |
| **Theorem 3** (convergence) | `alg1_converges`; one phase: `contraction`; explicit rate: `alg1_spread_le` (`≤ (1 - αⁿ/2)^⌊t/n⌋ (hi - lo)`) |
| Theorems 1–3 together | **`exists_correct_iff`**: `(∃ A : IterAlg V, A.Correct G f) ↔ Condition G f` (any `n`); `exists_correctStep_iff`; `alg1_run_correct`, `alg1_correct` |
| §6, complete graph / Cor. 2 converse | `condition_complete`, `condition_complete_iff` |
| §6.1 core network (Def. 4) | `IsCoreNetwork`, `IsCoreNetwork.condition`, `isCoreNetwork_example` |
| §6.2 hypercube | `hypercube`, `not_condition_hypercube` (`d ≥ 1`, `f ≥ 1`) |
| §6.3 chord network (Def. 5) | `chord`, `not_condition_chord_7_2`, `condition_chord_5_1` (`decide +kernel` over `4⁵` labelings via `condition_of_labelings`) |
| non-vacuity | `alg1_complete`: on the complete graph with `n > 3f`, tie-breaking rules exist and Algorithm 1 is correct. Concrete `example`s: `Fin 4`, `f = 1` (correct) and `Fin 3`, `f = 1` (no iterative algorithm). |

## Proof notes

* **Necessity.** First, `IterAlg.localValid`: if `A` is correct and all received values outside a set
  of `≤ f` in-neighbours, together with the own value, lie in `[lo, hi]`, then `Z i r v ∈ [lo, hi]`.
  This follows from validity at `t = 1` in a scenario in which the suspected nodes are faulty and all
  other nodes start inside `[lo, hi]`. The invariant "`L ≡ 0`, `R ≡ 1`, `C ⊆ [0,1]`" then follows
  by induction.
* **Lemmas 1–2.** These use the closure `cl(S) = propStep^[|X|] S`. It is a fixpoint
  (`propStep_iter_card_fix`), so `cl(S) ⇏ X \ cl(S)`. Lemma 2: if `cl(A) ≠ X`, then
  `R := X \ cl(A) ⊆ B`. If moreover `cl(R) ≠ X`, the partition `L = X \ cl(R)`, `R`,
  `C = cl(R) ∩ cl(A)` violates the condition. Hence `cl(B) ⊇ cl(R) = X`.
* **Convergence.** Everything is phrased with arbitrary bounds `lo ≤ x s j ≤ hi` instead of
  `μ[s]`, `U[s]`. The contraction step uses the split at `(lo+hi)/2` and Lemma 2 (`contraction`).
  Iterating it gives the explicit rate.

## Infrastructure

New `Podc/ApproxConsensus/`, since migrated to CSLib `Cslib/Computability/Distributed/ApproxConsensus/`:

* `Iterative.lean` contains the model of iterative (memoryless) Byzantine approximate consensus on
  digraphs, the validity and convergence notions and their equivalences, `run_add`, `localValid` and
  `ValidStep.exists_tendsto`.
* `Trim.lean` contains `IsTrim` (trimming with arbitrary tie-breaks), its existence, the
  fault-bounding lemmas, and the trimmed mean `tmean` with its inequalities. It is reusable for all
  MSR / W-MSR-type algorithms, for example LeBlanc et al. (r-robustness) and Tseng–Vaidya follow-ups.

**Why not CSLib's `LockStep`.** `LockStep` protocols run on a `SimpleGraph` (undirected), have
history-based state (the full history *is* the state), `Option`-valued messages and one-shot
decisions. This paper needs four things it does not offer:

1. directed graphs;
2. a *memoryless* class of algorithms, where the state is a real number and the output, with no
   history and no clock. The impossibility proof depends on this restriction.
3. real-valued outputs in every round, with convergence in the limit;
4. nondeterministic steps, for arbitrary tie-breaking.

Encoding the class into `LockStep` would mean restricting history-based protocols to functions of
the last state, which costs more than the small dedicated model.

`Iterative.lean` and `Trim.lean` have been migrated to CSLib
(`Cslib/Computability/Distributed/ApproxConsensus/`, namespace `Cslib.ApproxConsensus`). **Remaining CSLib candidates:**
the generic parts of `Condition.lean`: `propStep` closure lemmas `propStep_iter_card_fix` and
`propStep_iter_stable`, which give monotone-iteration stabilization on finsets.
