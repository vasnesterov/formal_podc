# Tight Bounds for Asymptotic and Approximate Consensus

Matthias Függer, Thomas Nowak, Manfred Schwarz. *Tight Bounds for Asymptotic and Approximate
Consensus.* PODC 2018, pp. 325–334. DOI
[10.1145/3212734.3212762](https://doi.org/10.1145/3212734.3212762); arXiv
[1705.02898](https://arxiv.org/abs/1705.02898) (v2, used here; journal version JACM 2021 not consulted).

## Status

**Done. No `sorry` or `axiom`.** `#print axioms` on all main theorems listed below shows only
`propext`, `Classical.choice` and `Quot.sound`. The modules build with
`lake build Papers.PODC2018.AsymptoticConsensus.Counterexamples Papers.PODC2018.AsymptoticConsensus.Approximate`.

**Main findings.**
* The contraction-rate lower bounds are **correct**: Theorems 1, 2, 3, 5, 6 and the
  approximate-consensus bounds 8–11 are proved, for values in any nontrivial real normed space
  (`ℝ^d`). Theorems 1 and 2 are proved tight via Algorithm 1 and the midpoint algorithm.
* **Theorem 4 (⇐) is false** (`theorem4_false`). The algorithm `fd` ("first deviation parity", two
  agents, model `{H₀,H₁,H₂}`) solves asymptotic consensus, and all its limits are initial values.
  So all its valencies are finite, hence singletons or disconnected. Yet exact consensus is not
  solvable there. The proof breaks at the claim "`δ_N(C_t) → 0` in any execution by Convergence
  and Agreement". That claim holds only for continuous consensus functions, and it fails for `fd`
  (`fd_not_vanishing`). With continuity added (`VanishingValency`), Theorem 4 holds
  (`theorem4_mpr_repaired`, `theorem4_repaired`). The repaired equivalence is conditional on the
  cited characterization of Coulouma et al. [12].
* **Definition 15 is stated imprecisely (typo-level).** It loosely restates [12, Def. 4.7]. The
  intended per-agent reading (`AlphaRel`) is confirmed by the paper's remark `D = 2` and by the
  proofs of Lemmas 20 and 24, and under it Lemma 20 and Theorem 5 hold. Lean counterexamples for the
  literal node-union reading are recorded in `lemma20_literal_false` and `theorem5_literal_false`.
* The proof of Theorem 11 is broken, but the statement holds and we prove it differently: restarting
  `A` with a fixed `ε` need not converge, and there are `log₃`/`Δ/n` typos. There are also minor
  slips: claim (8) of Theorem 3 and swapped endpoints in Lemma 24. Lemma 20 relies on the cited [8]
  for `R(K) ≠ ∅`. Theorem 4 is read with `N'` nonempty, and its refutation also covers binary
  consensus. Details are in `differencies.md`.

Rough token spend: about 1.2M tokens (paper agent and three subagents: upper-bound algorithms,
the `fd` algorithm, approximate consensus).

## Model (explicit choices)

* **Agents and graphs.** Agents are a finite type (`Fin n` for the paper's `[n]`, shifted to
  `0, …, n-1`). A communication graph is `G : α → α → Prop`, where `G j i` means that `i` receives
  `j`'s message. Self-loops are implicit (`Hears G i j := j = i ∨ G j i`). See
  `Cslib/Computability/Distributed/DynamicNetworks/HeardOf.lean`.
* **Synchrony and adversary.** The model is synchronous and communication-closed (Heard-Of style).
  The adversary is oblivious: a pattern is any sequence `p : ℕ → Graph α` with every `p t ∈ N`
  (`Pat N`). Theorem 3 uses block patterns `BlockPat`, the concatenations of the sequences `σ_u`,
  in place of the paper's "properties" and snapshots.
* **Algorithms.** `Alg α σ V` is deterministic and full-information:
  `init : α → V → σ` (the state may depend on the agent's identity and its initial value),
  `step : α → (α → Option σ) → σ` (the received states, `none` if not heard; the agent always
  receives its own state), and `out : σ → V` (the variable `y`). Agents may have arbitrary memory
  and may output values outside the hull of received values. There is no failure model;
  "failures" are encoded in the graphs.
* **Asymptotic consensus.** `Alg.Solves A N`: in every execution with pattern in `N`, all outputs
  converge to a common limit in the convex hull of the initial values. Values lie in a real normed
  space `V`; the midpoint algorithm uses `V = ℝ`.
* **Valency and rate.** `Alg.val A Q C` is the set of limits reachable from `C` with patterns in
  `Q`. It agrees with the paper's valency `Y*_N(C)` on reachable configurations
  (`val_eq_paperVal`). `δ_N(C)` is its diameter (`Metric.ediam`, in `ℝ≥0∞`). The contraction rate
  `Alg.rate A N = sup_E limsup_t δ_N(C_t)^{1/t}` also lives in `ℝ≥0∞`.
* **Exact consensus.** `EAlg` has a decision variable `dec : σ → Option V`. `EAlg.Solves`
  requires termination, irrevocability, agreement, and validity (decision ∈ initial values).
  `ExactSolvable α V N` quantifies over state types in `Type`.
* **Approximate consensus.** `DAlg` has fixed `ε, Δ` built into the algorithm.
  `DecidesBy N Δ ε T` requires that, for initial values within `Δ`, at time `T` every agent has
  decided, the decisions are within `ε` of each other, and they are valid. This is weaker than the
  paper's specification, so the lower bounds are stronger.
* **Asynchronous crashes (Section 8).** Only the network-model form is formalized: the model
  `N_A` of round-based algorithms waiting for `n − f` messages. The reduction from asynchronous
  executions, and the time-versus-rounds remark, are not formalized.

## Theorems ↔ Lean

| Paper | Lean (namespace `AsymptoticConsensus`) | File |
|---|---|---|
| Lemma 3 (i)–(iv) | `Alg.Solves.mono`, `Alg.paperVal_mono`, `Alg.δ_mono`, `Alg.rate_mono` | Valency |
| Lemma 4 | `Alg.val_eq_iUnion` | Valency |
| Lemma 5 | `Alg.exists_δ_eq_union` (abstract: `Cslib.HeardOf.Chain.exists_ediam_eq_union`) | Valency |
| Lemma 6 | `Cslib.HeardOf.next_eq_of_agree` (+ run version `conf_agree`) | Cslib/Computability/Distributed/DynamicNetworks/HeardOf.lean |
| Lemma 7 | `Alg.val_inter_nonempty_lemma7` (general: `val_inter_nonempty_of_deaf`, `_of_closed`) | Valency |
| Lemma 8 | `Alg.δ_initC`, `Alg.exists_δ_initC_pos` | Valency |
| [8] necessity of rootedness | `Alg.Solves.exists_root` | Valency |
| proof scheme of Thms 1–3, 5 | `Alg.exists_block_run`, `Alg.le_rate_of_blocks`, `Alg.le_rate_of_chains` | Engine |
| **Theorem 1** (`n = 2`, `≥ 1/3`) | `theorem1` | LowerBounds |
| **Theorem 2** (`deaf(G)`, `≥ 1/2`) | `theorem2` (three deaf graphs suffice), `theorem2_deaf`, `theorem2_nonsplit` | LowerBounds |
| Lemma 14 | `psi_agree` (strong form `psi_agree_aux`) | Psi |
| **Theorem 3** (`Ψ`, `≥ (1/2)^{1/(n-2)}`) | `theorem3`, `theorem3_rooted` | Psi |
| Algorithm 1 tight (`= 1/3`) | `alg1_solves`, `alg1_rate_eq`, `alg1_rate_eq_N3` | Algorithms |
| Midpoint tight (`= 1/2`) | `midpoint_solves`, `midpoint_rate_eq` | Algorithms |
| Thm 2 of §2.2 (continuity, convex combination algorithms) | `Averaging.vanishing` (averaging algorithms) | Counterexamples |
| Def. 15, 18, 22 | `AlphaRel` (per-agent), `AlphaRelLit` (literal), `SourceIncompatible`, `AlphaDiamLE` | Alpha |
| Lemma 20 | `Alg.val_inter_nonempty_alpha` | Alpha |
| Lemma 21 | `Alg.lemma21` (constant `1/(n-1)`), `lemma21_paper` | Alpha, Exact |
| **Theorem 4 (⇒)** | `theorem4_mp` | Exact |
| **Theorem 4 (⇐)**: false | `theorem4_false`, `theorem4_mpr_counterexample`, `fd_solves`, `fd_limit` | Theorem4, FirstDeviation |
| Theorem 4 repaired | `theorem4_mpr_repaired`, `theorem4_repaired` (hypothesis `CouloumaHyp`) | Theorem4 |
| "rate 0 if exact consensus solvable" | `rate_toAsym`, `exists_rate_zero_of_exactSolvable` | Exact |
| [12] easy direction (common root ⇒ solvable) | `exactSolvable_of_common_root`, `sourceIncompatible_of_not_exactSolvable` | Exact |
| **Theorem 5** | `Alg.theorem5` (source-incompatible), `theorem5_paper` (¬ exact) | Alpha, Exact |
| Corollary 23 | `Alg.corollary23` | Alpha |
| Lemma 24 | `alphaDiam_NA` | Alpha |
| **Theorem 6** (`≥ 1/(⌈n/f⌉+1)`) | `theorem6` (network-model form) | Alpha |
| Theorem 7 (MinRelay) | not formalized (asynchronous model) | — |
| **Theorem 8** | `theorem8`, `theorem8_logb` | Approximate |
| **Theorem 9** | `theorem9`, `theorem9_deaf`, `theorem9_logb`, `theorem9_nonsplit` | Approximate |
| **Theorem 10** | `theorem10` (`Δ ≤ 2^{⌊T/(n-2)⌋} ε`), `theorem10_logb`, `theorem10_rooted` | Approximate |
| **Theorem 11** | `theorem11` (`Δ ≤ (n-1)(D+1)^T ε`), `theorem11_logb` | Approximate |
| Error found / literal-reading checks | `theorem4_false`, `fd_not_vanishing`; literal Def. 15: `lemma20_literal_false`, `theorem5_literal_false`, `alphaDiamLit_N3` | Theorem4, Counterexamples |
| Consequences for exact consensus | `not_exactSolvable_N3`, `not_exactSolvable_deaf`, `not_exactSolvable_of_sourceIncompatible` | Exact |

## Infrastructure and CSLib candidates

* `Cslib/Computability/Distributed/DynamicNetworks/HeardOf.lean` (now in CSLib). A round-based full-information dynamic-network
  model: `Graph`, `Hears`, `Deaf`, `SameIn`, `StepFn`, `next`, `conf`, `Pat`, and the pattern
  operations `pcons`, `shift`, `splice`. It also has the indistinguishability lemmas
  `next_eq_of_agree`, `conf_agree` and `conf_agree_deaf`. It complements `Cslib.DynNet`, whose
  `IsRoot` and `exists_edge_cross` are reused.
* `Cslib/Computability/Distributed/DynamicNetworks/Chain.lean` (now in CSLib). Chains of intersecting sets and diameters:
  `edist_le_sum_chain`, `exists_ediam_le_mul`, `exists_ediam_eq_union`. It also has greedy
  sequences (`exists_seq_of_step`) and `t`-th root growth rates in `ℝ≥0∞` (`le_limsup_rpow_inv`,
  `limsup_rpow_inv_le`).
* In the paper folder, possibly generalizable:
  * the valency engine for block patterns (`Engine.lean`);
  * `Averaging` (memoryless convex-combination algorithms: solvability and rate bound);
  * the finite-horizon decision-set engine in `Approximate.lean` (`ediam_le_pow_mul_of_chains`,
    marked CSLib candidate).
