# Tight Bounds for Asymptotic and Approximate Consensus — PODC 2018

Matthias Függer, Thomas Nowak, Manfred Schwarz. *Tight Bounds for Asymptotic and Approximate
Consensus.* PODC 2018. DOI [10.1145/3212734.3212762](https://doi.org/10.1145/3212734.3212762).
Formalized version: arXiv [1705.02898](https://arxiv.org/abs/1705.02898) v2 (the JACM 2021 version was
not consulted).

**Verdict: ❌ False claim.** The contraction-rate lower bounds (Theorems 1, 2, 3, 5, 6) and the
approximate-consensus bounds (Theorems 8–11) are correct. Theorems 1 and 2 are tight (Algorithm 1 and the
midpoint algorithm). **Theorem 4 (⇐) is false**: "valencies singleton or disconnected ⇒ exact consensus
solvable" fails for two agents in `{H₀, H₁, H₂}`. It becomes true once the asymptotic algorithm is
required to have a continuous consensus function.

## Mistakes in the paper

* **Theorem 4 (⇐) is false.** Two agents, model `N = {H₀, H₁, H₂}`: `H₀` lets both hear each other,
  and in `H₁`/`H₂` one of them is deaf. Consider the "first deviation" algorithm. Before any non-`H₀`
  round the output is `x₀`. At the first non-`H₀` round `t`, the deaf agent decides its own value if
  `t` is odd and the other's value if `t` is even. The other agent copies that decision, or applies
  the same parity rule if it is itself deaf in round `t+1`. This solves asymptotic consensus, and
  every limit is an initial value, so every valency `Y*_{N'}(C)` is finite: a singleton or
  disconnected. Yet exact consensus is unsolvable in `N`: by Theorem 1 an exact algorithm would have
  contraction rate 0. The proof fails at "`δ_{N'}(C_t) → 0` in any execution, by Convergence and
  Agreement". That holds only if the consensus function (pattern ↦ limit) is continuous, and the
  paper itself notes in §2.1 that it need not be. Here, along the all-`H₀` execution, both `x₀` and
  `x₁` stay reachable forever. The refutation also covers binary inputs. Adding continuity (valency
  diameters vanish along every execution of every submodel) makes (⇐) true. The full equivalence
  then follows, conditional on the cited characterization of Coulouma et al. [12]. (⇒) holds as
  stated. (`theorem4_false`, `fd_not_vanishing`; repaired: `theorem4_mpr_repaired`,
  `theorem4_repaired`)
* **Definition 15 (α-relation) is stated imprecisely; typo-level.** It writes `In_S(G)` as a union of
  node sets, whereas [12, Def. 4.7] and every later use (the remark `D = 2` for `{H₀,H₁,H₂}`, Lemmas
  20 and 24) need the per-agent version `In_i(G) = In_i(H)` for all `i ∈ R(K)`. Under the literal
  reading the α-diameter of `{H₀,H₁,H₂}` would be 1. Lemma 20 would fail for Algorithm 1 from
  `(0, 1)`, since the valencies after `H₁` and `H₂` lie in `[0, 1/3]` and `[2/3, 1]`. Theorem 5 would
  claim rate `≥ 1/2` for Algorithm 1, whose rate is `1/3`. Under the intended reading both hold
  (`lemma20_literal_false`, `theorem5_literal_false`).
* **Proof of Theorem 11 is broken; statement true.** It builds `Ã` by restarting `A` with the
  decision values, but with a fixed `ε` this need not converge, so `Ã` is not an asymptotic
  consensus algorithm. It also writes `log₃` for `log_{D+1}` and `δ_N(C₀) ≤ Δ/n` for `≥ Δ/n`. We
  prove Theorems 8–11 directly on finite-horizon decision sets (`theorem11`).
* **Minor gaps and slips.**
  * Theorem 3, claim (8), asserts the bound "for every initial snapshot"; Lemma 13 gives only one,
    which suffices.
  * Lemma 20 needs `R(K) ≠ ∅`, which follows from the cited rootedness result [8]; we prove it.
  * Lemma 24 swaps the endpoints of its chain relative to its own definition of `H_r`; Theorem 4
    must be read with nonempty `N'` (for `N' = ∅` the valency is empty).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finitely many agents; synchronous, communication-closed rounds (Heard-Of style). A pattern is any
  sequence of communication graphs from the model `N` (oblivious adversary). Self-loops are implicit.
  No failures beyond what the graphs encode.
* Algorithms are deterministic and full-information-capable: arbitrary state, agent-dependent initial
  state, outputs need not lie in the hull of received values. This is a larger class than the paper's,
  so the lower bounds are stronger.
* Asymptotic consensus: in every execution all outputs converge to a common limit in the hull of the
  inputs. Values lie in any nontrivial real normed space (covers `ℝ^d`); the midpoint algorithm is on
  `ℝ`.
* Valency = set of limits reachable from a configuration (equal to the paper's `Y*` on reachable
  configurations). Diameters and rates live in `ℝ≥0∞`. Snapshots and properties (§6.1) are replaced
  by block patterns.
* Approximate consensus: `ε, Δ` are fixed parameters, and only time-`T` decisions are constrained
  (weaker than the paper's spec, so stronger lower bounds).
* Section 8: only the network model `N_A` ("wait for `n − f` messages") is formalized, not the
  reduction from asynchronous crash executions.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (`n = 2`, rate `≥ 1/3`), Theorem 2 (`≥ 1/2`) | `theorem1`, `theorem2` | `LowerBounds.lean` |
| Theorem 3 (`≥ (1/2)^{1/(n−2)}`) | `theorem3` | `Psi.lean` |
| Tightness: Algorithm 1, midpoint | `alg1_rate_eq`, `midpoint_rate_eq` | `Algorithms.lean` |
| Theorem 4 (⇒) | `theorem4_mp` | `Exact.lean` |
| Theorem 4 (⇐) false; repaired | `theorem4_false`, `fd_solves`; `theorem4_mpr_repaired`, `theorem4_repaired` | `Theorem4.lean`, `FirstDeviation.lean` |
| Lemma 20, Lemma 21, Theorem 5 | `Alg.val_inter_nonempty_alpha`, `Alg.lemma21`, `Alg.theorem5`, `theorem5_paper` | `Alpha.lean`, `Exact.lean` |
| Theorem 6 (`≥ 1/(⌈n/f⌉+1)` in `N_A`) | `theorem6` | `Alpha.lean` |
| Theorems 8–11 (approximate consensus) | `theorem8`, `theorem9`, `theorem10`, `theorem11` | `Approximate.lean` |

Lemma 21 is proved with constant `1/(n−1)` instead of `1/n`, and Theorem 6 under weaker hypotheses
(`n ≥ 2`, `1 ≤ f < n`).

**Not formalized.** Theorem 7 (MinRelay, asynchronous crashes); the characterization of exact
consensus from [12] (Theorem 19, β-classes), which appears only as the hypothesis `CouloumaHyp` of the
repaired Theorem 4; the amortized midpoint algorithm of [9] (Theorem 3's tightness remains cited).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: Algorithm 1 and the midpoint algorithm are proved to solve asymptotic
consensus with the matching rates. The Heard-Of round model and chain/diameter lemmas are in CSLib
(`Cslib/Computability/Distributed/DynamicNetworks/{HeardOf,Chain}.lean`).
