# Order Statistics in Population Protocols via Simple Dynamics (PODC 2026)

Niccolò D'Archivio, Hind AlMahmoud, Emanuele Natale, Frederik Mallmann-Trenn.
*Order Statistics in Population Protocols via Simple Dynamics.* PODC 2026, Egham, pp. 425–436.
DOI [10.1145/3796701.3815922](https://doi.org/10.1145/3796701.3815922).
No arXiv version; the full version cited as [3] is HAL `hal-05548829` (checked; it adds the consensus-time
proof, Theorem 9, and the Top-k application, Corollary 10). Numbering below follows the
proceedings (Lemma 4.x; the full version numbers these 3.x).

## Model (as formalized)

- `n ≥ 1` agents `Fin n`; opinions in a **finite linear order** `α` (any finite set of real initial
  values is order-isomorphic to one; the dynamics only compares and copies opinions).
  Configuration `c : Fin n → α` (`Config n α`).
- **Randomness / scheduler**: sequential, one agent updates per round; a dynamics is a finite
  Markov chain given as a row-stochastic matrix `T` on configurations, built with
  `Cslib.Probability.Markov.randomMap μ F` ("draw `ω` with probability `μ ω`, move to `F ω c`").
  - Copy-or-Max (Sec. 4.1/4.2): `ω = (u, v, copy?)`; edge `(u, v)` w.p. `w u v / W`
    (clique: `w ≡ 1`, i.e. `u, v` uniform and independent, `v = u` allowed), copy w.p. `p`,
    else `X_u ← max(X_u, X_v)` (`copyOrMaxW`, `copyOrMax`). Weights `w ≥ 0`, `W = ∑ w > 0`,
    self-loops allowed, `p ∈ (0, 1)`.
  - Biased-Median (Sec. 4.5): `u` uniform, `v, s` uniform and independent (the reading fixed by
    Lemma 4.8's counts), coin with success probability `p/(1-p)`, `p ∈ (0, 1/2]` (`biasedMedian`).
  - Self-Excluding Median (Sec. 4.7): `u, a, b, d` uniform independent, `X_u ← median` (`selfExcludingMedian`).
  - Binary 2-Choices / 3-Majority on `Bool` (`twoChoices`, `threeMajority`).
- No failures, no adversary. No fairness assumption is needed: everything is about the random
  scheduler.
- **Output convention / fixation probability**: probability of consensus on `x` is
  `lim_{t→∞} (T^t) c (const x)` (`Tendsto … atTop (𝓝 _)`). Consensus configurations are absorbing,
  so this is the probability of eventually being forever in consensus on `x`; the limit's
  existence is part of every theorem. Ranks: `rank c x = #{u | c u ≤ x}`; for distinct opinions
  `rank c (c u) = k` iff `c u = x_(k)`. With ties, the probability of `x` is the sum of `π_k`
  over its ranks `#{u | c u < x} < k ≤ #{u | c u ≤ x}` (paper: "summing up").
- Proof method (differs from the paper): **threshold method**. For every lower set `D` of
  opinions, `cnt D c` performs a birth–death walk; `c ↦ ∑_{k ≤ cnt D c} π_k` is harmonic iff the
  balance `π_{m+1}·P[up] = π_m·P[down]` holds; absorption + harmonicity give the law
  (`fixation_of_harmonic`). The paper's rank-ancestry lemmas are also verified (`RankAncestry.lean`).

## Main results ↔ Lean

| Paper | Lean | File | Status |
|---|---|---|---|
| Def. 4.1 circulation, Lemma 4.6 | `IsCirculation`, `isCirculation_iff_cut` | CopyOrMax.lean | ✔ |
| Lemma 4.2 (one-step order statistics; also with ties) | `orderStat_step` (+ `copyOrMax_orderBased`: paper's `f_k, h_k`) | RankAncestry.lean, Instances.lean | ✔ |
| Lemma 4.3 (expected order statistics) | `orderStat_expectation` | RankAncestry.lean | ✔ |
| Lemma 4.4 (rank ancestry `P[X^t_(i)=X^0_(j)] = P^t_{j,i}`) | `orderStat_ancestry_injective`, `orderStat_ancestry` (ties) | RankAncestry.lean | ✔ |
| Lemma 4.5 (stationary law of `Pᵀ`, `g_k ≥ (n²+1)/(2n²)`) | `lemma45_detailed_balance`, `lemma45_diag_bound` | Instances.lean | ✔ (irreducibility/uniqueness not needed, not formalized) |
| Prop. 5 / Thm 1(1) (clique, geometric law) | `copyOrMax_fixation_injective`, `copyOrMax_fixation` (ties) | CopyOrMax.lean | ✔ |
| Prop. 6 (⇐) / Thm 1(2) | `copyOrMaxW_fixation_injective`, `copyOrMaxW_fixation` | CopyOrMax.lean | ✔ (paper's proof has a gap; new proof) |
| Prop. 6 (⇒) / Thm 1(2) "only if" | `copyOrMaxW_geomFix_iff` (`isCirculation_of_geomFix`, `connected_of_geomFix`) | Converse.lean | ✔ (paper's proof invalid; new proof) |
| Lemma 4.7 | — (bypassed; lemma valid). Minor D/D⁻¹ slip in its instantiation in the proof of Prop. 6 Item iv): `Counterexample.prop6_itemIv_sqrt_slip` | Counterexample.lean | ✔ clarification |
| Def. 4.2 + Thm 7 (Order-Based) | Def. 4.2 under-specified; intended reading: `OrderBased`, `orderBased_fixation`; clarification (literal reading fails): `Counterexample.tieMax_eq_copyOrMax`, `tieMax_fixation`, `tieMax_not_geometric` | OrderBased.lean, Counterexample.lean | ✔ (intended reading) + clarification |
| Lemma 4.8 / proof of Thm 2 (`f_k, h_k`) | `biasedMedian_orderBased`, `bm_upMass`, `bm_downMass` | Instances.lean, BiasedMedian.lean | ✔ |
| **Thm 2** (Biased-Median, binomial law) | `biasedMedian_fixation_injective`, `biasedMedian_fixation` | BiasedMedian.lean | ✔ |
| Cor. 3 (2-Choices) | `twoChoices_eq_median`, `twoChoices_fixation` | BiasedMedian.lean | ✔ |
| Lemma 4.9 / proof of Thm 8 (`f_k, h_k`) | `selfExcludingMedian_orderBased`, `sx_upMass`, `sx_downMass` | Instances.lean, SelfExcluding.lean | ✔ |
| **Thm 8** (Self-Excluding Median, Γ-law) | `selfExcludingMedian_fixation_injective`, `selfExcludingMedian_fixation`; law: `sxLaw`, `sum_sxLaw`, `sxLaw_ratio` | SelfExcluding.lean, BetaBinomial.lean | ✔ |
| Cor. 4 (3-Majority, Beta-Binomial) | `threeMajority_eq`, `threeMajority_fixation`, `sxLaw_eq_betaBinomial`, `betaBinomial_symm` | SelfExcluding.lean, BetaBinomial.lean | ✔ |
| Thm 1 "O(log n) parallel rounds w.h.p." / full-version Thm 9 | — | — | not formalized (see differencies 13) |
| Fact 4.1, full-version Fact 3.2 (cycle), Cor. 10 (Top-k) | — | — | not formalized (informal / application) |

All theorems above are sorry-free; `#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound` (checked for every main theorem listed).

## Findings (details in `differencies.md`)

- All main fixation laws (Theorem 1 both parts, Theorem 2, Corollaries 3, 4, Theorem 8) are
  **correct**; verified, also for initial configurations with ties.
- **Proposition 6 proofs are flawed in both directions** (configuration-dependent random matrices
  treated as deterministic; "the limit is attained at a finite time N"); minor: its Item iv)
  instantiates Lemma 4.7 with `D = diag(√π)` instead of `diag(1/√π)` (Lemma 4.7 itself is valid).
  Proposition 6 itself is true:
  new proof via harmonic functions (⇐) and threshold lumping + harmonicity at a one-zero binary
  configuration (⇒).
- **Definition 4.2 is under-specified** (it only constrains configurations with distinct
  opinions; the paper's gloss "a function of the ranks only" shows the intended class). Under the
  intended reading (rank/threshold structure on all configurations) Theorem 7 holds
  (`orderBased_fixation`). Clarification: under the literal reading it fails — a dynamics equal to
  Copy-or-Max on distinct configurations but Max on ties fixes on `x_(3)` with probability 7/9
  instead of 4/7 (`n = 3`, `p = 1/2`).
- Ambiguity: Sec. 4.5's "unordered pair (v, s), may be equal" must be read as two independent
  samples (as Lemma 4.8 does); with a uniform unordered pair the Median law for `n = 3` is
  `(2/7, 3/7, 2/7)`, not binomial (numerical check).

## Infrastructure / CSLib candidates

- `Cslib/Probability/Markov/Absorption.lean` (now in CSLib, generic finite Markov chains): `randomMap`
  kernels, `tendsto_sum_compl_of_absorbing` (absorption w.p. 1 when an absorbing set is reachable),
  `tendsto_sum_mul_of_harmonic` (absorption probabilities from harmonic functions),
  `pow_mulVec_comp_of_lump`/`randomMap_lump` (lumping), `pow_eq_zero_of_closed`.
- `BetaBinomial.lean`: `risingVandermonde` (rising-factorial Chu–Vandermonde),
  `sum_betaBinomial` (Beta-binomial normalisation) — **CSLib/Mathlib candidates**.
- Threshold method for opinion dynamics (`Basic.lean`, `Fixation.lean`: `fixation_of_harmonic`,
  `harmonic_of_balance`, `reach_const_of_step`) — reusable for voter-type dynamics.

## Files

`Basic` (configs, counts, lower sets, median) → `Fixation` (generic theorem) → `CopyOrMax`,
`BiasedMedian`, `BetaBinomial`, `SelfExcluding`, `Converse`, `OrderBased`, `Instances`,
`RankAncestry`, `Counterexample`.
