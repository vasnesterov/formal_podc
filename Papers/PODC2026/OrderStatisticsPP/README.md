# Order statistics in population protocols — PODC 2026

Niccolò D'Archivio, Hind AlMahmoud, Emanuele Natale, Frederik Mallmann-Trenn. *Order Statistics in Population
Protocols via Simple Dynamics.* PODC 2026. DOI
[10.1145/3796701.3815922](https://doi.org/10.1145/3796701.3815922). Formalized version: the proceedings
(numbering follows it; the full version, HAL `hal-05548829`, numbers Section 4 as Section 3).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** All laws of the consensus value are proved, also for initial configurations with ties:
Copy-or-Max (Theorem 1, Proposition 6), Biased-Median (Theorem 2, Corollary 3), Self-Excluding Median (Theorem 8,
Corollary 4), and Order-Based dynamics (Theorem 7, with a repaired Definition 4.2). Both directions of Proposition 6
needed new proofs. The `O(log n)` convergence time stated in Theorem 1 rests on an invalid proof, and nothing we proved
saves it.

## Mistakes in the paper

### ❌ Theorem 1 (the `O(log n)` parallel-rounds claim; full-version Theorem 9)
The deferred proof of "convergence occurs in `O(log n)` parallel rounds with high probability" dominates the
geometric, state-dependent holding times by bounded i.i.d. variables, which is invalid.

**Impact.** The claim is plausible, but it is neither proved nor refuted (not formalized). The fixation laws, the
paper's main content, are unaffected.

**Details.** The geometric, state-dependent holding times are "upper-bounded by i.i.d. `Z_s`" with a bounded,
state-independent distribution, but no such domination holds. The restart step ("consensus is only faster")
lacks a monotonicity argument. The bound implicitly needs `p` constant: as `p → 1` the dynamics approaches the
voter model, which needs `Θ(n)` parallel rounds.

### 🔧 Definition 4.2 and Theorem 7 (Order-Based dynamics)
Definition 4.2 only constrains configurations with pairwise distinct opinions, and under this literal reading
Theorem 7 is false: a dynamics that is Copy-or-Max (`p = 1/2`) on distinct configurations but Max on tied ones fixes on `2`
from `(0, 1, 2)` with probability `7/9` instead of `π_3 = 4/7` (`Counterexample.tieMax_not_geometric`).

**Impact.** The paper's gloss ("a function of the ranks only") shows the intended class, and
under it Theorem 7 holds (`orderBased_fixation`). All three concrete dynamics are covered.

**Details.** After the first copy every configuration has ties, so the definition says nothing about the states
the dynamics actually visits. The instance above is Order-Based in the literal sense.

**Repair.** We require the rank structure on all configurations, in threshold form. Then Theorem 7 holds;
Copy-or-Max, Biased-Median and Self-Excluding Median satisfy it with exactly the paper's `f_k, h_k`
(`orderBased_fixation`).

### ✏️ Slips
- §4.5 (Biased-Median): "an unordered pair `(v, s)`, may be equal" must mean two independent uniform samples, as
  Lemma 4.8's counts require, and Theorem 2 holds under that reading (`biasedMedian_fixation`). With a uniform unordered
  pair the Median law for `n = 3` is `(2/7, 3/7, 2/7)`, not binomial (an exact computation, not formalized).
- Proposition 6, item iv) instantiates Lemma 4.7 with `D = diag(√π)` where `diag(1/√π)` is needed
  (`Counterexample.prop6_itemIv_sqrt_slip`); Lemma 4.7 itself is fine.
- Lemma 4.2's footnote boundary should be `k = n + 1`, not `k = n`.

### Typos
- The full version divides by `n³` where `n⁴` is meant (ratios unaffected).

## Proof gaps (statements true)

### 🛠️ Proposition 6 (⇐) (weighted Copy-or-Max has the geometric law)
The proof relabels the nodes by rank at every round, so the matrices `P^(t)` depend on the random configuration
and eq. (6), `P[X^t_(i) = X^0_(j)] = (∏_s P^(s))_{j,i}`, has a random right-hand side.

**Impact.** Statement true; new proof (`copyOrMaxW_fixation`).

**Details.** Eq. (6) is not justified by "similarly to Lemmas 4.3 and 4.4", since the expectation of a product of
dependent random matrices is not the product of expectations. Lemma 4.7 concerns deterministic sequences.

**Repair.** A bounded harmonic function of threshold counts, which only needs `π` to be stationary for every
possible `P^(t)`, i.e. balanced flows across every cut (`copyOrMaxW_fixation`).

### 🛠️ Proposition 6 (⇒) (the geometric law forces a connected circulation)
The proof claims that geometric fixation probabilities give an `N` with `P[X^t_(i) = X^0_(j)] = π_j` for all
`t ≥ N`, but a limit need not be attained in finite time.

**Impact.** Statement true; new proof (`copyOrMaxW_geomFix_iff`).

**Details.** Already on the clique with `n = 2`, `P[X^t_(1) = x_(1)] = π_1 + (1−π_1)r^t ≠ π_1` for every `t`.
The proof also again treats `P^(N)` as deterministic.

**Repair.** Projecting onto a threshold reduces to binary Copy-or-Max. Harmonicity of the binary fixation
probability at the configuration with a single `0` at `v` forces in-flow(`v`) = out-flow(`v`). Disconnection
would make consensus unreachable (`copyOrMaxW_geomFix_iff`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- `n ≥ 1` agents, opinions in a finite linear order (a real initial configuration evolves inside its finite
  value set). Random sequential scheduler: one agent updates per step. Each dynamics is a finite Markov chain on
  configurations, given as a row-stochastic matrix built from a random map. No failures, no adversary.
- Sampling follows the paper's counts: clique pairs `(u, v)` are independent and uniform (`v = u` allowed);
  weighted Copy-or-Max picks edge `(u, v)` with probability `w u v / W`; the median dynamics draw independent
  uniform samples; 2-Choices and 3-Majority are binary.
- The fixation probability of `x` is `lim_{t→∞} P[X_t = (x,…,x)]`. Consensus is absorbing, so this is the
  probability of eventual consensus on `x`. The limit's existence is proved, not assumed. With ties, the
  probability of `x` is the sum of `π_k` over its ranks. The binomial law of Theorem 2 is Mathlib's
  `ProbabilityTheory.binomial` (`binomLaw_eq_binomial`: `π_k = P[Bin(n-1, 1-p) = k-1]`). Theorem 2 needs `p ≤ 1/2`, so
  the abstract's `K − 1 ~ Bin(n−1, 1−p)` covers only `1 − p ≥ 1/2`.
- Proof route differs from the paper: harmonic functions of threshold counts plus a finite-chain absorption
  lemma, instead of rank ancestry plus Perron–Frobenius. The paper's rank-ancestry lemmas are verified
  separately.

**Main results in Lean** (each with an `_injective` variant for distinct opinions).

| Paper | Lean | File |
|---|---|---|
| Lemmas 4.2–4.4 (order statistics, rank ancestry; with ties) | `orderStat_step`, `orderStat_expectation`, `orderStat_ancestry` | `RankAncestry.lean` |
| Lemma 4.5 (detailed balance, diagonal bound) | `lemma45_detailed_balance`, `lemma45_diag_bound` | `Instances.lean` |
| Theorem 1(1) / Proposition 5 (clique, geometric law) | `copyOrMax_fixation` | `CopyOrMax.lean` |
| Theorem 1(2) / Proposition 6 (⇐), (⇔) | `copyOrMaxW_fixation`, `copyOrMaxW_geomFix_iff` | `CopyOrMax.lean`, `Converse.lean` |
| Theorem 7 (intended Def. 4.2) and literal-reading counterexample | `orderBased_fixation`; `Counterexample.tieMax_not_geometric` | `OrderBased.lean`, `Counterexample.lean` |
| Theorem 2 (Biased-Median, binomial); Corollary 3 (2-Choices) | `biasedMedian_fixation`; `twoChoices_fixation` | `BiasedMedian.lean` |
| Theorem 8 (Self-Excluding Median, Γ-law); Corollary 4 (3-Majority, Beta-Binomial) | `selfExcludingMedian_fixation`; `threeMajority_fixation`, `sxLaw_eq_betaBinomial` | `SelfExcluding.lean`, `BetaBinomial.lean` |

**Not formalized.** The convergence-time claim (Theorem 1's `O(log n)`, full-version Theorem 9), Lemma 4.7
(bypassed), irreducibility, aperiodicity and uniqueness in Lemma 4.5 (not needed), the cycle example and the Top-k
application (Corollary 10 of the full version). Fact 4.1 has no proof and is not formalized; as written it covers neither
Copy-or-Max nor Biased-Median, whose adoption depends on the agent's own position, and Lemmas 4.1 and 4.8 compute
their `q_j(i)` directly.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
generic absorption and lumping lemmas for finite Markov chains come from CSLib
(`Cslib/Probability/Markov/Absorption.lean`).
