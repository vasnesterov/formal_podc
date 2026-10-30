# Task Completion in Crash-Prone Congested Cliques — PODC 2026

Orr Fischer, Ran Gelles. *The Task Completion Problem and its Application to Crash-Resilient
Computation.* PODC 2026. DOI [10.1145/3796701.3815916](https://doi.org/10.1145/3796701.3815916).
Formalized version: arXiv:2605.17961v1.

**Verdict: 🛠️ Proof repaired.** All checked statements are true as written:
- the existence of load balancing covering families (Lemma 3.1);
- the analysis of Algorithm 1 (Lemmas 4.3–4.5);
- the `O(R⌈M/n⌉ log n)` deterministic task-completion algorithm (Theorem 4.1);
- the `Ω(log n / log log n)` lower bound (Theorem B.1).

The probabilistic proof of Lemma 3.1 has two genuine errors and needs a different tail argument.

## Mistakes in the paper

- **Lemma 3.1, union bound for large ε (proof gap, statement true).** The second half of the
  proof bounds `Pr(|J| < (1−ε)n)` for one `k`-subset by a Chernoff bound around the mean, which is
  `e^{−ε²(1−ε/2)n/8}`. It then takes a union bound over the at most `2^{2m} ≤ 2^{2cn}` subsets,
  with `c = ε³/8`. This union bound is below 1 only when `2ε ln 2 < 1 − ε/2`, i.e. `ε < 0.53`.
  The lemma claims every `ε ∈ (0,1)`. (The displayed inequality also silently drops the `/2` of
  the exponent; even then it needs `ε < 0.84`.) The lemma is still true.
  The gap does not affect Theorem 4.1, which needs only a small `ε` (we use `ε = (1−α)/8 < 1/8`).

  Our proof uses only second moments, for all `ε` and all `n`. Chebyshev shows that each element
  is bad with probability `a ≤ 2/(ε²B) ≤ ε/288`. The bad events are independent across elements.
  So the probability that `⌊εn⌋+1` elements are bad is at most `C(n,t)a^t ≤ (e a/ε)^t`, which
  beats `2^{2cn}` for every `ε`. (`lemma_3_1`, `lemma_3_1_all_n`)
- **Lemma 3.1, first half (wrong inequality direction).** To show that at least `m` of the `2m`
  random sets have the right size, the paper writes `Pr(M < m) ≤ Pr(M < (1−0.98)E[M])`. The
  right-hand event `M < 0.04m` is smaller than `M < m`, so this is backwards. A correct Chernoff
  bound gives only `Pr(M ≥ m) ≥ 0.22` for `m = 1`. Markov's inequality on the number of bad sets
  fixes it: each set is bad with probability `≤ 1/576`.
- **Termination of Algorithm 1 (proof slip).** The proof of Lemma 4.3 runs the loop "until
  `k_i < 1`", but `k_i = ⌈(1−ε)^{i−1}m⌉ ≥ 1` always. The correct stopping rule is the one in
  footnote 3: stop after the first iteration with `k_i ≤ 2B`, at which point `N_{i+1} = 0`. We
  formalize that rule (`numIter`, `lemma_4_3_1`).
- **Small gaps.**
  - Lemma 4.5's induction uses `N_i > k_{i+1} ⇒ N_i ≥ (1−ε)k_i` without proof; it holds by
    integrality.
  - Claim B.2's proof negates "at most `2n'/k'`" as "at least `2n'/k'+1`".
  - Theorem B.1's crash count `r · 4n/log n ≤ αn` needs `r ≤ α log n/4`, which is left implicit.
  - For `n = 1` the bound `O(R⌈M/n⌉ log n)` is 0; we state Theorem 4.1 for `n ≥ 2`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Network.** `n` nodes `Fin n` and `M` abstract tasks. The model is synchronous and
  deterministic. A task takes `R` rounds and is completed iff its executor does not crash during
  them (*executor-safe*, *idempotent*). At most `αn` crashes over the whole execution, `α ∈ [0,1)`.
- **Algorithm 1 (`Algorithm.lean`), iteration-level model.** An iteration is a task phase of
  `2BR` rounds plus one broadcast round of the bits `s_{i,v}`, so it costs `2BR + 1` rounds.
- **Adversary.** It is adaptive and arbitrary. For every node it fixes:
  - the iteration in which the node crashes;
  - whether the node survived that iteration's task phase;
  - which nodes receive its last broadcast bit (any subset, as in the paper's crash model).
- **Knowledge and completion.** `C_{i,v}`, "fully verified" and `N_i` are defined as in the paper.
  Completed tasks (`Done`) are under-approximated, which only strengthens the result.
- **Theorem 4.1 (`Main.lean`).** It runs `⌈M/m⌉` batches of `m = ⌊cn⌋` tasks sequentially against
  one global adversary. The covering families come from Lemma 3.1, and `ε = (1−α)/8`.
- **Lower bound (`LowerBound.lean`).** `R = 1`; each node attempts one task per round. The
  algorithm is a full-information strategy: crash history ↦ attempted task per node. This is
  stronger than the paper's message-passing algorithms, and even than an oracle for the incomplete
  tasks, so the lower bound is at least as strong as the paper's.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1 (load balancing covering family) | `IsLBCF`, `load` | `Basic.lean` |
| Lemma A.2 | `floor_mul_ceil_le_ceil_mul` | `Basic.lean` |
| Lemma 3.1 | `lemma_3_1` (and `lemma_3_1_all_n`: every `n`) | `Covering.lean` |
| Algorithm 1 | `Alg.C`, `Alg.T`, `Alg.Done`, `Alg.numIter` | `Algorithm.lean` |
| Claim 4.2 | `Alg.claim_4_2` | `Algorithm.lean` |
| Lemma 4.4 | `Alg.lemma_4_4` | `Algorithm.lean` |
| Lemma 4.5 (claim (b) in both cases) | `Alg.lemma_4_5` (`Alg.N_succ_eq_zero_of_small`, `Alg.N_succ_le_of_large`) | `Algorithm.lean` |
| Lemma 4.3 (1), (2) | `Alg.lemma_4_3_1`, `Alg.lemma_4_3_2` | `Algorithm.lean` |
| Theorem 4.1 | `theorem_4_1` | `Main.lean` |
| Claim B.2 | `LowerBound.claim_B_2` | `LowerBound.lean` |
| Theorem B.1 | `LowerBound.theorem_B_1` (core: `LowerBound.exists_incomplete`) | `LowerBound.lean` |

All names are in the namespace `Podc.TaskCompletion`.

**Not formalized.**
- Section 5: the robust congested-clique simulation (Theorems 1.2/5.1, error-correcting codes,
  NetStore/NetRetrieve).
- The `O(log n)` message-size bound (Algorithm 1 only sends single bits).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Theorem 4.1 is existential over the algorithm parameters, and its hypotheses
(`Alg.Good`) are discharged from Lemma 3.1 inside the proof, so it is not vacuous. The proofs use
Mathlib and CSLib's finite uniform-probability counting (`Cslib.Probability.Finite.Uniform`).

**CSLib candidates.** The generic counting lemmas at the top of `Covering.lean` (marked
`-- CSLib candidate`, for `Cslib/Probability/Finite/Uniform.lean`):
- `card_mul_sum_sq_sum_apply`: the second moment of `∑_j h_j(g j)` for centred `h_j`;
- `card_le_abs_sum_apply_le`: Chebyshev in counting form;
- `card_many_le_choose`: many independent rare events with the factor `C(|ι|,t)·a^t`.
