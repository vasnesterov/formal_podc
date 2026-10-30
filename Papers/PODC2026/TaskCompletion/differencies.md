# Differences between the formalization and the paper

Paper: Fischer, Gelles, *The Task Completion Problem and its Application to Crash-Resilient
Computation*, PODC 2026, arXiv:2605.17961v1. Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Errors and gaps in the paper's proofs (statements remain true)

1. **Lemma 3.1, first part (Definition 1(1) for ≥ m of the 2m sets).** The paper bounds
   `Pr(M < m) ≤ Pr(M < (1 − 0.98)E[M])`. Since `(1 − 0.98)E[M] ≈ 0.04m < m`, the event `M < m` is
   *larger* than `M < 0.04m`, so the inequality goes the wrong way. With the correct
   `δ ≈ 1 − 1/1.98` Chernoff only gives `Pr(M ≥ m) ≥ 1 − e^{−0.24m}`, which is `≈ 0.22 < 1/2` for
   `m = 1`. Repair: Markov's inequality on the number of bad sets (each set is bad with probability
   `≤ 8k/(nB) ≤ 1/576` by Chebyshev), giving failure probability `≤ 1/288`. Inside a proof → proof repair (R1).
2. **Lemma 3.1, second part (union bound over the k-subsets).** The paper needs
   `C(2m,k) · e^{−(ε/2)²(1−ε/2)n/2} < 1/2` with `C(2m,k) ≤ 2^{2cn}` and `c = ε³/8`. This requires
   `2ε ln 2 < 1 − ε/2`, i.e. `ε < 0.53`. (The displayed line even drops the `/2` of the
   Chernoff exponent; with it dropped one still needs `ε < 0.84`.) The lemma is stated for every
   `ε ∈ (0,1)`, so the proof fails for large `ε`. Repair: independence of the "bad" events over
   the elements `j`, plus a union bound over the `t = ⌊εn⌋+1`-sets of bad elements:
   `C(n,t)·a^t ≤ (e a/ε)^t` with `a ≤ 2/(ε²B) ≤ ε/288` (Chebyshev), and `C(2m,k) ≤ 2^{2m} ≤ 2^t`. This works for all `ε` and
   all `n`; it needs only second moments, no Chernoff bound. The statement is true → proof repair (R1).
   The paper's own argument still covers the small `ε` Theorem 4.1 needs (we use `ε = (1−α)/8 < 1/8`).
3. **Lemma 4.3 / Algorithm 1, termination condition.** The proof of Lemma 4.3 runs the loop
   "until `k_i < 1`". But `k_i = ⌈(1−ε)^{i−1}m⌉ ≥ 1` for every `i`, so this never happens (the
   test `1 ≤ k_i` in line 4 is also always true). Footnote 3 gives the right condition: once
   `k_i ≤ 2B`, `N_{i+1} = 0`. We run Algorithm 1 up to and including the first iteration with
   `k_i ≤ 2B` (`numIter`). Proof slip with the intended fix in the paper (R3) → proof repair.
4. **Lemma 4.5, induction step.** "If `N_i > k_{i+1}`, the conditions of claim (b) hold" needs
   `N_i ≥ (1−ε)k_i`. This is true but unproved: `N_i ≥ k_{i+1} + 1 > (1−ε)k_i` by integrality
   (`one_sub_mul_ceil_lt`, the same estimate as Lemma A.2). Routine.
5. **Lemma 4.5, claim (b), counting.** We count the crashed nodes of `J_i` slightly differently:
   only nodes of `J_i` that survive the iteration, with `|G| ≥ (1−ε−α)n`. Our progress condition is
   `4ε ≤ (1−ε−α)(1−ε)` instead of `(1−4ε−(1+ε)α)/2 ≥ ε`. Both hold for `ε = (1−α)/8`, the value we
   use. Not an error.
6. **Claim B.2 (proof).** The negation of "attempted by at most `2n'/k'` nodes" is written as "at
   least `2n'/k' + 1` nodes", which is only right when `2n'/k'` is an integer. The argument works
   with "more than". Harmless.
7. **Theorem B.1 (proof).** The total-crash bound `Σ_{i≤r} 4n/log n ≤ αn` needs `r ≤ α log n/4`.
   This holds because `r = O(log n/log log n)`, but the paper does not say so. The paper's
   assumption `⌊αn/logⁱn⌋ ≤ ⌊αn/log^{i−1}n⌋/2` holds once `log n ≥ 2`. Harmless.

## Statement-level differences

- **Theorem 4.1 and `log n`.** For `n = 1` the bound `O(R⌈M/n⌉ log n)` is `0`, which is impossible.
  We state the theorem for `n ≥ 2` (degenerate case, R2; the paper does not count it as an
  error and neither do we).
- **Lemma 3.1.** We prove it as stated (`lemma_3_1`, "for sufficiently large `n`") and in a
  stronger form for **all** `n` (`lemma_3_1_all_n`).
- **Definition 1(2).** "Any `k` sets `A_{i_1}, …, A_{i_k}`" is read as `k` *distinct* indices, i.e.
  a `k`-subset `I` of the index set. This is the only way the paper uses it (`I'` is a set of `k_i`
  tasks).
- **Lemma 3.1, proof text.** The size argument says "for any `i ∈ [m]`" while the sets range over `[2m]` (typo).
- **Lemma A.2.** The hypothesis `y ≥ 0` is not needed. We keep it to match the paper.
- **Theorem B.1 is proved in a stronger model.** The algorithm is a *full-information strategy*:
  each node's choice may depend on the whole crash history, which covers an oracle for incomplete
  tasks. The quantitative form is: for `n ≥ ⌈e^e⌉` and `r < (α/4)·ln n/ln ln n`, every strategy
  has an adversary with `≤ αn` crashes that leaves a task incomplete after `r` rounds. The
  non-asymptotic core is `exists_incomplete`: `L ≥ 2`, `2rn ≤ fL`, `L^r ≤ M`. The Lean statement
  uses natural logarithms; the paper uses `log₂`, which only changes the constant.

## Modelling choices

- **Iteration-level model of Algorithm 1.** One iteration = task phase (`2BR` rounds) + one
  broadcast round, counted as `2BR + 1` rounds. Message contents other than the bits `s_{i,v}`
  are not modelled: the algorithm sends nothing else, and tasks are abstract.
- **Adversary.** A crash adversary is given per node: the iteration `crashIter v` in which it
  crashes; whether it survived the task phase of that iteration (`fin v`); and which nodes get its
  broadcast bit in that iteration (`reach v`, an arbitrary subset, as in the paper's crash model).
  The algorithm is deterministic, so quantifying over these data covers all adaptive adversaries.
  A node that crashes in iteration `c` with `fin`, and whose bit reaches everybody, counts as
  crashed. That only makes the adversary stronger.
- **Completed tasks are under-approximated.** `Done` counts only the tasks of `U_{j,u}` for nodes
  `u` that complete their whole list. A node that crashes mid-phase may really have completed a
  prefix of its list, but the theorem says *all* tasks are in `Done`, so this only makes it stronger.
- **Theorem 4.1, batching.** `m = ⌊cn⌋` with `c = ε³/8`, `ε = (1−α)/8`, `B = ⌈72/c⌉`, once
  Lemma 3.1 applies (`n ≥ N`, `⌊cn⌋ ≥ 1`); otherwise `m = 1`. A batch of `m ≤ 2B` tasks needs no
  covering family. Batch `b` runs in the global iterations `[bK, (b+1)K)` against a single global
  adversary (crash budget `αn` overall). Task `t` is task `t mod m` of batch `⌊t/m⌋`; the last batch
  is padded with dummy tasks.
- **Covering families.** Algorithm 1 takes the agreed families `F k` as a parameter (`Params.F`);
  Theorem 4.1 instantiates them with families from Lemma 3.1 (by choice). The paper does the same
  ("each node deterministically constructs").
- **Lemma 3.1, probability space.** Probabilistic method on the uniform space
  `Fin n → Fin (2m) → Fin k`, with `j ∈ A_i` iff `x j i < B`: exactly the paper's independent
  `Bernoulli(B/k)` memberships.

## Not formalized

- Section 5 (robust simulation of congested-clique algorithms, Theorem 5.1 / 1.2): NetStore /
  NetRetrieve, MDS codes (Claim 2.1), the nested task-completion instances.
- Theorem 1.1 is the special case `M = n` of Theorem 4.1 and is not stated separately.
- The congested-clique bandwidth bound (`O(log n)`-bit messages). Algorithm 1 sends single bits,
  so the bound is immediate.
