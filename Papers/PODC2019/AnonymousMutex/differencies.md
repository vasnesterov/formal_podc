# Differences between the formalization and the paper

Paper: Z. Aghazadeh, D. Imbs, M. Raynal, G. Taubenfeld, P. Woelfel, *Optimal Memory-Anonymous
Symmetric Deadlock-Free Mutual Exclusion*, PODC 2019 (arXiv:1810.03723v1).

## Errors in the paper

1. **Theorem 2 is false (Algorithm 1 is not deadlock-free).** For `n = 4` processes and
   `m = 5 ∈ M(4)` registers there is a fair infinite execution in which all four processes stay in
   `lock()` forever, nobody is in the critical section and no operation completes
   (`AnonymousMutex.theorem_2_false`, `Alg1Livelock.lean`, with the explicit 28-step period in the
   module docstring). Anonymity permutations: `p0: [0,4,1,2,3]`, `p1: [1,2,3,0,4]`,
   `p2: [2,0,1,3,4]`, `p3: [3,0,1,2,4]` (local → physical); line 6 writes the first `⊥` entry in
   local order. In each period: all four processes snapshot the empty memory; `p0`, `p1` fill the
   memory (`p0` owns 2, `p1` owns 3); `p0` (2 < 5/2) starts shrinking; the *stale* writes of `p2`
   and `p3` (decided on the empty snapshot) overwrite two registers of `p1`; now `p1`, `p2`, `p3`
   own 1 register each, below the averages 5/3 and 5/4, so everybody shrinks and the memory is
   empty again.
   *Which algorithm is refuted.* Line 6 says "write into some `x` with `view[x] = ⊥`" without
   fixing `x`; the paper's theorem must therefore hold for every way of resolving this choice
   (equivalently, for the nondeterministic algorithm). We resolve it as "the first `⊥` entry in the
   process's local order" (`firstBot` in `Alg1.lean`) and exhibit a livelock for this legal
   resolution, which refutes Theorem 2 as stated. We do **not** show that every resolution fails.
   What was checked: the bounded model checker `modelcheck/alg1s.cpp` lets line 6 pick *any* `⊥`
   register (nondeterministically, which over-approximates every choice rule) and found the livelock
   for `n = 4, m = 5`; the same 28-step schedule is also a livelock for the "last `⊥` in local
   order" rule (with the reversed permutations; replayed in `modelcheck/replay.py`). Since the
   permutations are adversarial, any rule of the form "the first `⊥` w.r.t. a fixed order of the
   local names" is covered. Rules that inspect the contents of the view (e.g. "a `⊥` next to an own
   register") were not explored; such a rule might rescue the algorithm.
   *Versions.* The text used is arXiv:1810.03723v1 (arXiv has no later version). The ACM proceedings
   version could not be compared; all statements here refer to arXiv v1.
   *Where the proof breaks*: Claim 4 only shows that at every time *some* competing process does
   not withdraw; the proof of Theorem 2 then concludes "at least one competing process never calls
   `shrink()`", which does not follow (the non-withdrawing process changes over time). The proof
   also never considers writes based on outdated snapshots, which can destroy the registers of the
   process owning the most registers. (Claim 5's "w.l.o.g. all competing processes have obtained
   the same view" has the same issue.)
   *Consequence*: the paper's main claim that `m ∈ M(n) \ {1}` is a **tight characterization for
   read/write anonymous memory** (abstract, §1.3, §4.2, §7) is **not established**: only the
   necessity of `m ∈ M(n)` holds (`theorem_5`). Bounded exhaustive model checking (any register
   choice at line 6, any shrink order) found no livelock for `n = 2` (`m ∈ {3,5,7}`, i.e. all
   `1 < m ≤ 7` in `M(2)`) and `n = 3` (`m ∈ {5,7}`), so Algorithm 1 may be correct for `n ≤ 3`; this is not proved.
2. **Theorem 4's proof is only a sketch** ("Repeating this argument, eventually one of the
   processes will find…"). It does not address that the views of Algorithm 2 are read
   non-atomically (a process may count registers of another process that the latter held at
   different times, e.g. before and after re-entering), nor that a process waiting at lines 8–10 may
   re-enter after a non-atomic all-`⊥` scan while other processes hold registers. The theorem is
   true; the formal proof is new:
   * `no_inflation` (`Alg2Inflation.lean`): if `p` owns a register during its scan, the number of
     entries of `p`'s view equal to `q`'s identifier is at most what `q` owned *simultaneously* at
     some time of the scan (owned sets grow while competing, shrink while erasing, and a waiting
     `q` cannot re-enter during `p`'s scan because its all-`⊥` scan reads `p`'s register);
   * `resign_bound`: a withdrawal with `c ≥ 1` registers needs another process owning `> c`
     registers during the scan;
   * `exists_holder` (`Alg2Holder.lean`): with `c*` the eventual maximum of the number of owned
     registers, if `c* ≥ 1` a process owning `c*` registers late never withdraws again;
   * `endgame` / `zero_case` (`Alg2Endgame.lean`): afterwards re-entries stop, the memory becomes
     constant and full, and all remaining competitors own the same number of registers, which
     contradicts `m ∈ M(n)`.
3. **Theorem 5's proof** describes the scanning order through "order(pᵢ, k)", which is
   confused (processes do not access registers in a fixed order); the essence — a lock-step
   execution that preserves a rotational symmetry — is correct. Formalized with the rotation
   `sh = (finRotate m)^(m/g)` and `π pᵢ = shⁱ`; in a round all `g` processes access *different*
   physical registers, so sequential rounds equal simultaneous ones. The paper uses "ℓ divides m";
   we use `g = gcd(ℓ, m)` processes.
4. Minor: §1.3 describes `compare&swap(x, old, new)` as succeeding "iff `new = v`" (should be
   `old = v`). The algorithm uses it correctly; we model it as an atomic read-modify-write.

## Strengthened or weakened statements

5. **Theorem 5** is proved for *arbitrary* symmetric algorithms using arbitrary atomic
   read-modify-write registers **and atomic snapshots**, arbitrary register value types and local
   state types; it only needs correctness for *one* injective identifier assignment and all
   anonymity permutations (in fact for the rotation permutations). It thus also yields the
   read/write necessity result attributed to [15] and covers the snapshot model of Algorithm 1.
6. **Theorem 1** holds whenever `n ≤ m` (`Alg1.theorem_1`); the paper's hypothesis
   `m > 1 ∧ m ∈ M(n)` implies `m > n` (`theorem_1_of_M`). Mutual exclusion holds in *all*
   executions, client-well-formed or not.
7. **Theorem 3** holds for every `m ≥ 1` (no `m ∈ M(n)` needed), every identifier assignment and
   all permutations.
8. **Theorem 4** assumes `m ≥ 1` and `m ∈ M(n)` (paper: `m ∈ M(n)`, where `m ≥ 1` is implicit;
   with `m = 0` the code is meaningless).
9. The read/write characterization's exclusion of `m = 1` relies on the Burns–Lynch bound
   `m ≥ n` (cited as [3]); we prove the needed special case directly: one read/write register
   cannot support deadlock-free mutual exclusion for two processes, even without symmetry
   (`one_register_impossible`).

## Modelling choices

10. **Symmetry** ("identifiers can only be compared for equality") is formalized semantically:
    initial states, invocations and steps commute with every renaming of identifiers
    (`SymAlg.Symmetric`); `⊥` is fixed by renamings. Processes know `n` (irrelevant here).
11. **Memory anonymity**: one adversarial permutation per process, fixed for the execution.
    Theorems 1, 3, 4 hold for all permutations; the counterexample and the lower bound choose them.
12. **Snapshot** (Alg. 1): an atomic primitive, as assumed in §2.1 (the paper's double-collect
    implementation is not formalized). The livelock uses only atomic snapshots.
13. **Granularity**: every loop iteration is one atomic access; iterations of line 7 of
    Algorithm 2 and of `shrink()` with `view[x] ≠ id` are skipped (no access); the bookkeeping
    between accesses (lines 4–6, 8–12) is folded into the preceding access. Returning from an
    operation is a separate step (CSLib convention).
14. **Line 6 of Algorithm 1** ("write into some `x` with `view[x] = ⊥`") is resolved as the first
    `⊥` entry in local order. Theorem 1 does not depend on this choice; the counterexample uses
    exactly this natural rule (with the chosen permutations).
15. `owned() < m/cnt` and `owned > m/2` are compared over the rationals in the paper; we use
    `owned * cnt < m` and `m < 2 * owned`.
16. **Deadlock-freedom** follows §2.3 literally: fair infinite client-well-formed executions; fair =
    every process with a pending operation eventually takes a step. Mutual exclusion is stated for
    finite client-well-formed executions (`lock(); CS; unlock()` pattern).
17. The lock-step execution of Theorem 5 lets the processes return in the same round: then all
    `g ≥ 2` of them are in the CS (mutual exclusion violated); otherwise the execution is a fair
    execution without completions (deadlock-freedom violated) — as in the paper.
