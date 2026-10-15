# Memory-Anonymous Symmetric Mutual Exclusion — PODC 2019

Zahra Aghazadeh, Damien Imbs, Michel Raynal, Gadi Taubenfeld, Philipp Woelfel. *Optimal Memory-Anonymous
Symmetric Deadlock-Free Mutual Exclusion.* PODC 2019. DOI
[10.1145/3293611.3331594](https://doi.org/10.1145/3293611.3331594). Formalized version: arXiv
[1810.03723](https://arxiv.org/abs/1810.03723) v1 (the only version); numbering follows it.

**Verdict: ❌ False claim.** **Theorem 2 is false**: the read/write algorithm (Algorithm 1) livelocks
for `n = 4` processes and `m = 5 ∈ M(4)` registers. So the headline tight characterization
`m ∈ M(n) \ {1}` for read/write anonymous memory is only half established: necessity holds, sufficiency
does not follow from the paper. Theorems 1, 3, 4 and 5 hold, and the characterization for
read-modify-write (compare&swap) registers is proved.

## Mistakes in the paper

* **Theorem 2 is false: Algorithm 1 is not deadlock-free.** With `n = 4` and `m = 5` there is a fair
  infinite execution with a 28-step period in which all four processes stay in `lock()` forever and
  nobody enters the CS. Each period goes as follows. All four processes snapshot the empty memory.
  `p0` and `p1` fill it, with `p0` owning 2 registers and `p1` owning 3. `p0` (2 < 5/2) starts
  shrinking. Then the *stale* writes of `p2` and `p3`, decided on the old empty snapshot, overwrite
  two of `p1`'s registers. Now `p1`, `p2`, `p3` own one register each, below the averages 5/3 and
  5/4. So everybody shrinks and the memory is empty again. The proof breaks in two places. Claim 4
  shows only that at every time *some* competing process does not withdraw. The proof of Theorem 2
  then concludes that some process *never* calls `shrink()`, but the non-withdrawing process may
  change over time. Also, writes based on outdated snapshots, which can destroy the registers of
  the process owning the most, are never considered. Claim 5's "w.l.o.g. all competing processes
  have the same view" has the same issue. (`theorem_2_false`)
  *Scope.* Line 6 says "write into some `x` with `view[x] = ⊥`" without fixing `x`, so Theorem 2
  must hold for every resolution. The Lean counterexample uses "first `⊥` in the process's local
  order". Since the permutations are adversarial, this covers every "first `⊥` w.r.t. a fixed order
  of local names" rule. Our model checker also finds the livelock when line 6 may pick any `⊥`.
  Rules that inspect the view's contents were not explored and might rescue the algorithm. Bounded
  exhaustive model checking found no livelock for `n = 2` (`m ∈ {3,5,7}`) or `n = 3` (`m ∈ {5,7}`),
  so Algorithm 1 may be correct for `n ≤ 3`; this is not proved.
* **Theorem 4's proof is only a sketch; statement true.** "Repeating this argument, eventually one
  of the processes will find…" ignores two things. First, Algorithm 2's views are read
  non-atomically, so a process may count registers another process held at different times.
  Second, a waiting process may re-enter after a non-atomic all-`⊥` scan while others still hold
  registers. Our new proof has three steps. (1) A no-inflation lemma: a view never shows `q` owning
  more registers than `q` owned *simultaneously* at some point of the scan. (2) Let `c*` be the
  eventual maximum number of owned registers; a process owning `c*` registers late never withdraws.
  (3) Once the memory is constant and full, all competitors own equally many registers, which
  contradicts `m ∈ M(n)`. (`theorem_4`)
* **Theorem 5's proof is confused but sound in essence.** It describes the schedule via
  "order(pᵢ, k)", but processes do not access registers in a fixed order. The real argument is a
  lock-step execution preserving a rotational symmetry. We use `g = gcd(ℓ, m)` processes and rotation
  permutations; in each round they access different physical registers. (`theorem_5`)
* **Typo.** §1.3 says `compare&swap(x, old, new)` succeeds "iff `new = v`"; it should be `old = v`.
  The algorithm uses it correctly.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory (CSLib), deterministic processes, no crashes. Processes may stay in the
  remainder (or in the CS) forever.
* The memory is `m` registers, initially `⊥`, with atomic read-modify-write accesses and atomic
  snapshots. Reads, writes and compare&swap are special cases.
* **Memory anonymity:** each process has its own adversarial permutation of register names, fixed
  for the execution.
* **Symmetry:** one program for all processes, which differ only in their identifier. "Compare
  identifiers only for equality" is formalized semantically: the algorithm commutes with every
  renaming of identifiers, and `⊥` is not an identifier.
* Deadlock-freedom follows §2.3: in every fair, client-well-formed infinite execution, if an
  operation is pending and nobody is in the CS, some operation later completes. Fair = every process
  with a pending operation eventually steps.
* Granularity: each loop iteration is one atomic access; local bookkeeping is folded into the
  preceding access. Algorithm 1 uses an atomic snapshot, as the paper assumes.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (Alg. 1 mutual exclusion; needs only `n ≤ m`) | `Alg1.theorem_1`, `Alg1.theorem_1_of_M` | `Alg1Safety.lean` |
| Theorem 2 (Alg. 1 deadlock-free): **false** | `theorem_2_false` | `Alg1Livelock.lean` |
| Theorem 3 (Alg. 2 mutual exclusion; any `m ≥ 1`) | `Alg2.theorem_3` | `Alg2Safety.lean` |
| Theorem 4 (Alg. 2 deadlock-free for `m ∈ M(n)`) | `Alg2.theorem_4` | `Alg2DF.lean` |
| Theorem 5 (lower bound `m ∈ M(n)`) | `theorem_5` | `LowerBound.lean` |
| RMW characterization (§6.2, §7) | `rmw_characterization` | `Main.lean` |
| RW necessity `m ∈ M(n) \ {1}` (§4.2) | `rw_necessity'`, `one_register_impossible` | `Main.lean`, `OneRegister.lean` |

`theorem_5` is more general than the paper's. It covers arbitrary read-modify-write *and*
snapshot accesses and any value/state types, and it needs correctness for only one identifier
assignment. So it also yields the read/write necessity result attributed to [15]. The `m = 1` case
of the read/write characterization, which the paper cites from Burns–Lynch, is proved directly,
without symmetry.

**Not formalized.** The double-collect implementation of the snapshot.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The livelock is checked by kernel computation (`decide +kernel`). Both algorithms are
proved symmetric (`Alg1.alg1_symmetric`, `Alg2.alg2_symmetric`), and Algorithm 2 is proved
deadlock-free, so the hypotheses are satisfiable. The bounded model checkers are in
[`modelcheck/`](modelcheck/) and are not part of the Lean development. Lock objects, fairness and
anonymous symmetric memory are in CSLib
(`Cslib/Computability/Distributed/SharedMemory/{Mutex,Anonymous}.lean`).
