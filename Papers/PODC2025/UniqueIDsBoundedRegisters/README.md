# Unique Identifiers from Bounded Registers — PODC 2025

Michael Anoprenko, Petr Kuznetsov, Vitaly Aksenov. *Brief Announcement: Optimal Construction of
Unique Identifiers from Bounded Registers.* PODC 2025. DOI
[10.1145/3732772.3733539](https://doi.org/10.1145/3732772.3733539). Formalized version: the
4-page brief announcement (no arXiv or full version found).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All claims hold.
* Algorithms 1 and 2 generate `(k−1)·2^w` distinct identifiers from `k` `w`-bit read/write/FAI
  registers.
* No anonymous obstruction-free implementation supports more than `k·2^w + k + 1` calls.

The lower-bound argument is sound. To reach the stated count, poised writes must also respect the
bound of `2^w` poised processes per register, and Claim 1 misses one case.

## Mistakes in the paper

* **Under-specified definition of "poised" (§4) — the final count needs a fix.** Condition (1)
  for FAIs says "fewer than `2^w` processes poised on `Rᵢ`". Condition (2) for `write(x)` only
  forbids a second poised `write(x)`. Under this literal definition the proof's case split is
  exactly the negation of "poised", and Claim 1 works with `≥ 2^w` poised processes, so the
  argument goes through. But a register can then collect up to `2^w` FAIs plus `2^w` distinct
  writes, and the final count "at most `2^w` processes poised on every register" fails: the
  argument yields only `k·2^{w+1} + k + 1`. Adding "fewer than `2^w` processes are poised" to
  condition (2) as well gives the stated bound `k·2^w + k + 1` (`theorem_4_1`).
* **Claim 1: proof gap, statement true.** The pigeonhole step ("one of `x, x−1, …, x−f` is a poised
  write value") fails when all `2^w` poised primitives are FAIs, because then no write is poised.
  The register can still be set to any `x` with fewer than `2^w` of those FAIs (`claim1` covers
  both cases).
* **Imprecise use of "wait-free" for Algorithm 2.** The paper says the algorithm "remains
  wait-free since the object produces a finite number of distinct identifiers". This argument
  already relies on a bounded number of calls, which is the regime where correctness is claimed.
  It is not standard wait-freedom: with unboundedly many calls, a process can starve in the
  `repeat` loop. We prove wait-freedom for every bound on the number of invocations
  (`alg_waitFreeUpTo`). Algorithm 1 is wait-free unconditionally (`alg1_waitFree`).
* **Small slip.** §3, first variation: "since `k' ≥ k/2`, `B ≥ k/2·2^w`" with `B = (k'−1)·2^w`
  does not follow as written. It is true since `k' − 1 ≥ k/2` (`variation_bound`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory (CSLib `Cslib.SharedMemory`), deterministic processes, no crashes.
* `k` registers with values in `Fin m`, with atomic `read`, `write v` and cyclic `FAI`, which
  returns the old value (`bReg m`). Here `m = 2^w`. All results are proved for general `m`.
* The object is `uidObj` with the long-lived operation `get()` returning `ℕ`. Correctness
  (`UniqueResp`): distinct completed operations return distinct values. For this specification
  this is equivalent to linearizability.
* "Correct for `B` calls" (`CorrectUpTo I B`): every execution with at most `B` invocations
  satisfies `UniqueResp`.
* Anonymity (`Anonymous I`): the same automaton and the same initial state for all processes. It
  is necessary: without it, `p` can return `⟪p, c⟫` using no shared memory (`nonAnonymous_correct`).
* Progress: CSLib `ObstructionFree` for the lower bound and `WaitFree` for Algorithm 1.
  `WaitFreeUpTo I N` for Algorithm 2: wait-freedom in infinite executions with at most `N`
  invocations.
* The lower bound uses `k·m + k + 2` processes (`e : Fin (k*m+k+2) ↪ P`), each calling `get()`
  once. The algorithms work for any set of processes, each calling `get()` any number of times.
* Algorithms 1 and 2 are one algorithm `alg n d m`:
  `repeat i ← R₀.FAI() mod d until i < n; j ← R_{i+1}.FAI(); return i·m + j`.
  Algorithm 1 is `d = n = 2^x`. Algorithm 2 is `d = 2^⌈log₂ n⌉`. In general `n ≤ d`, `d ∣ m`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3.1 (Alg. 1: wait-free, `(k−1)·2^w` distinct ids) | `theorem_3_1` (`alg_correct`, `alg1_waitFree`) | `Main.lean`, `AlgCorrect.lean` |
| Algorithm 2 (`2 ≤ k ≤ 2^w + 1`) | `algorithm_2` (`alg_correct`, `alg_waitFreeUpTo`) | `Main.lean`, `AlgWaitFree.lean` |
| ids lie in `[0, (k−1)·2^w)` | `alg_resp_lt` | `AlgCorrect.lean` |
| (Alg. 1 fails at `(k−1)·2^w + 1` calls) | `theorem_3_1_tight` (`alg_not_correctUpTo_succ`) | `Main.lean`, `AlgTight.lean` |
| Theorem 4.1 (≤ `k·2^w + k + 1` calls) | `theorem_4_1_bits`, `theorem_4_1`, `lower_bound` | `Main.lean`, `LowerBound.lean` |
| Claim 1 | `claim1`, `restore_many` | `Restore.lean` |
| optimality `(k−1)·2^w ≤ B* ≤ k·2^w + k + 1` | `optimal` | `Main.lean` |
| first variation `B ≥ k/2·2^w` | `variation_bound` | `Main.lean` |
| (anonymity is needed) | `nonAnonymous_correct` | `NonAnonymous.lean` |

**Not formalized.** The recursive construction for `k > 2^w + 1` (the paper defers its proof to
future work), and the starvation example for Algorithm 2 with unboundedly many calls.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: Algorithm 1 is anonymous, allows `get()` for every process and is
wait-free, so it satisfies all hypotheses of the lower bound (`optimal`). The model comes from the
CSLib modules `Cslib.Computability.Distributed.SharedMemory.{Model,Progress,Covering}`.
The correctness proof of the algorithm uses a ghost state (`AlgInv.lean`): global `R₀`/`Rᵢ` FAI
counters and, for each successful `R₀` ticket, the invocation that took it. It needs no
finiteness assumption on the set of processes.
Shared library (`Podc/SharedMemory/`): `WaitFreeUpTo` is `Impl.WaitFreeOn` (`Progress`); the
wait-freedom proofs use `Impl.waitFreeOn_of_runPotential` (a potential depending on the ghost state
of the execution) and `Impl.waitFree_of_potential` (`Potential`); poised processes and their joint
step are `Impl.PoisedAt` and `Impl.runFrom_poised_block` (`Covering`); `respOf_append_of_not_ret`
(`History`).
CSLib candidate: `Mirror.lean` (replaying a run by another process under anonymity).
