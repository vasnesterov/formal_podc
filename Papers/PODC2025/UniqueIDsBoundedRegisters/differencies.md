# Differences between the formalization and the paper

Paper: Anoprenko, Kuznetsov, Aksenov. *Brief Announcement: Optimal Construction of Unique
Identifiers from Bounded Registers.* PODC 2025 (4-page brief announcement; no full version found).

## Errors and imprecisions in the paper

1. **Definition of "poised" (§4), condition (2) — under-specified definition; only the final
   count is affected.** Condition (2) says a process about to `write(x)` on `Rᵢ` becomes poised if
   no other poised process is about to `write(x)` on `Rᵢ`. Unlike condition (1), it has no bound
   "fewer than `2^w` processes are poised on `Rᵢ`". Under the literal definition the proof's case
   split ("either (1) at least `2^w` poised, or (2) a poised `write(x)`") is exactly the negation
   of "poised", and Claim 1 works with `≥ 2^w` poised processes, so the argument is sound. However,
   up to `2^w` FAIs and `2^w` distinct writes, i.e. up to `2^{w+1}` processes, can be poised on one
   register. The final count "at most `2^w` processes poised on every register" then fails, and the
   argument only gives `k·2^{w+1} + k + 1`. We add the bound to condition (2) (`Poisable`): an
   update is poised iff fewer than `m` processes are poised on the register and, for a write, its
   value is not already poised there. This gives the stated `k·2^w + k + 1`.

2. **Claim 1, proof gap (statement true).** The proof says that at least one of the `f + 1` values
   `x, x−1, …, x−f` is among the `2^w − f` poised write values. This fails when all `2^w` poised
   primitives are FAIs (`f = 2^w`): then there are no writes at all. The claim still holds:
   `(x − current) mod 2^w < 2^w` poised FAIs reach `x`. `claim1` proves both cases. When some
   write is poised (`f < m`), the pigeonhole needs `f + 1 ≤ m` distinct values, which is the case.

3. **Algorithm 2: imprecise use of "wait-free".** The paper says the algorithm "remains wait-free
   since the object produces a finite number of distinct identifiers". This justification already
   relies on a bounded number of calls, which is the regime where the algorithm is claimed
   correct. It is not wait-freedom in the standard sense: with unboundedly many calls a process can
   starve forever in the `repeat` loop. Example: `k = 4`, `w = 2`, `d = 4`. Process `p` always
   draws `R₀`-values `≡ 3 (mod 4)`, and another process takes the values `0, 1, 2` between its
   draws, in repeated calls. We did not formalize this example. We prove `alg_waitFreeUpTo`:
   wait-freedom in every infinite execution with at most `N` invocations, for every `N`.
   Algorithm 1 (`d = k − 1`) is wait-free unconditionally (`alg1_waitFree`).

4. **First variation of Algorithm 1 (§3) — slip in the inequality, conclusion true.** "Since
   `k' ≥ k/2`, we get `B ≥ k/2 · 2^w`": here `B = (k'−1)·2^w`, so `k' ≥ k/2` does not suffice. The
   conclusion holds because `k' − 1` is the largest power of two `≤ k − 1`, hence
   `2(k' − 1) ≥ k` (`variation_bound`).

5. **"Sufficiently many concurrent processes" (Thm 4.1) — made explicit.** `k·2^w + k + 2`
   processes suffice. Each invokes `get()` at most once.

## Modelling choices (not errors)

* **Registers** have values in `Fin m`, with `m = 2^w` for `w`-bit registers. All results are
  proved for arbitrary `m ≥ 1` (lower bound) and for any `n ≤ d`, `d ∣ m` (algorithms).
  `FAI` returns the old value and increments modulo `m`. `write v` returns `v`, a dummy response
  that carries no information.
* **The specification** "all outputs are distinct" is nondeterministic, so it is not expressed by
  CSLib's deterministic `ObjSpec`. `uidObj` has a dummy transition function. Correctness is
  `UniqueResp`: distinct *completed* operations return distinct values. For this specification it
  is equivalent to linearizability, because every order of operations with distinct outputs is a
  legal sequential history. "Correct for `B` calls" (`CorrectUpTo I B`) quantifies over all
  executions with at most `B` invocations (`numInv`).
* **Anonymity** (`Anonymous`) is semantic: `locInit`, `invoke` and `act` do not depend on the
  process. It is necessary for the lower bound. Without it, `p` can return `⟪p, c⟫` using no
  shared memory at all (`nonAnonymous_correct`, `NonAnonymous.lean`).
* **Progress**: CSLib's `ObstructionFree` (lower bound) and `WaitFree`. `WaitFreeUpTo I N` is
  wait-freedom restricted to infinite executions with at most `N` invocations.
* **Algorithms 1 and 2** are one parametric algorithm `alg n d m`, with `n = k − 1` counter
  registers and modulus `d`. Algorithm 1 is `d = n = 2^x`; Algorithm 2 is `d = 2^⌈log₂ n⌉`
  (`2^(Nat.clog 2 n)`). The trivial case `k = 1` (FAI on one register) is not formalized.
* **Number of processes in the upper bound**: arbitrary (any type `P`, possibly infinite). Each
  process may call `get()` any number of times.
* **Degenerate parameter.** The general algorithm with `n = 0` counter registers is not
  wait-free (`alg_zero_not_waitFree`), so `alg1_waitFree` assumes `1 ≤ n`. This does not affect
  the paper, where `k − 1 = 2^x ≥ 1`.
* **Bookkeeping in the lower-bound proof.** The paper calls a returned process *special* if it
  performed the first update on some register. We instead keep a set `U` of registers that the
  poised processes can restore to their *current* value (`Restorable`). A returned process that
  changes the value of some register outside `U` adds it to `U` (at most `k` times). Otherwise
  the poised processes restore the memory to its state before the process started. This is the
  paper's argument with the invariant made explicit. The paper's "last update before `p_j` set
  `Rᵢ` to `x`, and `p_k` was not poised" step is exactly the preservation of `Restorable` by a
  non-poised update.
* **Not formalized**: the recursive construction for `k > 2^w + 1` (`(k−3)·2^w` ids). The paper
  explicitly leaves its proof to future work.
