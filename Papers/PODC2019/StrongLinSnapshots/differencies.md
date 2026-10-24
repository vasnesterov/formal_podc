# Differences between the formalization and the paper

Ovens, Woelfel. *Strongly Linearizable Implementations of Snapshots and Other Types.* PODC 2019,
arXiv:1908.10826v1 (numbering follows it).

## Errors and imprecisions in the paper

1. **Specification of the first `DRead` (Section 3, definition of the ABA-detecting register).** The paper
   says `DRead_q()` returns `a = true` iff "`q` performed an earlier `DRead_q()` operation, and a `DWrite`
   was performed since `q`'s last `DRead_q()`". So a process's first `DRead` must return `false`.
   Algorithms 1 and 2 return `true` for a first `DRead` that follows any `DWrite`: `A[q] = ⊥` differs
   from the tag read from `X`. Under the literal specification, Algorithm 2 is not even linearizable.
   The sequential execution `DWrite_p(x); DRead_p() → (x, true)` is a counterexample for every `n ≥ 1`
   and every `pick` (`FirstRead.lean`, `not_linearizable_literal`). We use the specification in which the
   flag reports a `DWrite` since the last `DRead_q()` *or since the beginning*: `abaObj` of the PODC'15
   ABADetection formalization, whose flags start `false` and are set by every `DWrite`. Lemma 8 only
   compares two consecutive `DRead`s, so the paper's proof never covers the first one. Algorithm 3 is
   unaffected: it uses only flags of `DRead`s that follow a `DRead` of the same `SLscan`.
2. **Observation 6(b) is mistyped.** It says "`A[p] = s` throughout `[t, t']`". The intended (and used)
   statement is "`A[q] = (p, s)` throughout `[t, t']` for some `q`". The paper only cites it from
   Aghazadeh's thesis. We prove it as a state invariant (`ProtBy`, `protBy_getSeq`, `protBy_of_wInv`).
3. Small slips: Lemma 8's proof says "loop-guard on line 53" (twice; line 41 is meant). The proof of
   Theorem 12 cites "Theorem 11" (Lemma 11 is meant). Lemma 11's case (ii) "follows from Q-2" (Q-1 is
   meant). Observation 6(a) says "at least `n`" `GetSeq` calls, while the queue gives `n + 1`.

## Modelling choices and differences

### Theorem 1 (Algorithm 2)

* **Model.** CSLib asynchronous shared memory (`Cslib.SharedMemory.Impl`) with `n` processes `Fin n`.
  Processes are deterministic and base objects atomic registers. The response is a separate step after
  the last shared-memory access.
* **Values.** `D` is an arbitrary type `V` with a distinguished initial value `v₀` (the paper's `⊥ ∈ D`).
  `X` holds `(x, tag)` with `tag : Option (Fin n × Fin (2n+2))` (`none` = `(⊥, ⊥)`). Every register has
  this type; `A[q]` uses only the tag. So there are `n + 1` registers with
  `|V| · (n(2n+2) + 1)` values each, i.e. `O(log n + log |D|)` bits, as claimed.
* **`GetSeq`.** `na` is a function `Fin n → Option Seq` (at most one entry per index, as the paper's
  update rule implies). `usedQ` is the list of the last ≤ `n + 1` chosen numbers, newest first: the
  paper's initial `⊥` entries are dropped, which changes nothing. The "arbitrary" choice of line 11 is
  a parameter `pick` with the specification `PickSpec` (it avoids a list of `< 2n + 2` excluded values).
  All results hold for every such `pick`; `theorem1` instantiates `pickMin`.
* **`DRead` operation.** It carries the reader (`dread q`), and `Impl.allowed` lets only `q` invoke
  `dread q`, because CSLib objects do not see the caller. `DWrite` may be invoked by every process
  (multi-writer, as in the paper). The dummy response of `DWrite` is `(x, true)`.
* **Specification.** We use the corrected one (item 1 above).
* **Proof method.** The paper defines `pt` and argues about times (Lemmas 7–11). We prove a forward
  simulation (`ABASim.lean`, `linSim`) whose linearization points are exactly Q-1/Q-2. Strong
  linearizability then follows from CSLib's `stronglyLinearizable_of_linSim`. Lemma 7, Lemma 8,
  Observation 6(b) and Lemma 9 become invariant components (`RInv`, `WInv`, `ProtBy`).
* **Lock-freedom (Theorem 14).** Proved by a potential that decreases at every non-response step
  (`ABALockFree.lean`); this also implies Lemma 13 morally, but Lemma 13 is not stated separately. The
  quantitative bounds of Theorem 14 (2 steps per `DWrite`, `O(min(r,n)·w + r)` steps for `DRead`s,
  amortized `O(n)`) are not formalized; that a `DWrite` performs exactly two accesses is immediate from
  the code.

### Observation 4 (Algorithm 1)

* Proved for one concrete instance: `n = 2`, `V = Bool`, `v₀ = false`, `pick = pickMin`, reader `0`,
  writer `1`, value `true` (`Alg1.lean`). The paper argues for every `n` and every choice rule, by
  pigeonhole on the sequence numbers. One instance suffices to refute "Algorithm 1 is strongly
  linearizable" as a statement about the algorithm. The executions are the paper's `S`, `T1`, `T2` with
  `dw_i = dw1`, `dw_{i+1} = dw2`, `dw_j = dw5`.

### Theorem 2 / Theorem 25 (Algorithm 3)

* **`S` and `R` are atomic base objects** (`snapObj n` and `abaObj` over vectors). This is the main
  restriction. The paper's point is that `S` may be any *linearizable* (not strongly linearizable)
  snapshot, which yields bounded space, and that `R` can be replaced by Algorithm 2 by composability.
  * The linearization function R-1/R-2 does not depend on where `S`'s operations take effect: it uses
    only the high-level events, the `R` steps and the values returned by `S.scan`. The invariant proof
    for a fixed execution only needs *some* linearization of `S`'s history, as in the paper. So we
    expect the atomic-`S` proof to carry over to a linearizable `S`: a linearizable `S`'s history can be
    replayed with atomic accesses at its linearization points without changing `f`. This reduction is
    **not formalized**. CSLib has no composition theorem for implementations, so neither the
    substitution of a linearizable `S` nor that of Algorithm 2 for `R` is formalized.
  * Consequently Theorem 2's space bound (via Attiya–Rachman's bounded snapshot) is not formalized.
* **Values.** The implemented object is CSLib's `snapObj n` over `ℕ` with `0 = ⊥`. `update_p(x)` is
  allowed only on component `p` and only for `x ≠ 0`, as in the paper's definition. Updates return the
  dummy zero vector.
* **Interpreted values.** With atomic `S`, the interpreted value (Section 4.2, Observations 15–16) is
  the actual value. Lemmas 17–22 are replaced by a forward simulation (`SnapSim.lean`). Its invariant
  `good` says that while no `R.DWrite` happened since line 47 and the scanner's `s₁ = ℓ`, every entry of
  `S` and of the abstract state agrees with `ℓ`, except for processes with a pending unlinearized
  `SLupdate(ℓ[p])`. It replaces the time-based Lemmas 19–22.
* **Linearization order inside one step.** Updates are linearized at a scan's point in process-id order,
  before the scan (U-2/U-3), via `helpers`.
* **Lock-freedom** of Algorithm 3 (atomic `S`, `R`) is proved directly by a lexicographic potential
  (`SnapLockFree.lean`, `Snap.lockFree`), not via the paper's amortized bound. The bound `O(s + n³u)`
  (Lemmas 26–31, Algorithm 4 with sequence numbers) is not formalized. "Lock-free provided `S` and `R` are"
  (composition with lock-free implementations) is not formalized.

### Theorem 3 (Section 5)

* Not formalized: simple types, Aspnes–Herlihy's construction (Algorithm 5), linearization graphs
  (Lemmas 41–53).
