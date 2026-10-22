# Differences between the formalization and the paper

Paper: Z. Aghazadeh, P. Woelfel, *On the Time and Space Complexity of ABA Prevention and Detection*,
PODC 2015 (arXiv 1507.02722v1, the version formalized).

## Model

1. **Deterministic implementations only.** CSLib's shared-memory model (`Cslib.SharedMemory.Impl`) has
   deterministic processes. Theorem 1(a) and Observation 1 are stated in the paper for
   *nondeterministic* implementations satisfying *nondeterministic solo-termination*. We prove them for
   deterministic ones, where that condition is obstruction-freedom (`Impl.ObstructionFree`). This
   is a **weaker result** than the paper's: the lower bound is proved for a smaller class of
   implementations, and randomized implementations are excluded. The paper's proof does not seem to
   use determinism in an essential way (schedules would carry the coin flips), but this is not
   checked: the nondeterministic generalization is **not** formalized. Theorem 1(b),(c) and Corollary 1 are about
   deterministic wait-free implementations in the paper too, so for them nothing is lost.
2. **Returning is a separate step.** In CSLib a process returns with a separate `ret` label that does
   not access memory. In the paper the last shared-memory step may also return. This only matters in
   the base case of Lemma 2 (`t = 0`): there `q` may still have to execute its `ret` step, and case (a)
   is reached by appending that step.
3. **Executions are label lists, `allowed` restricts invocations.** The paper lets "process 0 repeatedly
   call WeakWrite(), the others WeakRead()". We assume only that these invocations are *allowed*
   (`I.allowed w0 (dwrite x)`, `I.allowed p (dread p)`). The executions built in the proofs use only
   them (`Std`). The implementation may allow more (e.g. reads by the writer). Correctness
   (linearizability) is assumed for all executions.
4. **`DRead` carries the reader.** An `ObjSpec` cannot see the caller, so the ABA-detecting register
   (`abaObj`) has operations `dread p` and `dwrite x`. Implementations must enforce "`p` only invokes
   `dread p`" with `allowed`. The same holds for CSLib's `llscObj` (`ll p`, `sc p v`, `vl p`).
5. **Value type of the implemented object.** The paper states the theorems for 1-bit objects. We state
   them for any value type `W` (`W = Bool` is the paper's case). The lower bound does not depend on it.
6. **`DWrite` has a dummy response** (`(x, true)`); the paper's `DWrite` returns nothing.

## Base objects

7. **Bounded registers (Theorem 1(a), Lemma 1)** are `register (V i) (v₀ i)` with `Finite (V i)`, for
   finitely many indices `i : ι` (`Fintype ι`). Lemma 1 (`lemma1`, `card_le_of_separates`) is proved more
   generally, for any bounded base objects all of whose operations are read-only or blind overwrites.
8. **CAS objects (Theorem 1(b),(c), Lemmas 2–3, Corollary 1)** are *writable* CAS objects `wcasObj V v₀`
   over one finite value type `V` for all objects. `Read` and `CAS(x,y)` return the old value, the more
   informative of the paper's two conventions, so the bound also covers the Boolean one in spirit.
   `Write` returns nothing. Objects of different sizes are not covered directly; they can be padded to
   a common `V`, but this reduction is not formalized.
9. **Registers and non-writable CAS objects (Theorem 1(b), Corollary 1(a))** are writable CAS objects on
   which the implementation, in reachable configurations, never `CAS`es a register and never `Write`s a
   CAS object (`RegOrCas I isCas`).
10. **`CAS(x,x)`.** The paper assumes w.l.o.g. that no `CAS(x,x)` is executed ("can be replaced by a
    Read"). We do not need this assumption. A *successful* step (`SOp`) is a `Write` or a `CAS(x,y)`
    with `x ≠ y` on value `x`. In Lemma 2 a `CAS(x,x)` of `q` is treated like a read.

## Correctness condition, clean/dirty configurations, Observations 1 and 2

11. **The paper's literal `WeakRead()/WeakWrite()` condition is not implied by linearizability**, contrary
    to the sentence "Linearizability of an ABA-detecting register R guarantees that … satisfy the
    correctness properties above". There are two independent reasons, each with a concrete execution
    of the (linearizable, wait-free) atomic implementation (`WeakSpec.lean`):
    `weakSpecLiteral_not_of_linearizable_concurrent` (a read concurrent with a write may be linearized
    after it and return `True`, but no write *happens before* it) and
    `weakSpecLiteral_not_of_linearizable_later_read` ("every other WeakRead() by p" includes *later*
    reads, so the first read after a write would have to return `False`). We do not use the
    WeakRead/WeakWrite condition. The only property of the implemented object the lower bounds use
    is the abstract `Separates` (Observations 1/2: clean and dirty configurations are distinguishable),
    and we prove it directly from linearizability (`separates_aba`, `separates_llsc`). For linearizable
    ABA-detecting registers and LL/SC objects the theorems therefore hold as stated. The paper's claim
    that the lower bounds hold for the (weaker) WeakRead/WeakWrite condition is not formalized. For the
    literal condition that claim is vacuous: no implementation in which a reader can complete two
    reads after a complete write satisfies it (the first read must return `True` in the prefix
    `DWrite(); DRead()` and `False` in its extension by a second `DRead()`; informal argument, not
    formalized). The abstract theorems `card_le_of_separates`, `card_le_of_separates_wcas` and
    `card_le_of_separates_regOrCas` apply to any object and correctness condition for which
    `Separates` holds, so they cover any repaired weak condition implying Observation 1.
12. **Clean/dirty** (`Clean`, `Dirty`) are defined on executions (label lists) rather than
    configurations, relative to a designated writer `w0`, reader operations `rd p` and a writer *round*
    `ws`. That is `[DWrite(x)]` for ABA-detecting registers and `[LL(), SC(x)]` for LL/SC, as in
    Appendix B.3. "Every WeakWrite happens before r*" becomes "every operation of the writer returned
    before `r*` was invoked". The executions considered are *standard* (`Std`): the writer invokes only
    `ws` operations, the others only `rd`. Observation 1/2 is required only for standard executions
    whose final configurations have the reader idle. That is all the proofs use.
13. **Observation 2 (LL/SC)**: in the dirty execution the paper takes "a successful SC()". We take the
    writer's round `LL(); SC(x)` and derive that this `SC` succeeds from linearizability: no other
    process invokes `SC` in standard executions.

## Lemmas 1–3

14. **Lemma 1** is stated for reachable quiescent configurations reached by standard executions, with
    `(ps ∪ {w0})`-only schedules (`lemma1`). "`k` distinct registers covered by `p₁…pₖ`" is a list of
    (process, object) pairs with distinct objects. The proof is the paper's; the induction works for
    every `n` (in particular `n = 2`, with `R = ∅` and an empty block write).
15. **Lemma 2: gap in Case 1.** The proof takes "the first process `z ∈ P` that executes a step on
    `V` in `Exec(C,β)`", which need not exist. In that case: if `q`'s step is a `Read`, a failing
    `CAS` or a `CAS(x,x)`, `q` takes its step and the induction hypothesis applies; if it is a `CAS`
    that would succeed, case (c) holds directly with `σ = β`, since no process of `P` is poised on
    `V`. Proved in `lemma2`.
16. **Lemma 2: inequality slips.** The paper derives `|WCov(C′,R) ∩ P′| ≤ t′` "since `q` must finish
    within `t′` steps" and concludes `|WCov(C,R) ∩ P| ≤ t′ + 1 = t`, which does not give the claimed
    `< t`. The induction hypothesis gives `< t′`, hence `< t`.
17. **Lemma 2: implicit properties of `σ`.** The proof of Lemma 3 uses that `σ` is
    `(P ∪ {q})`-only and contains no invocations. The statement of Lemma 2 does not say so. Our
    `lemma2` states both.
18. **Lemma 2: proof structure.** The paper inducts on `t` and in Case 2 moves `z₁…z_ℓ` (the `CAS`es on
    `V` before the first write, and that write) at once. We move one process at a time and induct
    on `t + |β|`. The case split is on whether `q`'s step changes the memory. If it does not, `q`
    steps alone. If it does and no process of `β` accesses the object, case (b)/(c) holds directly.
    If the first accessor `z` writes, `q` steps and then `z`. If `z` and `q` both `CAS`, `z` steps and
    then `q`, whose `CAS` fails. If `z` `CAS`es and `q` writes, either (b) holds or `z` alone is moved
    and `t` is kept. The arguments are equivalent (`lemma2_aux`, `succ_bubble`).
19. **Lemma 3** is stated for reachable quiescent configurations reached by standard executions. (ii)
    is "some ordering of `ps` is a successful schedule" (`β.Perm ps ∧ Succ I C β`). The *signature*
    of a configuration is its memory together with the poised access of every process. The paper's
    index typos in `λ′` (`… γ_{i+1} α_{i+1} …`) and `Dⱼ′ = Conf(Dᵢ′, λ′αⱼβⱼ)` (should be `βᵢ`) are
    corrected.
20. **Step complexity.** "Worst-case step complexity at most `t`" is `StepBound I t`: in every
    execution, every (complete or pending) operation has at most `t` base-object accesses. Wait-freedom
    is assumed separately (`Impl.WaitFree`), as in the paper; the proofs only use obstruction-freedom
    plus the step bound.

## Not formalized

21. Theorem 1 for nondeterministic implementations (item 1).
22. Theorem 2 (LL/SC/VL and a multi-writer ABA-detecting register from one bounded CAS object, Figure 3),
    Theorem 3 (ABA-detecting register from `n + 1` bounded registers, Figure 4) and Appendix A
    (ABA-detecting register from LL/SC/VL). As a consequence there is no non-vacuity witness for the
    hypotheses of Theorem 1 with bounded base objects: the upper bounds that would provide one are not
    formalized.
