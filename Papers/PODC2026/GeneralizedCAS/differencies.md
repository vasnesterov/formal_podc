# Differences between the formalization and the paper

Paper: Hadzilacos, Thiessen, Toueg, *Generalized Compare-and-Swap and Space-Efficient Universal
Constructions for the Infinite-Arrival Model*, PODC 2026, arXiv 2605.19237v1. Scope: Algorithm 1,
Theorems 4 and 5, Appendix B.

## Statement-level

* **Theorem 4 (Algorithm 1 is a wait-free linearizable universal construction).** Proved as stated:
  `theorem4` (`linearizable`, `waitFree`). Linearizability is CSLib's `Linearizable`, the amended
  Herlihy–Wing definition; it matches Appendix A. Wait-freedom is CSLib's `WaitFree`: in every infinite
  execution, an operation that stays pending forever takes finitely many steps. This matches
  Appendix A's definition.
* **Theorem 4 (space linear in the number of participants).** Proved with explicit constants:
  `space C ≤ 4 + |{processes appearing in α}|` (`space_bound`). The 4 static objects are `C`, `A`, `S`
  and the dummy cell; each participant allocates at most one cell. "Participated by time `t`" means
  "took a step in the execution so far", as in Section 2.1.
* **Theorem 5 (steps linear in the point contention).** Proved with explicit constants (`theorem5`).
  Let `c` be the number of pending operations when `p` executes line 3. Then every interval of the
  operation contains at most `105 c + 44` memory steps of `p`. With the invocation and the response,
  the operation has at most `105 c + 46` steps. The theorem is stated on `Trace`s, which carry ghost
  variables; `exists_trace` shows that every finite execution of `alg` is a trace. The "same operation"
  hypothesis is phrased as "`p` is pending at `a` and does not return in `[min a n3, m)`".
* No statement was found false. By rule R1, the issues below are proof-level only.

## Proof-level

* **Lemma B.2.14, inductive step (genuine gap; verdict 🛠️).** From `O_{n+1} = O_n` the proof concludes
  `o' = o_{3n+2} = o_{3n+3} = o_{3n+4}` for some `o' ∈ O_n`. This does not follow: the three operations
  may be distinct elements of `O_n`. Repair: by Proposition B.2.13, no operation is identified by four
  periods, so each operation of `S(o)` is identified by at most 3 periods; pigeonhole gives at most
  `3|S(o)|` periods.
  *Borderline:* the repair is one line. We rate it 🛠️ rather than ✅ because the written argument is
  logically invalid and a careful referee would flag it.
* **Our counting argument differs from B.2.13/B.2.14.**
  * Instead of the operation "identified" by a useful period (Definition B.2.4), we use *rises*. A rise
    of `τ` is a step after which `τ` is done and `A.time ≠ τ` (`Trace.RE`).
  * Every useful period contains a rise of its identified operation. Indeed, `o'` is stored in `A` at
    `T2`, and at `T3 > max(T1, T2)` it is done and not stored, so a rise happens in `(T2, T3]`.
  * Our `OpStart.useful` (Lemma B.2.12) directly produces a rise of an operation of `S(o)` inside the
    time window of the period.
  * Each operation rises at most 3 times (`Trace.card_RE_le`). Between two rises the operation must
    re-enter `A`. Its owner writes it into `A` at most twice while it is done (`Inv2.wd_le`, a ghost
    counter), because the next execution of line 5 sees that it is done. This is the content of the
    proof of Proposition B.2.13.
  * Periods are disjoint in time, so their rises are distinct; this gives at most `3|S(o)|` periods
    (`OpStart.periods`, `OpStart.it_le`).
* **Proof of Theorem B.2.15, arithmetic slip.** At most `3c` disjoint periods allow up to `15c + 4`
  complete non-terminal iterations after the first, not "`15|c|`". The total bound should be
  `15c + 6` iterations, not `15c + 2`. Linearity is unaffected. We prove at most `15|S(o)| + 5` complete
  iterations (`OpStart.it_le`). The step count of a pending operation is at most `9 + 7 · it`
  (`Inv2.ns`), where `it` is the number of complete iterations.
* **Lemma B.2.6 and Proposition B.2.5 for `Noop`.** "`o'` is not pending, hence complete" is used also
  when `o'` is `Noop`, which is not an operation execution. The argument still works because no
  process writes `Noop` into `A`. Our `OpStart.old_out` handles timestamp `0` separately.
* **Lemma B.2.6 and the period of Proposition B.2.8** are not stated in the paper's form. We prove
  `OpStart.A_SO`: from line 8 of a non-first iteration on, every operation in `A` with timestamp
  `≤ t(o)` is in `S(o)`, and right after line 8 the operation in `A` has timestamp `≤ t(o)`. The paper's
  B.2.8 then becomes `re_not_SO`: if `A` holds an operation outside `S(o)` after line 8, then an
  operation of `S(o)` rose in between. The paper's proof of B.2.8 contains this argument (the first
  successful line-15 GCAS after `T8`).
* **Appendix B.1 is reorganized as a state invariant.** The facts of B.1 (Observations B.1.9–B.1.15,
  Lemmas B.1.16–B.1.25) are clauses of `Inv` (`Invariant.lean`) or consequences of it (`Facts.lean`).
  Examples: "after line 7, if `S` is unchanged its operation is done" (`copied`, Lemma B.1.21); "a
  process about to succeed on line 13 does so for a pending, not yet linearized operation" (`l13`,
  Lemmas B.1.16, B.1.25, Proposition B.1.24); "the response stored with an operation is its response in
  the linearization" (Claims B.3.1.3–B.3.1.5).
* **Theorem B.3.1 (linearizability).** Same linearization (the order of the successful CAS on `S`),
  built incrementally with CSLib's `IsLinearization.push` / `append_ret_of_respIn` instead of the
  explicit completion `H'` and sequential history `S` of the paper.
* **Assumption B.1.1** (every participating process takes at least two steps) is not needed.
* **Prop B.2.13 / time conventions.** The paper's "value at time `t`" is the configuration after step
  `t`. In `Trace`, `C n` is the configuration before step `n`. All arguments are adapted accordingly.

## Modelling choices

* **Deterministic `applyT`.** The type `T` is a CSLib `ObjSpec`, with a deterministic transition
  function. The paper (Section 2.1, Appendix A) allows a nondeterministic state-transition relation.
  The proof does not use determinism, but the formalized statement covers only deterministic types.
* **Comparator of GCAS on `A`.** Triples `(time, op, ptr)` are compared lexicographically (footnote 2).
  This needs a linear order on operations (`[LinearOrder T.Op]`, e.g. bit-string encodings) and on
  pointers (`Ptr = WithBot ℕ`). `Noop` is `⊥`, and `ptrNoop` is the pointer `⊥`.
* **Memory manager.** `AllocateCell` returns the cells `0, 1, 2, …` in order, from a base object `MM`.
  Algorithm 1 never frees, so any allocation order is this one up to renaming of cells. The initial
  contents of all non-dummy cells are arbitrary (`cellInit`); the paper leaves them unspecified. The
  dummy cell holds `(0, ⊥)`.
* **`Null` and `⊥`.** Responses in cells and in `S` are `RVal R = null | bot | val r` (Assumption B.1.2).
* **Granularity.** Each access to a shared object is one step, and local computation (lines 11, 12) is
  merged into the next access. Line 2 is a step only if the process allocates (the test `ptr = Null` is
  local). Line 16 is the response step and returns the response read on line 5, instead of reading the
  cell again. These choices change step counts by constants only.
* **Line 5 fallback.** If line 5 reads a cell whose response is neither `Null` nor a response (only `⊥`
  is possible, in an uninitialized cell), the process re-executes line 5. The invariant shows that
  this never happens (`Inv.own_cell`).
* **Crashes, infinite arrival.** There is no crash event: a crashed process simply takes no more
  steps, which the asynchronous CSLib model already allows. The process type `P` is arbitrary
  (possibly infinite). Invocations are unrestricted (`allowed := True`).
* **Ghost variables** (`Ghost`). They record timestamps (`ts`), the linearization (`lin`), completed
  operations (`k`), iteration and step counters (`it`, `ns`), the "written while done" counter (`wd`),
  a clock and the times of the lines of the current iteration (`lt`). They do not influence the
  algorithm: `arun_fst` and `exists_arun` show that projecting them away gives exactly the executions
  of `alg`.
