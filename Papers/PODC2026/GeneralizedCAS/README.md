# Generalized CAS and a space-efficient universal construction — PODC 2026

Vassos Hadzilacos, Myles Thiessen, Sam Toueg. *Generalized Compare-and-Swap and Space-Efficient Universal
Constructions for the Infinite-Arrival Model.* PODC 2026. DOI
[10.1145/3796701.3815968](https://doi.org/10.1145/3796701.3815968). Formalized version: arXiv
[2605.19237](https://arxiv.org/abs/2605.19237) v1 (full version with appendices); numbering follows it.

**Verdict: 🛠️ Proof repaired.** Theorems 4 and 5 for Algorithm 1 hold. Algorithm 1 is a linearizable,
wait-free universal construction for any (possibly infinite) set of processes. Its space is at most 4
plus the number of processes that have participated. An operation takes `O(c)` steps, where `c` is the
point contention when it obtains its timestamp. One step of the counting argument (the induction in
Lemma B.2.14) is a non sequitur; a pigeonhole argument repairs it. Algorithm 2 (Theorem 6) is not
formalized.

## Mistakes in the paper

* **Lemma B.2.14: the inductive step does not follow (proof gap; the statement is true).**
  * The lemma bounds the number of non-initial periods of an operation `o` by `3|S(o)|`.
  * The proof shows `|{o₁,…,o_{3n+1}}| ≥ n+1` by induction, where `oᵢ` is the operation identified by
    the `i`-th period. In the inductive step it assumes the set did not grow, so `o_{3n+2}`,
    `o_{3n+3}`, `o_{3n+4}` all lie in `O_n`. It then concludes "`o' = o_{3n+2} = o_{3n+3} = o_{3n+4}`
    for some `o' ∈ O_n`" and applies Proposition B.2.13 to four periods identifying one operation.
  * This is a non sequitur: the three new operations can be three different elements of `O_n`.
  * Repair: Proposition B.2.13 says that no operation is identified by four periods. So each operation
    of `S(o)` is identified by at most three periods, and pigeonhole gives at most `3|S(o)|` periods.
  * In Lean we count differently. A *rise* of an operation `τ` is a step after which `τ` is done and not
    in `A`. Every operation rises at most 3 times, because its owner writes it into `A` at most twice
    after it is done (`Trace.card_RE_le`). Every non-initial period contains a rise of an operation of
    `S(o)`, and disjoint periods give distinct rises (`OpStart.useful`, `OpStart.it_le`).
* **Minor slips.**
  * Proof of Theorem B.2.15: at most `3c` disjoint periods allow up to `15c + 4` complete non-terminal
    iterations after the first, not `15c`. The total is then `15c + 6` iterations, not `15c + 2`.
    Linearity is unaffected. We prove that an operation completes at most `15|S(o)| + 5` iterations and
    takes at most `105c + 44` memory steps.
  * Lemma B.2.6 uses Proposition B.2.5 ("not pending ⇒ complete") also for `Noop`, which is not an
    operation execution. The case is easy: no process ever writes `Noop` into `A`. We treat it
    separately (`OpStart.old_out`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory (CSLib `Impl`, `Cslib.SharedMemory`). The processes form an arbitrary
  type `P`, possibly infinite: this is the infinite-arrival model with unbounded concurrency. The
  adversary chooses the schedule. A crash is a process that stops taking steps. There is no
  randomness.
* Base objects. `C` is a fetch&increment object, initially 1. `A` is a GCAS object
  (`Podc/.../Objects/GCAS.lean`) on triples `(time, op, ptr)`, compared lexicographically as in
  footnote 2; this needs a linear order on operations. `S` is a CAS object. The dummy cell holds
  `(0, ⊥)`. Further cells are CAS objects with arbitrary initial contents, handed out by a memory
  manager in the order `0, 1, 2, …`. Since Algorithm 1 never frees cells, every allocation order has
  this form up to renaming.
* The target type `T` is a deterministic sequential specification (CSLib `ObjSpec`). The paper allows
  a nondeterministic `applyT`; the proof is the same.
* Each line that accesses a shared object is one step, and local computation is merged into steps.
  Line 2 is a step only when the process allocates. Line 16 returns the response read on line 5.
* Correctness notions are CSLib's `Linearizable` and `WaitFree`. The point contention is the number of
  processes with a pending operation. The space is the number of static objects (`C`, `A`, `S`, the
  dummy cell) plus the number of allocated cells.
* Proof method. Linearizability is a state invariant (`Invariant.lean`, about 30 clauses) over the
  algorithm augmented with ghost variables (`Ghost.lean`). The linearization is the order of the
  successful CAS operations on `S`, as in the paper. The step bound follows the time-based arguments of
  Appendix B.2 on `Trace`s. A trace is an execution indexed by time, with ghost records of when each
  line of the current iteration was executed. `exists_trace` turns any finite execution into a trace.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4 (linearizable, wait-free; space ≤ 4 + #participants) | `theorem4` | `Main.lean` |
| Theorem B.3.1 (linearizability) | `linearizable` | `Linearizable.lean` |
| Theorem 4, wait-freedom | `waitFree` | `Main.lean` |
| Theorem 4, space complexity | `space_bound` | `Main.lean` |
| Theorem 5 = B.2.15 (≤ `105c + 44` memory steps) | `theorem5`, `step_bound` | `Main.lean` |
| `|S(o)| ≤ c` | `OpStart.card_SO_le` | `Main.lean` |
| Lemma B.2.14 (≤ `15|S(o)| + 5` complete iterations) | `OpStart.it_le` | `Counting.lean` |
| Proposition B.2.13 (each operation rises ≤ 3 times) | `Trace.card_RE_le` | `Counting.lean` |
| Lemma B.2.12 (non-initial periods are useful) | `OpStart.useful` | `Periods.lean` |
| Propositions B.2.8–B.2.11 | `OpStart.re_not_SO`, `OpStart.useful_l15`, `OpStart.useful_succ`, `OpStart.useful_fail` | `Periods.lean` |
| Lemmas B.2.6, B.2.7 | `OpStart.A_SO` | `Periods.lean` |
| Observation B.1.8, Lemmas B.1.19, B.1.21, B.1.22, B.1.25 | `Trace.done_mono`, `done_of_completed`, `Trace.done_after_l7`, `Trace.done_of_S_change`, `Trace.S_ne_of_change` | `Trace.lean`, `Facts.lean` |

**Not formalized.** Algorithm 2 (Section 4, Theorem 6, Appendix C: bounded concurrency and memory
recycling). The claim that GCAS is cheap in hardware is not mathematical.

**Trust.** No `sorry`. `theorem4`, `theorem5` and `linearizable` use only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The theorems are unconditional: there are no hypotheses on `T`,
on `P` or on the initial cell contents, apart from the linear order on operations. The model is CSLib's
asynchronous shared-memory framework (`Model`, `History`, `LinPoints`).

**CSLib candidates.** The GCAS object `gcasObject` (`Podc/Computability/Distributed/SharedMemory/Objects/GCAS.lean`).
The general counting lemmas `card_rise_le` (`Counting.lean`) and `eventually_not_of_count`
(`Main.lean`).
