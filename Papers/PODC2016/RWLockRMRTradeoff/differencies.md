# Differences between the formalization and the paper

Hendler, *On the Complexity of Reader-Writer Locks*, PODC 2016 (author copy "ReadersWritersLock-CR",
Extended Abstract, 11 pp.). Numbering follows the paper.

## Model

1. **Algorithms.** A reader-writer lock for `n` readers and `m` writers is a CSLib implementation
   `RWAlg n m ι V v₀ L := Impl mutexObj (Regs ι V v₀) (Proc n m) L` of the lock object
   (`lock` = entry section, `unlock` = exit section) from registers `rwcas V v₀`, processes
   `Proc n m = Fin n ⊕ Fin m`. Processes are deterministic. Registers support read, write and CAS;
   **CAS returns the old value**, as in the paper (CSLib's `casObject` returns only a flag, which
   would cover fewer algorithms). Initial values are arbitrary (`memInit`).
2. **Steps.** CSLib labels `inv p o`, `tau p`, `ret p r`. An invocation and a response are labels
   without a memory access (in the paper the first step of the entry section is already a memory
   access). They incur no RMR and never change knowledge, so counts are unaffected.
3. **Sections.** remainder / entry / CS / exit = CSLib regions `rem` / `trying` / `cs` / `exiting`,
   computed from the history (`regionOf`). Properties are required for client well-formed
   executions (`ClientWF`), as in CSLib's mutex definitions.
4. **Extra hypothesis `∀ p o, I.allowed p o`**: every process may invoke `lock`/`unlock` (CSLib's
   `Impl` has an `allowed` field; the paper has no such notion).
5. **Mutual Exclusion** (`RWMutualExclusion`): as in the paper.
6. **Bounded Exit** (`BoundedExit`) and **Concurrent Entering** (`ConcurrentEntering`): the bound may
   depend on the execution prefix after which the exit (entry) section is running. This is weaker
   than the paper's constant bound, so our theorem is stronger. The paper's Concurrent Entering
   says "any reader that executes **at most** `b` steps … enters the CS"; we read it as "a reader
   that has taken `b` steps of its entry section (writers in the remainder section and not
   stepping) is in the CS", the evident intent (R3; typo).
7. **Deadlock Freedom**: CSLib's `Impl.DeadlockFree` (in every fair client well-formed infinite
   execution, if at time `t` some operation is pending and nobody is in the CS, some operation
   completes later). The paper's version (infinitely many passages complete in every infinite
   execution without fail-stops outside the remainder section) implies it, so this hypothesis is
   weaker than the paper's. Only its consequence `solo_returns_of_deadlockFree` is used.
8. **CC model.** The paper quotes the write-back and write-through protocols of Golab et al. We
   prove the lower bound for every `CacheModel` (three axioms: an access without a valid cached copy
   is an RMR; only the stepping process can gain a valid copy, of the variable it accesses; a step
   that changes the value of `v` invalidates the other processes' copies of `v`). `writeBack` and
   `writeThrough` are instances. Modelling choices inside the instances: in write-back every CAS
   needs an exclusive copy; in write-through every write/CAS is an RMR and leaves the writer with a
   valid copy.
9. **RMR complexity.** `WriterEntryRMR I cm Wb`: in every execution, a writer incurs at most `Wb`
   RMRs between leaving the remainder section and starting its exit section. `ReaderExitRMR I cm Rb`:
   a reader incurs at most `Rb` RMRs from the CS until it starts a new entry section. Worst-case
   bounds over all executions, as in the paper.
10. **Knowledge.** Definitions 1–2 are formalized forward along a fragment (`kstep`): a reading
    step (read or CAS) of `p` on `v` adds `F(v)` to `AW(p)`; a non-trivial write sets
    `F(v) := AW(p)`; a non-trivial CAS sets `F(v) := AW(p) ∪ F(v)`; trivial steps leave `F(v)`
    unchanged. This is the paper's backward recursive definition read forward (equal by an immediate
    induction on `E`; not formalized separately). Knowledge is reset at the beginning of a fragment
    (`Ext.fresh`). Definition 3 (`Expanding`) is verbatim. Fact 1 = `expanding_iff`,
    Observation 1 = `kstep_aw` / `xrun_aw_mono`, Observation 2 is used through `KInv.fam_sub`
    (`|F(v)| ≤ max_p |AW(p)|`).

## Statements

11. **Lemma 1 is false** (R1: a false numbered lemma; not excused: the fix changes the content of the
    claim and the paper's proof reasons with the wrong case). In the write-back model, `q` writes `1`
    to `v`, then `p` writes `1` to `v` (a trivial write, so `F(v)` stays `{q}`, but `p` gets an
    exclusive copy), then `p` reads `v`: expanding, no RMR (`lemma1_false`; same in write-through when
    a write leaves the writer with a valid copy: `lemma1_false_writeThrough`). The proof assumes that
    some `q ≠ p` writes `v` while `p` holds a valid copy, which fails when the last non-trivial write
    precedes `p`'s caching step. **Replaced by** `lemma1_count`: in every fragment
    (arbitrary cache state at its start), every process has at least as many RMRs as expanding steps.
    This is what Theorem 5 needs.
12. **Lemma 2** (`lemma2`): stated for an arbitrary set `T` of processes poised on memory accesses
    (the paper: all processes in their entry or exit section); conclusion `|AW(p)| ≤ 3B` for all
    `p` whenever `|AW(p)| ≤ B` for all `p` before. True.
13. **Lemma 3** (`lemma3`): "steps executed by other processes when they are aware of `p`" is read as
    "steps after which the stepping process is aware of `p`" (awareness *after* the step). Read
    literally (awareness before the step) the statement is false: if `p` writes `1` to `v` and `q`
    then reads `v`, the read of `q` is kept but returns `0` instead of `1` in `E'`. The paper's proof
    ("this implies that `s_q` should have been removed") uses our reading (R3, evident intent).
14. **Lemma 4** (`lemma4`): stated for any fragment `C₁ ↪ E` that starts with reader `i` in the CS and
    ends with writer `w` in the CS (the paper: the specific `E₂E₃`). The paper writes `⊂` for `⊆`.
15. **Observation 3**: `exists_E1` (Concurrent Entering) and `solo_returns_of_deadlockFree`.
16. **Theorem 5.** Exact form `theorem5`: `n ≤ Wb · 3^Rb`. Logarithmic form `theorem5_logb`:
    `log₃ (n / C) ≤ Rb` for every `C ≥ Wb`; with `C = c · f(n)` this is the paper's
    `Ω(log (n / f(n)))` with explicit constants: `Rb ≥ log₃(n / f(n)) − log₃ c`. When `n / f(n)` is
    bounded (e.g. `f(n) = n/2`) the asymptotic claim `Rb = Ω(log (n / f(n)))` would require `Rb ≥ 1`
    for large `n`, which the paper's proof does not give (the reader of the last round may not exist
    when `r = 0`); this degenerate corner is outside the interesting range (R2) and is not formalized.
    `theorem5_general`: the same for any number `m ≥ 1` of writers (one of them is used).
17. **Corollary 6** (`corollary6`): `⌊log₃ n⌋ ≤ Wb + Rb ≤ 2 · max(Wb, Rb)`.
18. **Corollary 7** is not formalized: it combines `theorem5_general` (which holds for any `m`) with
    the `Ω(log m)` mutual-exclusion lower bound of Attiya–Hendler–Woelfel, which is not formalized.

## Proofs

19. **Lemma 2, case 1** (proof gap, 🛠️): "if `v` was written to in `σ₂`, then its value after
    `Eσ₁σ₂` differs from the expected parameter of all CAS steps of `σ₃`" is false (a write may
    restore the expected value), so one CAS of `σ₃` may succeed. The bound still holds: all CAS steps
    of `σ₃` on `v` expect the value of `v` after `E`, so at most one of them succeeds, and then
    `F(v) ≤ 2M`, `AW ≤ 3M`. We prove the lemma with a greedy schedule instead (`lemma2`).
20. **Theorem 5, use of Lemma 1** (🛠️): both uses ("`W₁` performs `O(f(n))` expanding steps",
    "`R_i` executes exactly `r` expanding events … The theorem now follows from Lemma 1") go through
    with `lemma1_count`, applied to the fragments `C₁ ↪ E₂E₃` (writer) and `C₁ ↪ E₂` (reader).
21. **Theorem 5, expanding steps after reordering** (🛠️): invariant 2 says that readers are *about
    to* perform expanding steps, but Lemma 2 reorders these steps, and whether a step is expanding
    depends on what was executed before it. Not argued in the paper; true because all poised steps
    are reading steps (read/CAS), during which familiarity sets only grow (`round_expanding`).
22. **Theorem 5, the steps `σ''`** (🛠️): "let all the readers of `R_j` take steps until they either
    return to the remainder section or are about to perform another expanding step" — a
    non-expanding write of one reader can change whether another reader's poised step is expanding.
    `e2_construct` repeats single non-expanding steps until all readers are simultaneously poised on
    expanding steps or done (terminating by Bounded Exit).
23. **Theorem 5, Equation (9) ⇒ `|AW(W₁)| < n`** (routine): during `E₃` the writer's own writes change
    familiarity sets; each expanding step of the writer adds at most `3^r` processes
    (`aw_solo_bound`). The cap of `log₃(n/f(n))` iterations is not needed: the construction runs
    until all readers are back in the remainder section, and the count gives `n ≤ Wb · 3^r` with
    `r ≤ Rb`.
24. **Lemma 4 proof**: as in the paper, via Lemma 3; ClientWF of the erased execution needs that the
    kept steps of every process form a prefix of its steps (`eraseFrom_filter_prefix`).

## Algorithm `A_f` (Sections 4–5)

25. **Model** (`Alg/Model.lean`): a concrete interleaving transition system following the pseudo-code
    line by line (one shared-memory access per step; line 51 is two steps). Counters `C[i]`, `W[i]`
    are atomic objects with `add`/`read`, as the paper assumes (the `f`-array implementation and its
    `O(log K)` cost are cited, not modelled). One writer: the writers' lock `WL` is omitted and
    `WSEQ` is writer-local. Readers are partitioned by an arbitrary function `grp : Fin n → Fin G`.
    Line 30 writes `⌊p/f(n)⌋`, intended `⌊p/K⌋` (typo; covered by arbitrary `grp`).
26. **Line 51 order** (❌, decides the verdict): the literal left-to-right evaluation of
    `C[i].read() = W[i].read()` violates Mutual Exclusion (`mutex_violation_literal_order`,
    `not_mutualExclusion_literal_order`; 3 readers, one group). Not excused by R3: the paper never
    fixes the order, and the proof of Lemma 8 reasons as if both counters were read atomically. With
    `W[i]` read first Mutual Exclusion holds (`mutualExclusion_repaired`, all `n`, all groupings,
    unbounded sequence numbers). Lemma 8, Lemma 9 and the Mutual Exclusion part of Theorem 18 are
    false as written (R1).
27. **Line 47** (⚠️, R3): `else if op = WAIT` should be `op' = WAIT`. As written, Deadlock Freedom
    fails (`deadlock_literal_line47`, `deadlock_literal_line47_noCS`; one reader) and Mutual Exclusion
    fails (`mutex_violation_literal_line47`; one reader, two writer passages), for either order in
    line 51. Intent recoverable: the branch passes `seq'` (line 41) and the other branch tests `op'`.
28. **Verdict, borderline call (❌ vs 🚨).** The abstract presents "a family of reader-writer lock
    algorithms that establishes that the tradeoff is asymptotically tight". We read this as an
    existential headline (the tradeoff is tight), with the family as its witness: the family as
    written is wrong, a two-line repair makes Mutual Exclusion provable, but its liveness and RMR
    bounds are not established here. By R5 an unestablished (not refuted) headline is ❌. If one
    reads the headline as "Algorithm `A_f` is a correct reader-writer lock with these RMR bounds",
    it would be 🚨. Independent review concurs with ❌: Section 4 ("we show that the complexity
    tradeoff … is tight. We do so by presenting a family `A_f`") uses the family as the witness of an
    existential claim; the repair is a swap of two reads plus the `op'` typo and leaves Lemma 17's RMR
    count unchanged (same calibration as `NonEquivocationLimits`, PODC 2012). The verdict is ❌
    independently of this call, by Lemma 1 (item 11).
29. **Lemma 10** (Bounded Exit): proved for every variant (`boundedExit_reader`: from the CS a reader
    reaches the remainder section within 5 own steps; `boundedExit_writer`: within 2). The paper's
    proof refers to the "Bounded Waiting" of `WL`; irrelevant with one writer.
30. **Lemma 11** (repaired algorithm): `lemma11_repaired`.
31. **Not formalized:** Lemmas 12–16 (Concurrent Entering, Deadlock Freedom, no reader starvation),
    Lemma 17 (RMR bounds), Observation 4 / multiple writers. Bounded explicit-state model checking
    (`af.py`, `n ≤ 3`, one group, ≤ 2 passages each) of the repaired algorithm found no state in which
    all non-remainder processes are stuck.
32. **Slips in Section 5 proofs:** Lemma 8 writes `t' < t` where the order is the other way round;
    Lemma 13's discussion says "read 0 from `W[i]`", meaning `C[i]`.
33. **RMR model remark (Lemma 17, not formalized):** the claim that the writer incurs one RMR per
    await in lines 14/21 assumes that failed CAS steps of readers on `WSIG[i]` do not invalidate
    the writer's cached copy; in protocols where every CAS takes the line exclusively, stale
    `HelpWCS`/line-45 CAS steps may cost the writer extra RMRs (not analysed).

## Non-vacuity

34. `toyLock_spec` (`NonVacuity.lean`): for every `n`, a simple single-writer lock (reader flags and
    a writer flag; readers back off while the writer flag is set) satisfies all non-RMR hypotheses of
    Theorem 5 (`allowed`, `RWMutualExclusion`, `BoundedExit`, `ConcurrentEntering`,
    `Impl.DeadlockFree`). Its RMR bounds are not analysed.
