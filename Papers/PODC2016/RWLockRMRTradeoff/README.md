# On the Complexity of Reader-Writer Locks — PODC 2016

Danny Hendler. *On the Complexity of Reader-Writer Locks.* PODC 2016. DOI
[10.1145/2933057.2933099](https://doi.org/10.1145/2933057.2933099). Formalized version: the author's
copy "ReadersWritersLock-CR" (Extended Abstract, 11 pp., with the proofs of Sections 3 and 5; no arXiv
version); numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The lower bound holds: Theorem 5 (`n ≤ Wb · 3^Rb`, i.e. writer entry `O(f(n))` forces reader exit
`Ω(log(n/f(n)))`) and Corollary 6 are proved, after repairing its proof, because **Lemma 1 is false**
(an expanding step need not be an RMR in the write-back model). The matching algorithm family `A_f`
is **incorrect as written**: with the two counter reads of line 51 done in the written order a writer
and a reader can be in the CS together, and line 47 (`op` for `op'`) breaks both Mutual Exclusion and
Deadlock Freedom. With both lines repaired we prove Mutual Exclusion; liveness and the RMR upper
bounds, hence the tightness of the tradeoff, are not established here.

## Mistakes in the paper

### ❌ Lemma 1 (every expanding step is an RMR)
False in the write-back CC model with the paper's Definition 1: `q` writes `1` to `v`, then `p` writes `1` to `v` (a trivial write, so `F(v)` stays `{q}`, but `p` now holds `v` exclusively), then `p` reads `v` — an expanding step without RMR (`lemma1_false`).

**Impact.** Lemma 1 is used twice in the proof of Theorem 5, which survives: the counting version
"every process performs at least as many RMRs as expanding steps in any fragment" is true
(`lemma1_count`) and suffices.

**Details.** Definition 1 lets the familiarity set of `v` be determined by the last *non-trivial*
step on `v`, so the trivial write of `p` does not make `F(v)` part of `p`'s knowledge, yet it gives
`p` a valid cached copy. The proof of Lemma 1 argues that, since `p`'s copy stayed valid since its
last caching step, "there must be a process `q ≠ p` that writes to `v`" in between; here the last
non-trivial write precedes `p`'s caching step. The same counterexample works in the write-through
protocol if a write leaves the writer with a valid copy (`lemma1_false_writeThrough`).

**Repair.** `lemma1_count`: charge each expanding step of `p` without RMR to the earlier RMR of `p`
that created its valid copy. Potential: the number of variables of which `p` holds a valid copy
without knowing their familiarity set; it starts at `0` in every fragment and is increased only by
RMRs of `p`.

### ❌ Lemmas 8–9, Theorem 18 (Mutual Exclusion of `A_f`, line 51)
With `HelpWCS` reading `C[i]` before `W[i]` (line 51, `if C[i].read() = W[i].read()` read left to right), three readers of one group and the writer reach a configuration where the writer and a reader are both in the CS (`mutex_violation_literal_order`).

**Impact.** The algorithms as written do not satisfy Mutual Exclusion, so the tightness half of the
abstract is not established by the paper (nor refuted: the repair leaves the RMR counting of
Lemma 17 unchanged, but Lemmas 12–17 are not formalized here). Reading `W[i]` first repairs it: Mutual Exclusion then holds
for every `n`, every grouping and unbounded sequence numbers (`mutualExclusion_repaired`).

**Details.** Writer at line 21 waits for `<0,CS>` because reader `r₂` entered the CS on
`PREENTRY` (so `C = 1, W = 0`). Reader `r` starts waiting (`C = 2, W = 1`) and in `HelpWCS` reads
`C = 2`; reader `r₃` then starts waiting (`C = 3, W = 2`); `r` reads `W = 2`, equal to the `C` it
read, and CASes `WSIG[0]` to `<0,CS>`; the writer enters the CS while `r₂` is still there. The proof of
Lemma 8 treats the two reads as one atomic snapshot ("there is a time `t'` in which all readers that
incremented `C[i]` … are waiting"). The paper never fixes the order, and nothing in it points to reading `W[i]` first
(the prose, too, says `HelpWCS` "reads counters `C[i]` and `W[i]`").

**Repair.** Read `W[i]` first: while the writer is before its CS, `W[i]` can only grow and every
reader counted in `W[i]` is counted in `C[i]`, so `c = w` forces every group-`i` reader in a passage
to be waiting when `C[i]` is read. The invariant (`Inv` in `Alg/Safety.lean`) also gives Lemma 11
(`lemma11_repaired`).

### ⚠️ Line 47 of Algorithm 1 (`op` instead of `op'`)
With the literal test `op = WAIT` (the opcode read on entry) a single reader breaks Deadlock Freedom (the writer waits in line 21 forever while the reader is in the remainder section, `deadlock_literal_line47`) and Mutual Exclusion (`mutex_violation_literal_line47`).

**Impact.** A typo with evident intent (the branch uses `seq'` from line 41 and the `PREENTRY` branch
tests `op'`); with `op'` both executions disappear. Counted as ⚠️ (R3); the line-51 issue above
decides the verdict.

**Details.** Deadlock: the reader entered on `PREENTRY`, the writer then publishes `WAIT` and waits for
`<seq,CS>`; the exiting reader reads `<seq,WAIT>` in line 41 but skips `HelpWCS` because its entry
opcode was `PREENTRY`. Mutual exclusion: a reader that waited on entry reads `<1,NOP>` on exit and
still calls `HelpWCS(1)`; it signals `<1,CS>` to writer passage 1 before that passage publishes
`WAIT`, then re-enters on `PREENTRY`, and the writer enters its CS too.

### Typos and slips
- Concurrent Entering (§2.1): "any reader that executes **at most** `b` steps … enters the CS" should
  read "after `b` steps of its entry section".
- Lemma 3: "steps executed by other processes when they are aware of `p`" must mean awareness *after*
  the step (read literally, a read that makes `q` aware of `p` is kept and returns a different value);
  the proof uses the intended reading.
- Lemma 4 writes `⊂` for `⊆`.

## Proof gaps (statements true)

### 🛠️ Theorem 5 (the tradeoff `Ω(log (n / f(n)))`)
The proof relies on the false Lemma 1 and does not show that the readers' poised steps stay expanding after Lemma 2 reorders them, nor that its drain phase leaves all readers poised simultaneously.

**Impact.** Statement true; repaired (`theorem5`, exact form `n ≤ Wb · 3^Rb`).

**Details.** (1) Lemma 1 is replaced by `lemma1_count`, applied to the fragments `C₁ ↪ E₂E₃` (writer)
and `C₁ ↪ E₂` (reader). (2) Whether a step is expanding depends on the steps scheduled before it; it
is preserved here because all poised steps are reads or CAS steps, during which familiarity sets only
grow (`round_expanding`). (3) In the phase `σ''`, a non-expanding write of one reader can change
whether another reader's poised step is expanding; the construction (`e2_construct`) repeats single
non-expanding steps until all remaining readers are simultaneously poised on expanding steps. (4)
During `E₃` each expanding step of the writer adds at most `3^r` processes to its awareness set,
although the writer itself changes familiarity sets (`aw_solo_bound`).

### 🛠️ Lemma 2 (one round at most triples awareness)
Case 1 of the proof claims that after the writes of `σ₂` the value of `v` differs from the expected value of all CAS steps of `σ₃`; a write may restore that value.

**Impact.** Statement true: at most one CAS of `σ₃` on `v` succeeds, which keeps the factor 3. We
prove it with a greedy schedule (`lemma2`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, deterministic crash-free processes: `n` readers and `m` writers
  (`Proc n m = Fin n ⊕ Fin m`; Theorem 5 is stated for `m = 1`, `theorem5_general` for any `m`).
  Registers support read, write and CAS; CAS returns the old value, as in the paper.
- A reader-writer lock is a CSLib implementation (`Impl`) of `lock`/`unlock` (entry/exit section);
  remainder/entry/CS/exit are CSLib's regions. Executions are arbitrary interleavings (adversarial
  scheduler); no randomness.
- Properties (§2.1): Mutual Exclusion; Bounded Exit and Concurrent Entering with bounds that may depend
  on the configuration (weaker than the paper's constants); Deadlock Freedom in CSLib's form, which the
  paper's form implies. So our hypotheses are weaker than the paper's.
- RMRs in the cache-coherent model: any `CacheModel` (three axioms), with the paper's write-back and
  write-through protocols as instances (`writeBack`, `writeThrough`). `WriterEntryRMR`/`ReaderExitRMR`
  are worst-case bounds over all executions.
- Awareness and familiarity sets (Definitions 1–2) are computed forward along an execution fragment,
  starting from `AW(p) = {p}`, `F(v) = ∅` (`kstep`, `Ext.fresh`); expanding steps are Definition 3
  verbatim.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Fact 1, Observation 1 | `expanding_iff`, `kstep_aw`, `xrun_aw_mono` | `Awareness.lean` |
| Lemma 1 (false) | `lemma1_false`, `lemma1_false_writeThrough` | `Counterexample.lean` |
| Lemma 1 (counting form) | `lemma1_count` | `Lemma1.lean` |
| Lemma 2 | `lemma2` (+ `round_expanding`) | `Lemma2.lean` |
| Lemma 3 | `lemma3` | `Erasure.lean` |
| Observation 3 | `exists_E1`, `solo_returns_of_deadlockFree` | `Construction.lean`, `Solo.lean` |
| Construction of `E₂` | `e2_construct` | `E2.lean` |
| Lemma 4 | `lemma4` | `Theorem5.lean` |
| Theorem 5 | `theorem5`, `theorem5_logb`, `theorem5_general` | `Theorem5.lean` |
| Corollary 6 | `corollary6` | `Theorem5.lean` |
| Lemma 8/9 (false as written) | `mutex_violation_literal_order` | `Alg/Counterexamples.lean` |
| Line 47 as written | `mutex_violation_literal_line47`, `deadlock_literal_line47` | `Alg/Counterexamples.lean` |
| Lemma 8/9 (repaired algorithm) | `mutualExclusion_repaired` | `Alg/Safety.lean` |
| Lemma 10 | `boundedExit_reader`, `boundedExit_writer` | `Alg/BoundedExit.lean` |
| Lemma 11 (repaired algorithm) | `lemma11_repaired` | `Alg/Safety.lean` |

**Not formalized.** Corollary 7 (needs the `Ω(log m)` mutual-exclusion lower bound of
Attiya–Hendler–Woelfel; `theorem5_general` holds for every `m`). For `A_f`: Concurrent Entering, Deadlock Freedom and no reader
starvation (Lemmas 12–16), the RMR bounds (Lemma 17; they also depend on the cited `f`-array counters),
and `m > 1` writers (the writers' lock `WL` is omitted). `A_f` is modelled with atomic counters
`C[i]`, `W[i]` (as the paper assumes), one writer, an arbitrary static partition of the readers into
groups, and the two disputed lines as parameters.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `toyLock_spec` (`NonVacuity.lean`) gives, for every `n`, a reader-writer lock (reader flags plus a writer flag) satisfying all non-RMR hypotheses of Theorem 5 (every process may invoke, Mutual Exclusion, Bounded Exit, Concurrent Entering, Deadlock Freedom). The model is built on CSLib's `Impl`, `regionOf`,
`Impl.DeadlockFree` and `InfExec` (`Cslib/Computability/Distributed/SharedMemory/`). CSLib candidates
(marked `-- CSLib candidate`): `CacheModel` with `writeBack`/`writeThrough` (`Model.lean`), `regFold`
lemmas (`Regions.lean`), `solo_returns_of_deadlockFree` (`Solo.lean`).
