# O(1)-Barriers Optimal-RMR Mutual Exclusion — PODC 2013

Hagit Attiya, Danny Hendler, Smadar Levy. *An O(1)-Barriers Optimal RMRs Mutual Exclusion Algorithm.*
PODC 2013. DOI [10.1145/2484239.2484255](https://doi.org/10.1145/2484239.2484255). Formalized version: the
authors' extended abstract (11 pages, from Hendler's web page; no arXiv or full version available).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Theorem 1, the CAS version, holds in full under TSO: Algorithm 1 satisfies mutual
exclusion, starvation freedom and (log n + 3)-bounded waiting (even log n + 2), and every passage costs at
most `19 log n + 23` RMRs and two barriers. But the paper's safety proof treats every write as performed
when it is issued, so Lemma 2 is false as stated and mutual exclusion needs a new inductive invariant over
the store buffers. The read/write variant (Theorem 12), on which the abstract's "first read/write" claim
rests, was not checked.

## Mistakes in the paper

### 🛠️ Lemma 2 under TSO (parts (b), (c); part (d) and Corollaries 3–4 rest on it)
The proof of Lemma 2 treats every write as performed when it is issued and never mentions store buffers, so parts (b) and (c) fail under TSO (`lemma2b_false`, `lemma2c_false`) and mutual exclusion under TSO is asserted rather than proved.

**Impact.** Mutual exclusion and the repaired parts hold (`mutual_exclusion`, `lemma2d`, `corollary4`,
`lemma2b`, `lemma2c`). Part (b) holds under sequential consistency, but the paper's model is TSO. The whole
proof of Lemma 2 reasons at the sequential-consistency level ("step `s` is the execution of statement 47 …
`p` is the lock owner"), and no part of Section 5 explains why the store buffers do not matter for safety.

**Details.**
- **Part (b).** "If `pc(C,p) = 48`, then the lock owner is the process `p` dequeued" fails, because
  `lock ← next` (statement 47) may still be in `p`'s store buffer, so `C.lock = p` (`lemma2b_false`, 31
  events, 2 processes). Symmetrically, after `lock ← next` is performed but before `signal[next] ← true` is,
  `p` is still in its exit section by Definition 1 while `pc ≠ 48` and `p` no longer owns the lock.
- **Part (c).** A process that was signalled in an earlier passage issues `signal[r] ← false`
  (statement 17), but the write sits in its store buffer while `C.signal[r]` (memory) is still true.
  Two processes then satisfy the condition at once (`lemma2c_false`, 80 events, 2 processes).
- **Safety.** The real argument needs facts the paper never states. Writes of one process are
  performed in FIFO order, so the next lock owner sees all writes of the previous one. A process that
  is enqueued has performed its `signal[r] ← false` before its `apply[r] ← true`. The holder reads
  `promQ` and `inPromQ` partly from its own buffer, and its view of `promQ`, `inPromQ` and `exits`
  is the logical value left by all earlier holders.

**Repair.** We use an inductive invariant over all TSO configurations (`Inv`, `InvDefs.lean`; preservation in
`InvFlush.lean`, `InvStep.lean`), stated in terms of performed writes and store-buffer contents. It fixes the
exact store-buffer contents at each program counter, the owner of `lock`, the "logical" queue (the lock
owner's view), and the relation between `exits` and the number of CS entries. It was validated by an
exhaustive model checker (n = 2, 3 passages each) before the Lean proof. `lemma2b`: during the exit section,
`p` owns the lock in memory unless its write of statement 47 has been performed. In that case the lock owner
is the dequeued process, which is in its entry section.

### 🔧 Lemma 2(c), range of `pc` (who holds `signal`)
The invariant "if `signal[r] = true` and `17 < pc(r) < 49`, then `r` owns the lock" fails even under sequential consistency: a process `r` that entered the CS by being signalled and has executed statement 47 (`lock ← next`) is at `pc = 48` with `signal[r]` still true while `next` owns the lock (`lemma2c_false_sc`, 2 processes, every write performed immediately).

**Impact.** Mutual exclusion (Corollary 3, part (d) of the lemma) is unaffected and is proved from a
corrected invariant (`lemma2c`, `lemma2d`).

**Details.** Case 4 of the proof (statement 47) says that `17 < pc(C,p), pc(C_s,p) < 49`, so
invariant (c) "cannot be violated". This overlooks the exiting process itself when its own `signal`
is set. Case 5 (statement 48) then applies (c) to that same process at `pc = 48`.

**Repair.** The corrected statement covers only processes past their barrier, statements 23–27
(`lemma2c`): if `signal[r]` is set in memory, then `r` owns the lock and nobody else is in the critical
or exit section. It is a consequence of the TSO invariant `Inv` (clause `sig`).

### 🔧 Footnote 4 (reads of the process's own writes)
Footnote 4 says that "a read accesses a variable that was previously written to by the same thread only after a barrier", but the exit section reads `promQ` (statements 37, 42, 45) and `inPromQ` (statement 36, when the same process id is read at two consecutive levels) after writing them, with the writes still in its buffer.

**Impact.** Nothing in the paper depends on the footnote.

**Repair.** Drop the claim: the Lean model serves reads from the process's own buffer, and `theorem1` holds.

### Typos
- Statement 45 says `Q.dequeue()` for `promQ.dequeue()`.

## Proof gaps (statements true)

### 🔧 Lemma 7, base case of Claim 2 (role of statement 25)
The base case neither uses the `exits − e ≥ 2` disjunct of statement 25 nor handles a process that waits at statement 25 forever.

**Impact.** Repaired (`Run.waiting_entry`, `Run.starvation_freedom`).

**Details.** This disjunct is exactly what guarantees that a lock owner enters *after* `p`'s barrier.
The owner `r` at `p`'s failed CAS may already have read the root and buffered its increment of
`exits`.

**Repair.** Suppose `p` completes its barrier at `ta` and never enters. Then some process enters the
CS after `ta` (`Run.waiting_entry`). The argument tracks `ent ≤ exits + 1` and shows that `lock` can
only leave `−1` by a CS entry. If nothing enters, the lock eventually stays free and `p` reads it.
The inductive step of Claim 2 is formalized as stated: it takes the last write to the parent node
before the stabilization time, uses TSO order of the doorway writes (`perf`, `Doorway.lean`), and
the minimal level among starved processes.

### 🔧 Lemma 9 (missing case)
The case split on the process `r` read from `n^m_p` misses `r = q′` (the reader itself wrote the node), and case 1 silently needs `r` to have stayed in its entry section since its write, so that `apply[r]` has been performed.

**Impact.** Both cases are easy. Lemma 8 is proved with the sharper bound `log n + 2` (`lemma8`), and the
paper's `log n + 3` follows (`lemma8_log_n_add_three`).

### 🔧 Lemma 10 (RMR counts at statements 25 and 27)
"At most 4 RMRs at statement 25 (twice `exits`, twice `lock`)" is wrong: the true bound is 6, attained by a run with 4 processes in which `p` reads `lock` remotely 4 times and `exits` twice (`stmt25_tight`), and statement 27 can cost 2 RMRs, not 1 (`stmt27_two`).

**Impact.** Only constants change: `lemma10_rmr` gives `≤ 19 log n + 23` RMRs per passage,
`lemma10_barriers` gives exactly 2 barriers per complete passage.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory under **TSO**, operational, after Section 3 of the paper.
  - Every process has a FIFO store buffer. A write is *issued* (appended) by the process and
    *performed* (removed from the buffer and written to memory) by an adversarial `flush` event at
    any time.
  - Reads return the newest buffered write to the variable, else memory.
  - A barrier step performs the oldest buffered write, or proceeds when the buffer is empty.
  - A CAS first performs the whole buffer.
- `n = 2^h` processes, `log n = h`, complete binary tree in heap numbering. No crashes. Every step
  performs one shared access.
- `foreach` loops follow a fixed order. Statement 34 reads `n`, `n.left`, `n.right` in this order.
  Candidates are deduplicated in order of first appearance.
- `exits ← exits + 1`, `enqueue` and `dequeue` read and issue in one step. Only the lock owner
  accesses these variables, which `corollary4` shows.
- The CS is one local step.
- **Adversary/fairness:** for safety, bounded waiting and RMR bounds, every schedule of steps and
  flushes. For starvation freedom, weak fairness (`Run.Fair`): a process outside the remainder
  section eventually takes a step. Flushes need no fairness, since barriers drain buffers.
- **RMRs (CC model of Section 3):**
  - Every issued write and every CAS costs 1.
  - A read from the own buffer is free.
  - A read from memory costs 1 iff the reader's cached copy was invalidated, by a write of another
    process *performed* since its last read, or if it is the first read.
  - A failed CAS writes nothing and invalidates nothing. This is the paper's rule; with a convention
    where every CAS invalidates, the bound at statement 25 would not be constant. This is a remark
    only, not formalized.
- Deterministic algorithm, no randomness.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (all four properties) | `theorem1` | `Main.lean` |
| Lemma 2(a) | `lemma2a` | `Safety.lean` |
| Lemma 2(b), false under TSO / repaired | `lemma2b_false` / `lemma2b` | `Lemma2Literal.lean` / `Safety.lean` |
| Lemma 2(c), false (SC and TSO) / repaired | `lemma2c_false_sc`, `lemma2c_false` / `lemma2c` | `Lemma2Literal.lean` / `Safety.lean` |
| Lemma 2(d), Corollary 3 (mutual exclusion) | `lemma2d`, `mutual_exclusion` | `Safety.lean` |
| Corollary 4 (promQ accessed sequentially) | `corollary4` | `Safety.lean` |
| Lemma 5(a), 5(b) | `lemma5a`, `Run.lemma5b` | `Safety.lean`, `Progress.lean` |
| Lemma 6 (generalised) | `Run.handed_enters` | `Progress.lean` |
| Lemma 7 (starvation freedom; Claims 1–2) | `Run.starvation_freedom` | `Starvation.lean` |
| Lemma 9 | `lemma9` | `BoundedWaiting.lean` |
| Lemma 8 (`log n + 2`, and `log n + 3`) | `lemma8`, `lemma8_log_n_add_three` | `BoundedWaiting.lean` |
| Lemma 10 (RMRs, barriers) | `lemma10_rmr`, `lemma10_barriers`, `lemma10_barriers_le` | `RMRMain.lean` |
| Lemma 10 proof constants (25: 6, 27: 2) | `stmt25_rmr_le`, `stmt25_tight`, `stmt27_rmr_le`, `stmt27_two` | `RMRMain.lean`, `RMRTight.lean` |

**Not formalized.** Section 6 (Lemma 11 and Theorem 12, the read/write version via the comparison-object
simulation of Golab et al.) and Observation 1 (`exits` modulo `(n−1)(log n+2)+1`). The experimental
appendix is out of scope.

**Trust.** No `sorry`, no `native_decide`. All listed theorems use only `propext`, `Classical.choice`,
`Quot.sound`. Counterexamples are concrete executions checked by `decide +kernel`.

Non-vacuity:
- `rrRun_fair`: a round-robin execution is fair.
- `passage_exists`: complete passages exist.
- `stmt25_tight`, `stmt27_two`: the RMR constants are attained.

The model is paper-local (`Model.lean`); no CSLib modules were needed.
