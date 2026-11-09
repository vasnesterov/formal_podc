# Space-Efficient Lock-Free Linear-Probing Hash Table — PODC 2026

Hagit Attiya, Rotem Oshman, Noa Schiller. *Brief Announcement: A Space-Efficient Lock-Free
Linear-Probing Hash Table.* PODC 2026. DOI
[10.1145/3796701.3815936](https://doi.org/10.1145/3796701.3815936). Formalized version: the full
version, arXiv 2606.17315v1 (*Space-Efficient Lock-Free Linear-Probing Hash Table*, 32 pp.), which
contains the pseudocode (Algorithms 1–6) and the proofs; numbering follows it.

**Verdict: ⚠️ Weakened.** The **CAS version (Algorithm 6) is not linearizable**: a 2-process,
2-cell execution has no linearization (`cas_not_linearizable`), so Theorem 1 fails for the CAS
primitive with logarithmic metadata. For the LL/SC version (the paper's main design, constant
metadata) we proved in Lean lock-freedom, wait-freedom of lookups, Lemma 4 (at most one final
copy per key), Proposition 3 and Proposition 2 (no spurious `ABORT`); its linearizability was
checked only by exhaustive model checking of small configurations (no violation found), not in
Lean.

## Mistakes in the paper

### ❌ Theorem 1, CAS version (Algorithm 6 with `del_copy`, lines 66–80)
With CAS, an insert whose own copy was already deleted can still *mark* a later tentative copy
of another insert (line 116 runs before the own-cell check of line 120); the victim's CAS to
`⟨v, final⟩` (line 67) fails, line 69 tests the stale value read at line 66, `del_copy` resurrects
only `⟨v, revalidate⟩` (line 77), so the victim tombstones its copy and its `insert(v)` returns
`false` although `v` is absent: with 2 processes and 2 cells, `insert(v) ∥ delete(v); insert(v)`
is not linearizable (`cas_not_linearizable`).

**Impact.** Theorem 1's claim for CAS (`⌈log U⌉ + min{⌈log m⌉, ⌈log n⌉} + O(1)` bits per cell)
is unsupported; the LL/SC version is not affected (the bug needs marked values, which exist only
with CAS, and breaks the CAS case of Lemma 7).

**Details.** The execution (`cex`, key `v`, both hashed to cell 0, table `[E, E]`):
1. `p0` invokes `insert(v)`, scans, writes `⟨v,t⟩` into cell 0 (line 43) and starts its duplicate
   scan (line 48), skipping its own cell.
2. `p1` runs `delete(v)`: reads `⟨v,t⟩` in cell 0 and overwrites it with `DELETED` (line 88);
   it returns `true`.
3. `p1` invokes `insert(v)`: cell 0 holds `DELETED`, so it writes `⟨v,t⟩` into cell 1, completes
   its duplicate scan and reads its own cell (line 66).
4. `p0` (its copy deleted) reads `p1`'s copy in cell 1 (line 65); the copy is later and tentative,
   so `del_other_copy` (Alg. 6) CASes it to `⟨⟨v,0⟩,marked⟩` (line 116) — before checking its own
   cell (line 120).
5. `p1`'s CAS to `⟨v,final⟩` (line 67) fails; `restart(cur_val)` at line 69 is evaluated on the
   stale `⟨v,tentative⟩` read at line 66, so `p1` calls `del_copy`, which reads the marked value
   (line 76), does not resurrect it (line 77 tests only `⟨v,revalidate⟩`) and tombstones it
   (line 80); `insert(v)` returns `false`.

The `delete(v)` returned `true` before the second `insert(v)` was invoked and the only other
`insert` must precede that `delete`, so the set is empty when the second `insert` starts and
nothing can make it non-empty: no linearization exists. The CAS proof of Lemma 7 assumes that the
marked copy is overwritten only by its owner or the marker and that an owner whose CAS fails
revalidates (Section 5.1 says a marked copy "may transition to `⟨v,tentative⟩`"); `del_copy` never
does this, and the claim that "only `op2` can write the cell number `i`" overlooks that `op2`'s
copy can be already deleted. The bug was found by our explicit-state model checker (also with
process ids instead of cell indices in the marks) and the trace was replayed in Lean.

**Repair.** Not proved in Lean. Model checking suggests the fix: at line 77 test `restart(val)`
instead of `val = ⟨v, revalidate⟩`, and when the CAS of line 78 fails go back to line 76 (instead
of reading at line 79 and tombstoning at line 80). Fixing only line 77 is not enough (a lookup can
turn the mark into `⟨v,revalidate⟩` between lines 76 and 78, and line 80 then tombstones a
revalidated copy). With both changes no violation was found in any configuration checked (about 10 000
configurations, up to 5 processes and 6 cells, marks with cell indices or process ids).

### ✏️ Slips
- Section 3 defines *properly-paired* LL/SC as "an `LL(x)` is eventually followed by `SC(x, _)`",
  but every scan performs `LL`s without `SC`s. What the algorithm satisfies (and what Section 4.2
  means) is that every `SC` targets the cell of the process's last `LL`, with only plain reads in
  between; our model checker found no difference between per-cell links and a single reservation
  per process.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`):
- any set of processes `P`, keys `K`, a table of `m ≥ 1` cells and any hash function
  `h : K → Fin m`; indices wrap modulo `m` (`Fin m`), and the comparison of line 51 is the probe
  distance `dist h v i = (i − h v) mod m`; the table starts empty;
- LL/SC version: one CSLib `llscObj` per cell (per-process links: `SC` succeeds iff the cell was
  not written since the caller's last `LL`); `Read` = `LL`, `Modify` = `SC`, the plain reads of
  lines 94, 102, 105 are `VL` (value, no link change);
- CAS version: one CSLib `casObject` per cell, cells may hold `⟨⟨v, j⟩, marked⟩`;
- each process runs Algorithms 1–4 (and 5 or 6) as a state machine, one shared-memory access per
  step (`Defs.lean`, `DefsCAS.lean`); asynchronous adversarial scheduler, no crashes beyond
  stopping (executions are arbitrary finite label sequences);
- the specification is the dictionary in which `insert` may return `ABORT` at any time without
  effect (`dictSpec`, a CSLib `NSpec`); linearizability is CSLib's `IsNLinearization`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1, CAS version, is false | `cas_not_linearizable` (`cex_valid`, `cex_not_linearizable`) | `CounterexampleCAS.lean` |
| Lemma 4 (at most one `⟨v, final⟩`) | `lemma4` | `Lemma4.lean` |
| Proposition 3 (no `EMPTY` before a copy) | `prop3` | `Lemma4.lean` |
| Proposition 2 (no spurious `ABORT`) | `prop2` | `Prop2.lean` |
| Section 5.3: lookups are wait-free (≤ `6m + 5` steps) | `lookup_waitFree` | `Lookup.lean` |
| Section 5.3, Lemmas 18–19: lock-freedom (finitely many processes) | `lockFree` | `LockFreeMain.lean` |
| invariant behind Lemma 4 | `Inv`, `inv_of_run` | `Step.lean`, `Lemma4.lean` |

Lemma 4 is proved differently from the paper: an inductive invariant (`Inv`) with ghost
timestamps of the owners' rounds says that an owner that has *covered* (scanned past) the cell
of another owner's tentative copy started its round earlier, and that no owner with a tentative
copy covers a final copy; a final write then cannot coexist with another final copy. The same
invariant gives Proposition 3.

Lock-freedom is also proved differently from Lemmas 15–17: a potential `A · budget + Σ local`
decreases at every step that is not a response. Each successful `SC` consumes one unit of a
budget held by the pending operations (an operation before it owns a cell holds 3, an owner
1 plus 1 for a tentative and 2 for a revalidate mark in its cell, an idle process 4). Between
successful `SC`s each step decreases the stepping process's local potential (scan positions,
and for the retry loops of `try_delete` and `del_copy` whether its last `LL` is still valid,
which only another process's successful `SC` can change). So a stretch of the execution without
responses has at most `pot C` steps, where `C` is its first configuration.

**Not formalized.** The linearizability of the LL/SC version (Lemmas 5–14: per-key
linearizations, insert sequences), the bit counts of Theorem 1, and the step-complexity analysis
(Proposition 20, Theorem 21). For the LL/SC version, our explicit-state model checker
(linearizability by exact tracking of the set of possible linearizations, lock-freedom as absence
of response-free cycles) found no violation in
about 8 000 configurations: 4–5 processes with one or two operations each (several concurrent
inserts of the same key with deletes and lookups), 3–6 cells, two keys, all initial tables with
tombstones and final copies consistent with linear probing, up to 47 million states per
configuration. With a single reservation per process instead of per-cell links the reachable
states are the same.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound` (the counterexample's execution and finite check are evaluated by `decide +kernel`).
The model uses CSLib's `Impl`, `llscObj`, `casObject`, `NSpec` and `IsNLinearization`.
