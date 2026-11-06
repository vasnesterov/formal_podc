# Read/Update Tradeoffs for Counters, Snapshots and Max Registers — PODC 2014

Danny Hendler, Vitaly Khait. *Complexity Tradeoffs for Read and Update Operations.* PODC 2014. DOI
[10.1145/2611462.2611472](https://doi.org/10.1145/2611462.2611472). Formalized version: the authors'
copy with complete proofs (no arXiv version); numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** All the abstract's results hold: the counter/snapshot tradeoff (Theorems 1–2,
Corollary 1), the max-register tradeoff (Theorems 3–4) and the tree max register (Theorems 5–6). But the
information-flow machinery they rest on is unsound as defined (**Lemma 2 and Claim 1 are false** with
the paper's Definitions 1–5), so it had to be redesigned, and the proofs of Lemmas 4 and 6 and the
linearization points of Theorem 5 needed new arguments. Only Theorem 4 under its printed hypothesis for
`M > N` stays unproved.

## Mistakes in the paper

### ⚠️ Theorem 4 for `M > N` ("immediate from Theorem 3")
The paper calls Theorem 4 "immediate from Theorem 3", but with `K = min(N, M)` and `f = log M`, Theorem 3
gives only `Ω(log(log N / log log M))`, which is not `Ω(log log N)` for huge `M`.

**Impact.** We prove the theorem for `M ≤ N` (`theorem4_fin`), and for all `N, M` when ReadMax takes
`O(log min(N, M))` steps: in particular for read-optimal implementations (the abstract's claim), the
generic `theorem4` gives `Ω(log log min(N, M))`. Only ReadMax costs between `c log N` and `c log M`
are affected.

**Details.** The bound is `Ω(log log N)` only while `log log M` is small compared with `log N`; for
`M = 2^N` it gives no bound. So the case of huge `M` is unestablished, and we neither prove nor refute
it.

### 🛠️ Lemma 2 and Claim 1 (erasing processes nobody is aware of)
With Definitions 1–5 a writer can be hidden although a reader saw its value: if `q` writes `5` twice in a row and then `r` reads `5`, no event is aware of `q`, yet removing `q`'s events leaves no execution (`PaperDefs.lemma2_false`, `PaperDefs.claim1_false`).

**Impact.** These are the paper's tools for erasing processes; all lower-bound proofs use them.
The theorems survive: a sound awareness notion gives the same bounds, with the paper's constant 3
in Lemma 1.

**Details.** Definition 1 makes an event invisible in two cases:
- it does not change the value;
- it is overwritten by a write before any access to the object, and its process takes no step in
  between.

Here the first write of `q` is overwritten by `q`'s own second write, so it is invisible. The second
write leaves the value at `5`, so it is invisible too. Then no event of `r` is aware of any event of
`q` (Definition 2), even with a more generous transitive closure than the paper's. So `q` is hidden
(Definition 5), and the `E'` of Lemma 2 and the `E − {q}` of Claim 1 both equal `E` without `q`'s
events. Then the reader reads `0`, not `5`.

The implementation is a single-writer max register (`toyImpl`), wait-free and linearizable
(`toyImpl_linearizable`), so the counterexample lies in the setting of Claim 1. Nothing depends on
the toy's double write: two `WriteMax(5)` operations with one write each, or a 2-process
multi-writer max register built from per-process registers, give the same events. The paper does
mean trivial writes to be invisible: the proof of Lemma 1 schedules them first and asserts that
none of them is visible.

**Repair.** We use a data-flow semantics (`Cslib.SharedMemory.Awareness`):
- awareness sets grow by the familiarity set of each object read or CAS'ed;
- every write and every value-changing CAS records the writer's awareness set as the object's new
  familiarity set;
- trivial events change nothing.

On top of it:
- the erasure lemma `arun_erase` is the sound Lemma 2;
- `arun_filter_hidden` / `ess_erase` is the sound Claim 1;
- `exists_round` is Lemma 1, with the paper's three-phase schedule.

### 🛠️ Lemma 4 and Lemma 6 (proved under an extra invariant)
Both proofs assume that erasing hidden processes can only shrink familiarity sets, but erasing an object's last writer resurrects the previous write, possibly by another essential process.

**Impact.** Theorem 3 still holds. We prove both lemmas for essential sets satisfying a *block
invariant* that the construction maintains. Whether they hold for arbitrary essential sets
(Definition 7) is left open.

**Details.** Lemma 4 (low contention) picks processes whose objects are not familiar with *other
chosen* processes, then erases the rest. If an erased process wrote last to an object, the object
reverts to an older write. That write may come from a chosen process, which then becomes visible.

The high-contention case has a second problem. It classifies processes as read, write or
value-changing CAS using `o`'s value after `E_i`. The steps, however, are taken after the erasure,
which may change that value, so a "trivial" CAS can succeed.

Lemma 6 has the same issue. Erasing the completed process that the reader's next object is
familiar with can expose another completed process's older write to the reader.

**Repair.** The block invariant (`BlockOK`): for every object, the top run of its history written by
essential processes is written by a single process. We maintain it as follows:
- `lemma4_low` builds the conflict graph from *block owners*: out-degree ≤ 1, independent third by
  `exists_indep`;
- `lemma4_T`, `lemma4_W` and `lemma4_C` erase the owner of the contended object first and classify
  afterwards.

`lemma4` then gives `⌊√m⌋ ≤ 3(|E'| + 1)`, which implies the paper's `√m/3 − 2` without assuming
`m ≥ 81`.

`lemma6` replaces the reader-by-reader erasure with one comparison. It runs the reader with all
essential processes erased, notes the `≤ m` objects it reads, and keeps exactly the completed
processes owning none of them.

### 🔧 Definition 2 (awareness)
Definition 2 never propagates awareness through a process's local state, and its transitive clause
even requires every event in a chain to access the same object, while the proof of Lemma 1 reasons
with process-level awareness.

**Impact.** Lemma 1 holds with awareness that flows along a process's own events and without the
same-object requirement (`Cslib.SharedMemory.Awareness.exists_round`).

### ✏️ Slips
- Lemma 2 removes only the events of `q` that are aware of `p`, but the proof of Lemma 3 removes all
  events of `q` from the first such event on.
- Algorithm A, line 5: `n ← node.parent` should be `n ← n.parent`.
- Algorithm A: `T_L` needs `N` leaves (one per value `v < N`), not `N − 1`.

### Typos
- Lemma 4's proof cites "Claim 4"; only Claim 1 exists.

## Proof gaps (statements true)

### 🛠️ Theorem 5 (linearization points of Algorithm A)
Definition 9 linearizes a `WriteMax` when the root first "counts" it, but a completed `WriteMax` may never be counted (`AlgA.not_counts`: `N = 2`, `WriteMax(3)` by `p₀`, then `WriteMax(2)` by `p₁`).

**Impact.** The statement is true, with a new proof (`AlgA.linearizable`).

**Details.** A `WriteMax` is never counted when all its CASes succeed trivially, when its leaf write
is trivial, or when it returns early at line 16. The proof of Invariant 1 treats a trivial CAS as a
failed one.

**Repair.** We linearize `WriteMax(v)` at the first moment in its interval at which the root is
`≥ v`. Lemma 8 (`lemma8`) and the double-refresh guarantee (`root_ge_of_wDone`) are proved as state
invariants.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **System.** CSLib's asynchronous shared memory (`Cslib.SharedMemory.Impl`). Processes are
  deterministic and each step is one atomic access to a read/write/CAS register (`RWC ι V v₀`), with
  arbitrary value and index types. There are no crashes; the adversary is the scheduler, which
  chooses every interleaving. There is no randomness.
- **Implementations.** Implementations are linearizable (CSLib `Impl.Linearizable`).
- **Read bound.** The lower bounds assume only that the reader's operation completes within `R`
  solo steps from every reachable configuration (`SoloBound`). This is weaker than obstruction-freedom
  plus a worst-case bound.
- **Updates.** Updaters need no progress guarantee. Our conclusion is that some update operation has
  already taken the stated number of steps.
- **Objects.** Counters are `counterObj`; single-writer snapshots are CSLib `snapObj n`. The max
  register is CSLib `maxRegObj`, with `0` playing the role of `−∞`; it is `M`-bounded through
  `allowed`.
- **Generic theorem.** Theorem 1 and Corollary 1 are instances of `update_lower_bound`, which applies
  to any object whose read reveals all updaters. Corollary 1 is proved directly, not through the
  paper's reduction.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1–5 (literal), Lemma 2, Claim 1 false | `PaperDefs.lemma2_false`, `PaperDefs.claim1_false`, `toyImpl_linearizable` | `PaperDefs.lean`, `PaperDefsLin.lean` |
| Lemma 2 (sound), Claim 1 (sound) | `Cslib.SharedMemory.Awareness.arun_erase`, `arun_filter_hidden`, `ess_erase` | `Podc/.../Awareness.lean`, `MaxRegSetup.lean` |
| Lemma 1 | `Cslib.SharedMemory.Awareness.exists_round` | `Podc/.../AwarenessRound.lean` |
| Lemma 3 | `reader_aware_all` | `UpdateLB.lean` |
| Theorem 1 | `update_lower_bound` (generic), `counter_tradeoff`, `counter_update_logb` | `UpdateLB.lean`, `CounterSnapshot.lean`, `Theorem2.lean` |
| Corollary 1 | `snapshot_tradeoff`, `snapshot_update_logb` | `CounterSnapshot.lean`, `Theorem2.lean` |
| Theorem 2 | `theorem2_counter`, `theorem2_snapshot` | `Theorem2.lean` |
| Lemma 4 | `lemma4` (`lemma4_low`, `lemma4_T`, `lemma4_W`, `lemma4_C`, `exists_indep`) | `Lemma4.lean`, `Lemma4Aux.lean` |
| Lemmas 5–6 | `lemma6` (`read_lt`, `read_ge`, `solo_transfer`) | `Lemma6.lean`, `MaxRegSetup.lean` |
| Theorem 3 | `ess_iter`, `theorem3` | `Theorem3.lean` |
| Theorem 4 | `theorem4`, `theorem4_fin` (`M ≤ N`) | `Theorem3.lean` |
| Asymptotics | `doubly_log_bound`, `loglog_bound`, `logb_le_of_mul_pow`, `log_bound_of_mul_pow` | `Asymptotics.lean` |
| Lemma 8, Lemmas 9/11 | `AlgA.lemma8`, `AlgA.root_ge_of_wDone` | `AlgA/MemInv.lean` |
| Theorem 5 | `AlgA.linearizable`; Definition 9 broken: `AlgA.not_counts` | `AlgA/Lin.lean`, `AlgA/Counterexample.lean` |
| Theorem 6 | `AlgA.waitFree`, `AlgA.readMax_steps_le`, `AlgA.writeMax_steps_le` | `AlgA/Steps.lean`, `AlgA/Layout.lean` |

**Proof remarks.** The `o(·)`/`Ω(·)` steps of Theorems 1 and 3 are made exact. Theorem 1 becomes
"`R · 3^k + 1 < N` ⇒ some update takes `k + 1` steps". Theorem 3 becomes the recursion
`|E_{i+1}| ≥ ⌊√(|E_i| − m)⌋/3 − 1` with the explicit threshold `max(2m, 10^6)`; the paper's Eq. (4)
iterates a hidden `Ω` constant `i` times. Lemma 5 is folded into `lemma6`.

**Not formalized.**
- **Theorem 4 for `M > N`** with ReadMax above `O(log min(N, M))`: see the mistake above.
- **Lemmas 4 and 6 without the block invariant.**

**Trust.** There is no `sorry`. All listed theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Non-vacuity:
- the counterexample implementation `toyImpl` is a genuine wait-free linearizable max register;
- Algorithm A satisfies the hypotheses of the max-register theorems (it is linearizable and its
  `ReadMax` takes one step).

The model comes from CSLib's `SharedMemory` library (`Model`, `History`, `LinPoints`). The awareness
and erasure machinery is staged in `Podc/Computability/Distributed/SharedMemory/Awareness*.lean` as
a CSLib candidate.
