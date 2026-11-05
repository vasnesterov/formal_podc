# Limited-Use Atomic Snapshots — PODC 2012

James Aspnes, Hagit Attiya, Keren Censor-Hillel, Faith Ellen. *Faster than Optimal Snapshots (for a While).*
PODC 2012. DOI [10.1145/2332432.2332507](https://doi.org/10.1145/2332432.2332507). Formalized version: the
journal version *Limited-Use Atomic Snapshots with Polylogarithmic Step Complexity*, J. ACM 62(1):3, 2015
(author copy), together with the authors' erratum to it; numbering follows the journal version. The
proceedings version has the same Algorithm 2 (its Lemmas 1–3 and Theorem 4). Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Theorem 3.4 is false: the 2-component max array of Algorithm 2 (as published,
in both versions) is not linearizable. The authors found this error and published it in their erratum; we
confirm it in Lean for `k = 3`. With the erratum's fix (an embedded `MaxScan` in `MaxUpdate1`), the max
array is linearizable for every tree shape. The headline is not refuted, only left unproved as published:
over atomic max arrays, Algorithm 3 is a linearizable `(b−1)`-limited-use snapshot with `O(log² b log n)`
Updates and `O(log b)` Scans, and so is the multi-writer version (Theorem 5.1). The corrected max array keeps
these bounds. Theorem 4.2 needed new linearization points, because the paper's ones are wrong; this flaw is
not in the erratum.

## Mistakes in the paper

### ❌ Theorem 3.4 (Algorithm 2, linearizability of `MaxArray_{k×h}`)
Algorithm 2 is not linearizable: with `k = 3` (balanced tree, `m = 2`) and three processes, a slow
`MaxScan` returns `(1, 0)` although `MaxUpdate1(r, 1)` completed before `MaxUpdate0(r, 1)` started
(`alg2_not_linearizable`).

**Impact.** The authors found this error and published it in their erratum; we confirm it in Lean.
The max array is the paper's key tool. The headline snapshot is left unproved as published,
because the proof of Theorem 4.2 uses Theorem 3.4, but it is not refuted. The erratum's correction is
linearizable (`alg2_fixed_linearizable`, for every tree shape). It changes the cost of `MaxUpdate1` from
`O(log h)` to `O(log k log h)`, and Algorithm 3's `O(log² b log n)` per Update absorbs this.

**Details.** The execution is the erratum's:
1. `p₀` starts `MaxScan`, reads `r.second = 0` (line 11) and `r.switch = 0` (line 12), then pauses.
2. `p₁` runs `MaxUpdate1(r, 1)` to completion.
3. `p₂` runs `MaxUpdate0(r, 1)` to completion. It goes left at the root and sets the switch of the left
   child.
4. `p₀` resumes: it propagates its stale `0` into `r.left.second`, follows the new switch and returns
   `(1, 0)`.

A linearization that lets the scan see `1` in the first component must put `MaxUpdate0` before it, and by
real-time order also `MaxUpdate1`. The Lean execution (`badExec`, 17 labels) is checked by `decide`. The
non-linearizability proof is a short argument on an arbitrary candidate linearization.

The proof of Theorem 3.4 orders scans among themselves and each update against the scans, but never
orders `MaxUpdate0` against `MaxUpdate1`. The PODC 2012 version has the same Algorithm 2 and proof.

**Repair.** Line 9.5 of the erratum: `MaxUpdate1` performs a `MaxScan` after its `WriteMax`. We prove
this version linearizable (`alg2_fixed_linearizable`) with a new history-level criterion for max arrays
(`exists_isLinearization_maxArr`). The erratum gives only a sketch of the linearization of `MaxUpdate1`
("after its invocation and immediately before any `MaxScan` returns `≥ v`"). It does not say which such
scan is meant, given that scans are ordered by their results and not by real time. So we do not use it.
Instead each update goes immediately before the first scan that may see it, or last if there is none.

In Algorithm 3, every `MaxUpdate1` (line 10) is followed by a `MaxScan` of the same process (line 12),
which is what the erratum's line 9.5 adds. So Algorithm 3 may be linearizable even over the original
Algorithm 2. We did not check this.

### Typos and slips
- The erratum says the embedded `MaxScan` is added to `MaxUpdate0(r, v)` "after its
  `WriteMax(r.second, v)`". That line belongs to `MaxUpdate1`, which is what its own step-complexity
  paragraph uses.
- Lemma 3.5 is correct for Algorithm 2 as published (`lemma_3_5`), but it is not the cost of the
  linearizable, corrected algorithm (`lemma_3_5_erratum`: `MaxUpdate1` is `O(log k log h)`).

## Proof gaps (statements true)

### 🛠️ Theorem 4.2 (linearization points of Section 4.1)
Linearizing an `Update` at the first `WriteMax(root.mr, ptr ≥ d)` (`d` its own root pointer) is wrong,
because another process may carry the new value to the root inside a smaller pointer `c < d`, and a
`Scan` reading `c` returns the value before the `Update` is linearized
(`Snapshot.Counterexample.paper_linearization_points_fail`, 3 processes).

**Impact.** Statement true; repaired (`Snapshot.theorem_4_2`).

**Details.** The false step is "if there is no `Update` by process `j` linearized before `op`, then
`count_j = 0`".

**Repair.** Linearize an `Update` of process `j` with counter `m` at the first `WriteMax(root.mr, c)` with
`(root.seq[c])_j ≥ m`.

### 🛠️ Lemma 4.1
The proof does not justify that the parent's index at the invocation is at most the sum of the
children's components (it follows from the monotonicity of `seq` along max-array states).

**Impact.** Statement true; repaired (`Snapshot.lemma_4_1`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous wait-free shared memory, CSLib `Cslib.SharedMemory.Impl`. Processes are deterministic and
  scheduled arbitrarily; a crash is a process that stops taking steps. There is no randomization.
  Linearizability is CSLib's (amended Herlihy–Wing).
- Algorithm 2 is flattened over an arbitrary binary tree `T : Shape`. The leaves are the values of the
  first component, and the split `m` at a node is the size of its left subtree. This covers the balanced
  `m = ⌈k/2⌉` and every unbalanced choice. The switches are atomic 1-bit registers. The `MaxReg_h`
  objects `second` are atomic max registers, as the paper uses them in Theorem 3.4; their access cost
  `ch` is a parameter of the step bounds.
- Algorithm 3 is modelled over atomic max arrays, an atomic `MaxReg` at the root and register arrays,
  for any binary tree with the processes as leaves. Algorithm 4 is modelled over an atomic single-writer
  snapshot and an atomic timestamp max register.
- CSLib has no composition theorem. "Algorithm 3 over the corrected Algorithm 2" therefore follows from
  the two linearizability results only by locality of linearizability, informally.
- The bound `b` is not needed for linearizability with unbounded objects. Instead, `limited_use` shows
  that with at most `b − 1` Updates every pointer and index stays `< b`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 2 (original / corrected) | `alg P T false` / `alg P T true` | `Algorithm.lean` |
| Theorem 3.4 is false | `alg2_not_linearizable` | `Counterexample.lean` |
| Theorem 3.4 with the erratum's fix | `alg2_fixed_linearizable` | `Linearizable.lean` |
| Lemmas 3.1–3.3 (flattened) | `Inv` (`g1`, `ScanInv`, `Guard`), `lemma_3_2`, `maxScan_comparable` | `Invariant.lean`, `Linearizable.lean` |
| Max-array linearizability criterion | `exists_isLinearization_maxArr` | `Criterion.lean` |
| Lemma 3.5 / erratum | `lemma_3_5`, `lemma_3_5_erratum`, `tauSteps_le`, `opCost_le` | `Steps.lean` |
| Lemma 4.1 | `Snapshot.lemma_4_1` | `SnapshotLemma41.lean` |
| Theorem 4.2 | `Snapshot.theorem_4_2` | `SnapshotMain.lean` |
| Linearization points of §4.1 fail | `Snapshot.Counterexample.paper_linearization_points_fail` | `SnapshotCounterexample.lean` |
| `(b−1)`-limited use | `Snapshot.limited_use` | `SnapshotBounds.lean` |
| Lemma 4.3 | `Snapshot.lemma_4_3_update`, `lemma_4_3_scan`, `lemma_4_3_asymptotic` | `SnapshotCost.lean` |
| Theorem 5.1 | `Snapshot.MW.theorem_5_1`, `theorem_5_1_update_cost`, `theorem_5_1_scan_cost` | `SnapshotMW.lean` |

**Not formalized.**
- Section 6: the unlimited-use snapshot, Lemma 6.1 and Theorem 6.2.
- From Section 3.2: the adaptive unbalanced-tree costs, the swapped-cost max array and the `c`-component
  extension.
- The register implementation of `MaxReg_h`; it is taken as atomic.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Both the counterexample and the positive results are about the same concrete `Impl`
(`alg P T fix`), so the positive results are not vacuous. The model comes from CSLib
`Cslib.Computability.Distributed.SharedMemory` (`Model`, `History`, `Objects/MaxRegister`). CSLib
candidates: `exists_isLinearization_of_key`, `invPos`/`retPos` (`CriterionAux.lean`), `accCost_le_of_potential`
(`Steps.lean`) and `tauCost_add_le` (`SnapshotCost.lean`).
