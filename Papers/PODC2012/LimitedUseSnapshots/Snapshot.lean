import Papers.PODC2012.LimitedUseSnapshots.SnapshotMain
import Papers.PODC2012.LimitedUseSnapshots.SnapshotLemma41
import Papers.PODC2012.LimitedUseSnapshots.SnapshotBounds
import Papers.PODC2012.LimitedUseSnapshots.SnapshotCost
import Papers.PODC2012.LimitedUseSnapshots.SnapshotCounterexample
import Papers.PODC2012.LimitedUseSnapshots.SnapshotMW

/-!
# Sections 4–5: limited-use single- and multi-writer snapshots (Algorithms 3, 4)

Aspnes, Attiya, Censor-Hillel, Ellen, *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity* (PODC 2012 / J. ACM 62(1), 2015), Sections 4 and 5.

## Results

| Paper | Lean | File |
|---|---|---|
| Algorithm 3 | `Snapshot.alg3` | `SnapshotDefs.lean` |
| Lemma 4.1 | `Snapshot.lemma_4_1` | `SnapshotLemma41.lean` |
| Lemma 4.1, claim in the proof (Lines 8/10) | `Snapshot.lemma_4_1_maxUpdate` | `SnapshotLemma41.lean` |
| `seq` invariants (proof of Thm 4.2) | `SeqR.sum`, `SeqR.le`, `GInv` | `SnapshotSeq.lean`, `SnapshotInv.lean` |
| Theorem 4.2 | `Snapshot.theorem_4_2` | `SnapshotMain.lean` |
| `(b − 1)`-limited use (Sec. 4 text) | `Snapshot.indices_le_updates`, `Snapshot.limited_use` | `SnapshotBounds.lean` |
| Lemma 4.3 | `Snapshot.lemma_4_3_update`, `lemma_4_3_scan`, `lemma_4_3_update_balanced`, `lemma_4_3_asymptotic` | `SnapshotCost.lean` |
| Error: linearization points of Sec. 4.1 | `Snapshot.Counterexample.paper_linearization_points_fail` | `SnapshotCounterexample.lean` |
| Algorithm 4 | `Snapshot.MW.alg4` | `SnapshotMWDefs.lean` |
| Theorem 5.1 (linearizability) | `Snapshot.MW.theorem_5_1` | `SnapshotMW.lean` (proof: `SnapshotMWInv/Step/Up.lean`) |
| Theorem 5.1 (step complexity) | `Snapshot.MW.theorem_5_1_update_cost`, `theorem_5_1_scan_cost` | `SnapshotMW.lean` |

## Model

Asynchronous shared memory (CSLib `Impl`), deterministic processes, any number of crash-free
processes (crashes = processes that stop: safety only). The base objects are atomic: one
`maxArrObj` per internal node, one `maxRegObj` at the root, one register per `view` entry
(unbounded families indexed by `ℕ`). The tree is any binary tree whose leaves are the processes;
the balanced one has depth `≤ ⌈log₂ n⌉` (`depth_balanced_le`). Partial snapshots are vectors
`P → V` (only the components below the node matter). The local step `count_i ← count_i + 1` is
done together with the leaf write. Single-writer discipline via `Impl.allowed`.

## Differences / findings

* **The linearization points of Section 4.1 are wrong** (proof of Theorem 4.2): an `Update` with
  root pointer `d` is linearized at the first `WriteMax(root.mr, ptr ≥ d)`, but another process
  can propagate its leaf pointer to the root with a smaller root pointer `c < d` and complete a
  `WriteMax(root.mr, c)`; a later `Scan` reads `c` and returns the new value although the paper
  linearizes the `Update` after the `Scan` (3 processes, `paper_linearization_points_fail`). The
  sentence "if there is no `Update` by process `j` linearized before `op`, `count_j = 0`" is the
  false step. Theorem 4.2 itself holds: linearize an `Update` with counter `m` of process `j` at
  the first `WriteMax(root.mr, c)` with `root.seq[c]_j ≥ m` (all such updates of one step in leaf
  order).
* Lemma 4.1: the proof omits why the parent's stored index at invocation is at most the sum of
  the children's components at invocation; it follows from the `seq` monotonicity over the chain
  of max-array states (used in the Lean proof).
* Unbounded objects: linearizability needs no bound; the bound `b` is recovered separately
  (`limited_use`: with `≤ b − 1` invoked `Update`s every component, value and index is `< b`).
* Theorem 5.1: `s` (single-writer snapshot) and `timestamp` (max register) are atomic base
  objects (no composition theorem); processes `Fin n`, `n ≥ 1`. The paper's linearization points
  are correct; its remark "`op` is always linearized after it performs Line 2" is slightly
  inaccurate (it can be linearized between its `ReadMax` and its `WriteMax`, when another process
  with the same `ReadMax` value and a larger id writes `s`), which is harmless (the point is
  still after the invocation). Operations linearized at the same step: the paper orders them by
  timestamp; we put the writer's own operation last and the others (all overwritten) in id order.
* Lemma 4.3 is stated for weighted access costs (`Costs`): `Update ≤ depth·(MaxUpdate + MaxScan
  + 3) + WriteMax + 1`, `Scan ≤ ReadMax + 1`; the erratum's `O(log² b)` `MaxUpdate₁` keeps
  `O(log² b log n)`.
-/
