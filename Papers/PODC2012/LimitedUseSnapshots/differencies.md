# Differences between the formalization and the paper

Paper: J. Aspnes, H. Attiya, K. Censor-Hillel, F. Ellen, *Faster than Optimal Snapshots (for a While)*,
PODC 2012 (proceedings, 9 pp.), journal version *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity*, J. ACM 62(1):3, 2015 (author copy, 21 pp.), and the authors' erratum to the journal version.
Numbering follows the journal version (the proceedings version numbers the same results Lemma 1–3,
Theorem 4, …).

## Errors in the paper

1. **Theorem 3.4 is false: Algorithm 2 is not linearizable** (journal Theorem 3.4 = proceedings
   Theorem 4; both versions have the same Algorithm 2, checked on the rendered proceedings page 3 and
   the journal pseudocode). `alg2_not_linearizable` (`Counterexample.lean`): for `k = 3` with the paper's
   balanced tree (`m = ⌈3/2⌉ = 2`, `Shape.balanced 3 = T3`, `balanced_three`), any `h ≥ 2` (the value `1`
   is written to the second component) and three processes, the 17-label execution `badExec` (validity
   checked by `decide`) has no linearization. It is the erratum's execution: `p₀` starts `MaxScan`,
   reads `r.second = 0` and `r.switch = 0`; `p₁` runs `MaxUpdate1(r, 1)` to completion; then `p₂` runs
   `MaxUpdate0(r, 1)` to completion; `p₀` finishes and returns `(1, 0)`. Since `MaxUpdate1(r,1)` precedes
   `MaxUpdate0(r,1)` in real time, a scan seeing the first component `1` must see the second component `1`.
   *Rule.* A numbered theorem about the paper's algorithm, false for a small non-degenerate instance
   (R2 does not apply: `k = 3`, three processes), and not a typo (R3: the fix adds a step to the
   algorithm and changes its step complexity) → ❌. *Borderline (R5/R6).* The abstract calls the max
   array "the key to this implementation", but the headline result (title, first sentence of the
   abstract: "a novel implementation of a snapshot object … with O(log² b log n) step complexity for
   update operations and O(log b) … for scan operations") is the limited-use snapshot of Section 4;
   Theorem 3.4 is the tool. The headline names the paper's specific algorithm (Algorithm 3 over
   Algorithm 2), but it is only *unestablished*, not refuted: its proof uses the false Theorem 3.4,
   and no counterexample to the snapshot is known (item 2). R5: unestablished headline → ❌. Even if
   the max array itself counted as a headline, it is an existential claim (a new object with a
   polylogarithmic scan), and the erratum's repair exists with `MaxScan` cost unchanged and
   `MaxUpdate1` still polylogarithmic → ❌ by R5's existential exception. Hence ❌, not 🚨.
   *Credit.* The error and the execution are the authors' own (erratum to the J. ACM version); the
   formalization confirms them. The new findings are items 4 and the remarks on the erratum below.
   *Where the proof breaks* (as the erratum says): the proof of Theorem 3.4 orders scans correctly
   among themselves and orders each update correctly w.r.t. scans, but never orders `MaxUpdate0`
   operations against `MaxUpdate1` operations.

2. **Theorem 4.2's proof relies on Theorem 3.4** ("`u.ma` is a linearizable max array"). With the
   erratum's corrected max array the composition is sound (Theorem 4.2 is proved here with *atomic* max
   arrays; substituting the corrected Algorithm 2 is the usual locality-of-linearizability argument,
   which CSLib does not formalize). Note that Algorithm 3 already performs a `MaxScan` right after every
   `MaxUpdate1` (lines 10, 12), which is exactly the erratum's line 9.5, so the snapshot may well be
   linearizable even with the original Algorithm 2; we did not check this.

3. **Lemma 3.5 (step complexity) is correct for Algorithm 2 as published, but not for the corrected
   (linearizable) algorithm**: `MaxUpdate1` then costs `O(log k · log h)` instead of `O(log h)` (as the
   erratum says). Both versions are proved (`lemma_3_5`, `lemma_3_5_erratum` in `Steps.lean`). The
   abstract's bounds `O(log² b log n)` per Update and `O(log b)` per Scan survive, since an Update already
   performs a `MaxScan` (cost `O(log² b)`) at every level.

## Proof gaps (statements true)

4. **Theorem 4.2: the linearization points of Section 4.1 are wrong** (not mentioned in the erratum). The paper linearizes an `Update`
   whose root pointer is `d` at the first `WriteMax(root.mr, ptr)` with `ptr ≥ d`. Another process can
   carry the updater's new leaf pointer to the root inside a *smaller* root pointer `c < d` and complete
   `WriteMax(root.mr, c)`; a `Scan` that reads `c` then returns the new value although the paper
   linearizes the `Update` after that `Scan` (`Snapshot.Counterexample.paper_linearization_points_fail`,
   3 processes: every linearization of the execution must put the `Update` before the `Scan`). The false
   step is "if there is no `Update` by process `j` linearized before `op`, `count_j = 0`". Rule R1: a
   claim inside a proof of a true theorem → 🛠️. Repair: linearize an `Update` of process `j` with counter
   `m` at the first `WriteMax(root.mr, c)` with `root.seq[c]_j ≥ m` (several at one step in leaf order);
   `Snapshot.theorem_4_2` uses these points.
5. **Lemma 4.1**: the proof does not justify that the parent's stored index at the invocation is at most
   the sum of the children's components at that time; it follows from the monotonicity of `seq` along the
   chain of max-array states (used in `Snapshot.lemma_4_1`). 🛠️ (minor).

## Remarks on the erratum

- The erratum's description of the fix has a slip: "Forcing each `MaxUpdate0(r, v)` to perform an embedded
  `MaxScan(r)` operation after its `WriteMax(r.second, v)`" — `WriteMax(r.second, v)` is line 9 of
  `MaxUpdate1`; the intended fix (and the one formalized) embeds the scan in `MaxUpdate1`, as the erratum's
  own step-complexity paragraph confirms.
- The erratum's linearization of `MaxUpdate1(r, v)` ("after its invocation and immediately before any
  (perhaps embedded) `MaxScan(r)` returns a value `≥ v` for component 1") is only a sketch: it mixes a
  real-time point ("returns") with the value order of the scans and does not say which of several scans
  returning `≥ v` is meant. (A completed `MaxUpdate1` always has such a scan, its embedded one; a pending
  one without such a scan may be dropped, so this case is harmless.) It is repairable, not wrong. We do
  not follow it. Our linearization (`Criterion.lean`) orders
  completed scans by (sum of the result, response position) and puts every invoked update immediately
  before the first scan that is "good" for it (the scan follows every scan preceding the update and sees
  the update and everything preceding it); updates with no good scan go to the end (a pending update with
  no such scan can always be placed last).

## Modelling choices

- **Model.** Asynchronous shared memory, CSLib `Cslib.SharedMemory.Impl` (deterministic processes,
  atomic base objects, any set `P` of processes, executions = arbitrary interleavings; crashes are
  implicit: a process may stop taking steps; linearizability = CSLib `Impl.Linearizable`, the amended
  Herlihy–Wing definition with pending operations completed or dropped).
- **Base objects of Algorithm 2.** The 1-bit `switch` registers are atomic registers; the `MaxReg_h`
  objects `second` at every node are taken as **atomic** max registers over `ℕ` (CSLib `maxRegObj`), as the
  paper itself treats them in the proof of Theorem 3.4 (it uses only their linearizability). Hence the
  range `h` plays no role in the correctness statements; in the step-complexity statements the cost of a
  `MaxReg_h` access is a parameter `ch` (`⌈log₂ h⌉` for the balanced max register of Aspnes et al.).
- **The recursion is flattened** over a binary tree `T : Shape` whose leaves are the values of the first
  component (`k = T.size`); the split point `m` of a node is the size of its left subtree. All results
  (positive and negative) are for every tree shape where the paper only fixes `m = ⌈k/2⌉` in the
  pseudocode (and remarks that any tree works); the counterexample uses the balanced tree for `k = 3`.
- `MaxUpdate0(r, v)` may only be invoked with `v < k` (`Impl.allowed`); `MaxUpdate1` with any `v ∈ ℕ`.
  Updates return the dummy response `(0, 0)`.
- **Right steps of `MaxUpdate0` take no step**: lines 5–6 (`v ≥ m`: recurse into `r.right`) access no
  shared object, so the local state machine skips them (`d0Act`); line 7 is performed on the way back up
  (`upAct`, `deepRight`). This is exactly the paper's recursion.
- **Specification.** `maxArrObj` (`Spec.lean`): state `ℕ × ℕ`, `upd0 v`/`upd1 v` take the componentwise
  max, `scan` returns the state. The bounded ranges of the paper are enforced by `allowed`.
- **Linearizability proof architecture.** Instead of the paper's induction on `k` with linearizable
  sub-objects (CSLib has no composition theorem), we prove a history-level criterion for max arrays
  (`exists_isLinearization_maxArr`) and an invariant of the flattened algorithm (`Invariant.lean`,
  `inv_of_run`) from which the criterion's hypotheses follow. The invariant contains the paper's
  Lemmas 3.1–3.3 in flattened form: Lemma 3.2 = `Inv.g1` / `lemma_3_2`; Lemma 3.3 = the lower bound `lb`
  in `ScanInv` (`sc D [] ≤ lb` for the configuration `D` at the invocation); Lemma 3.1 = `Guard`/`RG`
  (the left child of a node a scan passed to the right, and every pending left propagation at it, stay
  below the scan's lower bound). The chain property of the proof of Theorem 3.4 is `maxScan_comparable`.
- **Section 4 (Algorithm 3)** is formalized with atomic base objects: one `maxArrObj` per internal node,
  one `maxRegObj` at the root, one register per `view` entry (unbounded families indexed by `ℕ`). The
  limit `b` is not needed for linearizability; `Snapshot.limited_use` / `indices_le_updates` show that
  with at most `b − 1` invoked `Update`s every max-array component, `root.mr` value and array index is
  `< b`, so `MaxArray_{b×b}`, `MaxReg_b` and arrays of length `b` suffice. Any binary tree whose leaves are
  the processes (`T.WF`); the balanced one has depth `≤ ⌈log₂ n⌉`. Partial snapshots are vectors `P → V`.
  `count_i ← count_i + 1` (line 2) is merged with the leaf write (line 5); `count_i` is local, so this is
  invisible to other processes.
- **Lemma 4.3** is stated for weighted base-object costs (`Costs`): `Update ≤ depth·(MaxUpdate + MaxScan +
  3) + WriteMax + 1`, `Scan ≤ ReadMax + 1`; `lemma_4_3_asymptotic` gives `O(log² b · log n)` with the
  (corrected) max-array costs.
- **Theorem 5.1 (Algorithm 4)**: the single-writer snapshot `s` and the timestamp max register are atomic
  base objects; processes `Fin n`, `n ≥ 1`. The paper's linearization points are correct; its remark
  "`op` is always linearized after it performs Line 2" is slightly inaccurate (it can be linearized
  between its `ReadMax` and its `WriteMax`), harmlessly. Operations linearized at the same step: the
  paper orders them by timestamp; we put the writer's own operation last and the others (overwritten) in
  id order.
- **Composition.** CSLib has no theorem substituting a linearizable implementation for an atomic base
  object; the end-to-end claim "Algorithm 3 over the corrected Algorithm 2 is linearizable" follows from
  `theorem_4_2` and `alg2_fixed_linearizable` by locality of linearizability, informally.
- **Not formalized**: Section 6 (unlimited-use snapshots, Lemma 6.1, Theorem 6.2), the unbalanced-tree
  adaptive costs `O(log v₁ log v₂)`, the swapped-cost max array and the `c`-component extension of
  Section 3.2, and the implementation of `MaxReg_h` from registers (taken atomic).
- Lemmas 3.1–3.3 are not stated separately for the *original* algorithm; they hold there too (the paper's
  proofs are correct), but only the corrected algorithm's invariant is formalized.
