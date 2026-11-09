# Differences between the formalization and the paper

Paper: Attiya, Oshman, Schiller, *Space-Efficient Lock-Free Linear-Probing Hash Table*,
arXiv 2606.17315v1 (full version of the PODC 2026 brief announcement).

## Mistakes (labelled as in `mistakes-labeling.md`)

1. ❌ **Theorem 1 for CAS (Algorithm 6) is false.** The execution `cex` (2 processes, 2 cells,
   `insert(v) ∥ delete(v); insert(v)`) is valid (`cex_valid`) and has no linearization
   (`cex_not_linearizable`, `cas_not_linearizable`). Causes: `del_other_copy` (Alg. 6) marks the
   other copy (line 116) before checking that its own copy still exists (line 120); line 69 tests
   the value read at line 66, so an owner whose final CAS (line 67) is beaten by a mark does not
   revalidate; `del_copy` (line 77) resurrects only `⟨v, revalidate⟩`, not marked copies. The CAS
   proof of Lemma 7 ("only `op2` can write the cell number `i`, … `op1` overwrites this copy with
   TOMBSTONE") and the remark of Section 5.1 that a marked copy may go back to `⟨v, tentative⟩` do
   not match the code. A repair (line 77 tests `restart(val)`; after a failed CAS at line 78
   re-read at line 76) passes our model checker but is not proved in Lean, hence ❌.
2. ✏️ **Properly-paired LL/SC (Section 3, Section 4.2).** The definition requires every `LL` to
   be followed by an `SC` on the same cell, which the scans violate; the intended property (every
   `SC` is on the cell of the last `LL`, with only plain reads in between) holds by inspection of
   the code, and the model checker found the same behaviour with per-cell links and with a single
   reservation per process.

## Modelling choices

- **Shared memory.** CSLib `Impl` with one base object per cell. LL/SC version: CSLib `llscObj`
  (state = value and list of processes with a valid link; `SC` succeeds iff the caller has a valid
  link, then clears all links). This is the paper's SC semantics ("writes if `x` was not written
  since the last `LL(x)` of the process") with per-cell links. The plain reads `table[i]` of
  lines 94, 102, 105 are `VL` (they return the value and touch no link). CAS version: CSLib
  `casObject` (`read`, `cas old new`).
- **Steps.** One shared-memory access per step; the local computation in between (control flow,
  helper-function returns, `goto 48`) is folded into the step (`fsBody`, `dsBody`, …). Returning
  the response is a separate step (CSLib convention).
- **Indices.** `Fin m`, so `i + 1`, `i − 1` wrap modulo `m` as the paper states; line 51's
  `i − h(v) < j − h(v)` is `dist h v i < dist h v j` with `dist h v i = ((i − h v) : Fin m).val`.
  `m ≥ 1` (`NeZero m`).
- **Initial state.** The table starts with all cells `EMPTY` (the paper does not fix an initial
  state; Proposition 2 and Lemma 4 are stated for every reachable configuration from it).
- **Specification.** `dict K` (deterministic dictionary, state `K → Bool`) for the operation and
  response types; `dictSpec K` (CSLib `NSpec`) adds "`insert` may return `ABORT` at any time
  without changing the set" (Section 4). The response type `Res` is `ok b | abort`.
- **CAS marks.** `⟨⟨v, j⟩, marked⟩` with `j : Fin m` the cell of the marking insert (as in the
  code); "contains the key `v`" includes marked values (Section 5.1); `restart(x)` holds for
  `⟨v, revalidate⟩` and every marked copy of `v`. The model checker found the same violation
  with process identifiers in the marks.
- **Processes and keys.** Arbitrary types with decidable equality (`K` inhabited, for the
  initial local states); the counterexample uses `K = ℕ`, `P = Fin 2`, `m = 2`, `h = const 0`.

## Statements

- **Lemma 4** (`lemma4`): for every reachable configuration, two cells holding `⟨v, final⟩` are
  equal. Proved by an inductive invariant (`Inv`, `inv_of_run`) with ghost timestamps (the step
  number of each owner's last write of `⟨v, tentative⟩`, existentially quantified), not by the
  paper's case analysis on the order of the two final writes. The invariant's key fields: an owner
  that has covered (scanned past, in its current round) the cell of another owner's current
  tentative copy has an older round (`a1`, with `doc` for the window of `del_other_copy`), and no
  owner with a tentative copy covers a final copy (`a4`).
- **Proposition 3** (`prop3`): if cell `i` holds `⟨v, t⟩` (any tag `t`), every cell `j` with
  `dist h v j ≤ dist h v i` is non-empty. (The paper also counts marked copies; for the LL/SC
  version there are none.)
- **Proposition 2** (`prop2`): stated for an `insert(v)` of process `p` invoked after an arbitrary
  execution `α`, in a configuration with an `EMPTY`/`TOMBSTONE` cell and no cell containing `v`
  (any tag): if `p` returns within the continuation `γ`, some step of `γ` overwrites an
  `EMPTY`/`TOMBSTONE` cell with a tentative key (`Reclaim`). "Some available cell in the table is
  reclaimed by a key" is read as this overwrite (only line 43 overwrites an available cell,
  `writeRel`). Only the LL/SC version.
- **Lookups are wait-free** (`lookup_waitFree`): from any reachable configuration where `p` has
  a pending `lookup`, `p` performs at most `6m + 5` accesses before returning (explicit bound; the
  paper says "it is easy to see that lookup operations are wait-free"). Only the LL/SC version.

- **Lock-freedom** (`lockFree`): CSLib's `Impl.LockFree` (every infinite execution with
  infinitely many non-response steps has infinitely many responses) for finitely many processes
  (`[Fintype P]`; CSLib notes that `LockFree` is only meaningful then). Proved by a global
  potential (`pot`: a budget of possible successful `SC`s plus per-process local potentials), not
  by Lemmas 15–17 ("bounded modifying instructions unless infinitely many operations return").
  Only the LL/SC version.

## Not formalized

- Linearizability of the LL/SC version (Lemmas 5–14, the per-key linearizations `µ_v`, `π_v`,
  insert sequences, locality), the bit counts of Theorem 1, Proposition 20 and Theorem 21. The
  linearizability was checked only by explicit-state model checking for small configurations
  (no violation), see `README.md`.
- The lemmas of the CAS version other than the refuted Theorem 1.
