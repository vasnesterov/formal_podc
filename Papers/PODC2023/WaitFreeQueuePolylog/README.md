# Wait-free Queue with Polylogarithmic Step Complexity — PODC 2023

Hossein Naderibeni, Eric Ruppert. *A Wait-free Queue with Polylogarithmic Step Complexity.* PODC 2023.
DOI [10.1145/3583668.3594565](https://doi.org/10.1145/3583668.3594565). Formalized version: arXiv
[2305.07229](https://arxiv.org/abs/2305.07229) v1 (the PODC paper plus Appendix A with the deferred
proofs); numbering follows it.

**Verdict: ⚠️ Minor statement issues.** Two typos make the algorithm of Fig. 4 wrong as printed. Line 13
never sets the `super` field of leaf blocks, and line 78 reads the wrong node's blocks. With either
typo the queue is not linearizable (Lean counterexamples). With both lines repaired as the paper's own
proofs intend, the queue is linearizable (Theorem 18) and wait-free (Corollary 23). Lemmas 9–17, 20
and 21 hold.

## Mistakes in the paper

### ⚠️ Fig. 4, line 13 (`Append` never sets `super` of leaf blocks; Invariant 3, Theorem 18)
As printed, `Append` increments `leaf.head` with a plain write instead of calling `Advance`, so the
`super` field of a leaf block stays `null` and the third claim of Invariant 3 is false for leaves
(`invariant3_false`); `IndexDequeue` then reads this `null` at line 72, and in the solo sequential
execution `Dequeue → null; Enqueue(7); Dequeue` the last `Dequeue` returns `null` instead of `7`
(`paper_not_linearizable`).

**Impact.** Theorem 18 is false for the algorithm exactly as printed. The repair is a single line,
`Advance(leaf, h)` instead of line 13, and the paper's proofs already assume it. With it, the
correctness proof goes through (`theorem_18`).

**Details.** `super` is written only at line 61, inside `Advance(v, h)`. `Advance(leaf, h)` is called only from
line 29, and only when `leaf.blocks[leaf.head] ≠ null`. That holds just between lines 12 and 13 of
the owner's `Append`. So in a solo run no leaf block ever gets a `super` value.

The proof of Invariant 3 says "only a CAS at line 63 can update a node's head field". It overlooks
the write at line 13. The proof of Lemma 12 speaks of "the call to `Advance(v, b)` that writes
`B.super`" for every block. Figure 3 gives every block a `super` field. So the intended algorithm
is clear: a leaf's head is advanced by `Advance`.

Reading `null` as `0` (Lean: `(M.sup v b).getD 0`) gives the wrong root block in the counterexample.
Any other reading of `v.parent.blocks[null]` fails as well.

A second race: if line 13 re-reads `leaf.head`, a helper's `Advance(leaf, h)` between lines 12
and 13 makes the owner write `h + 2`. That skips an index and breaks Invariant 3 again. The repair
removes this race too.

**Repair.** `Variant.fixed` keeps the index `h` written at line 12 and calls `Advance(leaf, h)` instead of
line 13 (`Pc.adv0 .app`).

### ⚠️ Fig. 4, line 78 (`IndexDequeue` counts dequeues of the wrong node)
Line 78 reads `v.blocks[…]` at indices taken from `endleft` fields, which index the blocks of the *left
sibling* (it should read `v.parent.left.blocks[…]`), so with only this typo left two concurrent dequeues
after one `Enqueue(7)` both return `7` (`line78_not_linearizable`).

**Impact.** This is a local typo. The proof of Lemma 13 states the intended computation ("all of the
subblocks of B′ from v's left sibling also precede the required dequeue"). Corrected, Lemma 13 holds
(`idxStep_spec`).

**Details.** In the counterexample, process `1`'s block is `leaf₃.blocks[1]` and its root block is
`root.blocks[2]` (`endleft = 2`, `endright = 1`). Printed line 78 adds
`leaf₃.blocks[2].sumdeq − leaf₃.blocks[1].sumdeq`, but `leaf₃.blocks[2]` is still `null`. Read
literally, this is a null dereference. The model reads a `null` block as the empty block `B₀` and
uses truncated subtraction, so the rank is `1` instead of `2`. With integer subtraction it would be
`0`, which violates the precondition of `FindResponse`. No reading gives the correct rank `2`.

### Typos and slips
- Proof of Proposition 19: "A Refresh does at most 5 CAS steps". Line 29 can call `Advance` once for
  each child, so the count is 7 (1 at line 35, 2 per `Advance` at lines 29, 29, 36). The `O(log p)`
  bound is unaffected.
- Proof of Lemma 10: "By Lemma 4, `v.blocks[h₂] = null`" should cite Invariant 3, together with
  `h₂ > h₁`.
- Proof of Invariant 7 (App. A): the second `E(v.left.blocks[0]) ⋯ E(v.left.blocks[B.endright])`
  should read `v.right`.
- Proof of Lemma 21: it takes "the earliest termination `t` of any operation contained in `B`". Such
  a termination need not exist. The fix is easy: when `B` is installed, all of its operations are
  pending (`lemma_21`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory with crash-free, deterministic processes (CSLib
  `Cslib.SharedMemory.Impl`). Linearizability and wait-freedom are CSLib's `Impl.Linearizable` and
  `Impl.WaitFree`. The object is CSLib's FIFO queue `queueObj V`, where `deq` on an empty queue
  returns `none`. An arbitrary adversary schedules all interleavings of steps.
- The base object is the whole memory: `head`, the `blocks` arrays, and the `super` fields. Every
  access to a mutable location is its own step: reading or advancing a `head`, testing or installing
  a block with a CAS, reading or CAS-ing a `super` field, and the leaf write of line 12. Reads of
  fields of blocks that are already installed are reads of immutable data. They are grouped with the
  preceding step. In particular, one level of `IndexDequeue`, all of `FindResponse` (including the
  search of line 91), and one level of `GetEnqueue` (including the binary search of line 114) are
  single steps.
- The tree uses heap numbering with height `H ≥ 1` and `np ≤ 2^H` processes (the paper takes
  `H = ⌈log₂ p⌉`). Blocks arrays are unbounded (`ℕ → Option Blk`).
- `Variant.paper` is Fig. 4 as printed and `Variant.fixed` is the repaired algorithm. All positive
  results are for `Variant.fixed`; the counterexamples use `Variant.paper` (and `⟨true, false⟩`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 18 (linearizability; repaired algorithm) | `theorem_18` | `Linearizable.lean` |
| Lemmas 15 + 17 (`L` of (3.2) linearizes every execution) | `lemma_15_17` | `Linearizable.lean` |
| Invariant 3, Lemma 4, line-50 sizes | `Shape` (proved invariant), `MInv` | `Shape.lean`, `Inv.lean` |
| Lemma 5, Cor. 6 (no operation twice) | `nodup_rootLin`, `nodup_keys_preK` | `Frame.lean`, `Seq.lean` |
| Invariant 7 | `Shape.sumenq_eq`, `Shape.sumdeq_eq` | `Shape.lean` |
| Lemmas 9, 10, 11 (double refresh propagates) | `RefCtx`/`OwnPost` cases of `stepRes` (`step_c44`, `step_r35`, `after_refresh`) | `StepProc.lean` |
| Lemma 12 (`super` is accurate) | `supOK_of` | `Helpers.lean` |
| Lemma 13 / 14 (one level of `IndexDequeue` / `GetEnqueue`) | `idxStep_spec`, `getEnqStep_spec` | `Steps.lean` |
| Lemmas 16, 17 (sizes, responses) | `runOps_batchLin`, `respIn_batchLin_deq`, `findResp_spec` | `QueueMath.lean`, `Steps.lean` |
| Cor. 23 (wait-free) | `corollary_23` | `Progress.lean` |
| Thm 22, Enqueue / null Dequeue part, and Prop. 19 (partial: `O(log p)` steps of the model) | `steps_le` (≤ `36H + 8` steps) | `Progress.lean` |
| Lemma 20 (length of the root search) | `lemma_20` | `Complexity.lean` |
| Lemma 21 (≤ 1 op per process, ≤ `c` ops and direct subblocks per block) | `lemma_21`, `lemma_21_subblocks` | `Complexity.lean` |
| Line 13 as printed: Invariant 3 false, not linearizable | `invariant3_false`, `paper_not_linearizable` | `Counterexample.lean` |
| Line 78 as printed: not linearizable | `line78_not_linearizable` | `Counterexample.lean` |

**Proof structure.** The paper's temporal arguments (Lemmas 9, 10 and 12) become invariants of
reachable configurations, using ghost variables. These record a refresh's snapshot of its children
at line 25, the parent's head when a block is installed, and the children's counts when a head
advances. They are updated alongside the run (`gstep`) and never influence the algorithm.
Linearizability then uses linearization points. Installing a root block appends that block's
operations (enqueues, then dequeues) to the linearization (CSLib `IsLinearization.push_list`). A
response is legal because the invariant tracks the response `L` gives to every process's current
operation.

**Theorem 22.** It is verified only in parts; the `O(log p · log c + log q_e + log q_d)` bound for
non-null dequeues is not proved as one statement. `steps_le` bounds the number of steps of every
operation by `36H + 8`. Each step is one access to a mutable location, plus a constant number of
reads of installed blocks, except the two search steps (lines 91 and 114). An Enqueue or a null
Dequeue does no search, so the `O(log p)` half of Theorem 22 follows. `lemma_20` bounds the
root search range by `size(bₑ) + size(b−1) + 1` blocks, which is better than the paper's
`2·size(bₑ) + size(b−1) + 1`. `lemma_21_subblocks` bounds every search of line 114 by the point
contention `c`. Two steps are left informal: the cost `O(log m)` of a doubling or binary search over
`m` monotone entries, and the conversion of `size(bₑ)`, `size(b−1)` into `q_e`, `q_d` (they differ by
at most `c`).

**Not formalized.** The bounded-space variant of Section 6 and App. B (red-black trees, garbage
collection, Theorems 31–32).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The counterexamples are checked by kernel evaluation (`decide +kernel`, no
`native_decide`). `fixed_example` and `line78_fixed_example` check that the repaired algorithm
answers correctly on the same schedules. The model comes from CSLib
`Cslib.Computability.Distributed.SharedMemory.{Model, History, LinPoints, Potential, Objects.Queue}`.
