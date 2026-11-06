# Differences between the formalization and the paper

Paper: H. Naderibeni, E. Ruppert, *A Wait-free Queue with Polylogarithmic Step Complexity*, PODC 2023;
arXiv 2305.07229v1 (PODC paper + Appendix A with the deferred proofs + Appendix B). The proceedings
version has the same pseudocode (Fig. 4).

## Statement-level issues

1. 🔧 **Fig. 4, line 13: `Append` does not set the `super` field of leaf blocks** (`Counterexample.lean`).
   As printed, `leaf.head := leaf.head + 1` replaces `Advance`. The leaf block's `super` is set only if
   some `Refresh` of the parent runs `Advance(leaf, ·)` at line 29 between lines 12 and 13. In a solo
   run that never happens.
   - Invariant 3, third claim, is false for leaves: `invariant3_false` (solo `Enqueue(7)`, `H = 1`,
     2 processes).
   - Theorem 18 is false for the printed algorithm: `paper_not_linearizable`. In the solo execution
     `Dequeue → null; Enqueue(7); Dequeue`, the last `Dequeue` reads `null` at line 72, read as `0`.
     Line 73 then picks root block 1 and line 76 computes rank 2. `FindResponse(1, 2)` returns `null`
     instead of `7`.

   The intended version can be recovered from the paper:
   - the proof of Invariant 3 assumes that head fields change only at line 63;
   - Lemma 12's proof uses "the call to `Advance(v, b)` that writes `B.super`" for every block, leaves
     included (Lemma 13 applies Lemma 12 to the leaf);
   - Figure 3 gives every block a `super` field.

   The repair is local: one pseudocode line, `Advance(leaf, h)` in place of line 13. The paper's
   proofs reason with the repaired version.

   An implementer following Fig. 4 literally gets a non-linearizable queue.

   *Reviewer check.* Fig. 4 was rendered from both the arXiv v1 and the proceedings PDF. Both print
   line 13 as `leaf.head := leaf.head + 1`. arXiv has no later revision. `super` is written only at
   line 61. `Advance` is called only at lines 29 and 36, and line 36 never applies to a leaf. So
   nothing else sets a leaf block's `super`, and the counterexample is a solo sequential run, not a
   race.
   - The prose of Section 3.4 ("the Append writes B there and increments head") does not mention
     `Advance`.
   - The proofs reason with the repaired version, not the printed one. Invariant 3 claims non-null
     `super` for every non-root node, leaves included. Its proof says head changes "only" by the CAS
     at line 63, and Lemma 12's proof uses the `Advance` that writes `B.super`.
2. ✏️ **Fig. 4, line 78: `v.blocks` should be `v.parent.left.blocks`**
   (`line78_not_linearizable` for the variant `⟨true, false⟩`: only line 13 repaired).

   The proof of Lemma 13 describes the intended computation ("the subblocks of B′ from
   v's left sibling"), and the fix is one identifier.

   In the counterexample, the printed line 78 reads `leaf₃.blocks[2]`, which is still `null` (a null
   dereference if read literally). The model reads it as `B₀`, and truncated subtraction then gives
   rank `1`. Integer subtraction would give `0`, which violates `FindResponse`'s precondition. The
   correct rank is `2`, so every reading fails. Apart from this example, the
   `endleft` indices plainly index the left sibling's array.

## Typos and slips in proofs (no effect on the statements)

3. ✏️ Proof of Proposition 19: "A Refresh does at most 5 CAS steps". It is 7: line 29 may call `Advance`
   for both children (2 CAS each), plus line 35 and the `Advance` of line 36. The `O(log p)` claim is
   unaffected; our step count per `Refresh` is 17 (`refPos` in `Progress.lean`).
4. Proof of Lemma 10: "By Lemma 4, `v.blocks[h₂] = null` when `R₁` executes line 25" should cite
   Invariant 3, using `h₂ > h₁`.
5. ✏️ Proof of Invariant 7 (App. A): `E(v.left.blocks[0]) ⋯ E(v.left.blocks[B.endright])` should be
   `v.right`.
6. 🔧 Proof of Lemma 21: "the earliest termination `t` of any operation contained in `B`" need not
   exist. We prove instead that, when `B` is installed, all its operations are pending: a completed
   operation is already in an earlier block of every node on its path, and Corollary 6 rules out a
   second block (`lemma_21`).
7. Lemma 20: we prove `b − bₑ ≤ size(bₑ) + size(b−1) + 1`, slightly better than the paper's
   `2·size(bₑ) + size(b−1) + 1` (no dequeue between `bₑ` and `b` is null). This is not an error.

## Modelling choices

- **Granularity of steps.** Every access to a mutable shared location is its own step: `head`,
  entries of `blocks` (tested at line 28, installed at line 35 and written at line 12), and `super`
  (read at line 72, CAS at line 61). Reads of fields of already installed blocks read immutable data
  (Section 4.1) and are grouped with the previous step:
  - line 2 / 6 reads `leaf.head` (`app0`) and then the immutable block `leaf.blocks[h−1]` (`app1`);
  - lines 44–56 form one step (`c44`): the read of `v.right.head` followed by reads of installed
    blocks;
  - one level of `IndexDequeue` (lines 71–80) is one step: the `super` read followed by reads of
    installed blocks;
  - `FindResponse` (lines 85–93), including the doubling and binary search of line 91, is one step;
  - one level of `GetEnqueue` (lines 101–116), including the binary search of line 114, is one step.

  The values read are the same whenever the immutable reads happen, so these groupings do not change
  any response. The search lengths are bounded separately (`lemma_20`, `lemma_21_subblocks`).
- **Local copies of `leaf.head`.** Line 12 writes `leaf.blocks[h]` with `h` read at line 2/6. Line 8
  uses `h` instead of re-reading `leaf.head − 1`. In the repaired algorithm both re-reads give `h` (only
  the owner installs leaf blocks, and `Advance(leaf, h)` sets `head = h + 1` before `Propagate`).
- **Repaired line 13** (`Variant.fixed`): `Advance(leaf, h)` with the `h` of line 12.
- **Natural numbers.** All integer fields are `ℕ`, and subtraction truncates. Every subtraction in
  the repaired algorithm is of a smaller value from a larger one, so the results equal the integer
  ones. The two exceptions coincide with the paper anyway: line 50's `max(0, ·)`, and `size`, which
  is exactly a truncated subtraction.
- **`null` reads in the repaired algorithm.** The model reads a `null` block as `B₀` (`Mem.bk`).
  For `Variant.fixed`, every block that a step reads is installed. This follows from the invariant:
  `Shape.inst` together with the `b ≤ cnt` bounds of `PInv` at `idx`, `fr` and `ge`, and with
  `MInv.supSet` for `super`. It is not stated as a separate theorem. So `theorem_18` does not hide
  a null dereference of the paper's algorithm.
- **`null`.** Missing blocks are `none` (`Option`). The `element` field is `Option V`, so enqueuing
  any value (also one playing the role of `null`) is unambiguous. A `null` `super` read at line 72 is
  used as `0`; this matters only for the printed algorithm.
- **Tree.** Heap numbering of a complete binary tree of height `H ≥ 1` with `np ≤ 2^H` processes
  (unused leaves stay empty). The paper's `H = ⌈log₂ p⌉` is the case `np = p`. `p = 1` needs `H ≥ 1`
  here; the paper's height-0 tree has no `leaf.parent` (degenerate, ✏️).
- **Searches.** `findFirst f x lo hi` is the least index in `[lo, hi]` with `x ≤ f(j)` (`hi` if none).
  It is the result of the doubling/binary searches; their cost is not modelled.
- **Ghost state.** The invariant uses ghost variables (`Ghost`, `gstep`) computed from the run. The
  implementation `queueImpl` itself has none.
- **Specification.** CSLib `queueObj V`: `enq v` returns `none`, and `deq` returns the oldest element
  or `none` if the queue is empty. Linearizability is CSLib's `IsLinearization` (the amended
  Herlihy–Wing definition: completed operations must be in `L`, real-time order is respected, and
  responses are legal) for every finite execution. Wait-freedom is CSLib's `WaitFree` (in every
  infinite execution a pending process takes finitely many steps).
- **Point contention.** `pendingSet β` is the set of processes with a pending operation after the
  prefix `β`. `c` is any bound on its size over all prefixes.

## Partially formalized

- **Theorem 22.** The `O(log p)` bound for Enqueue and null Dequeue follows from `steps_le`: these
  operations do no search, and each step does `O(1)` accesses. The bound for non-null Dequeue is
  only partly proved, as listed below.
  - `steps_le`: every operation takes at most `36H + 8` steps of the model.
  - `lemma_20`: the root search range has length at most `size(bₑ) + size(b−1) + 1`.
  - `lemma_21_subblocks`: each binary search of line 114 ranges over at most `c` blocks.

  Not formalized: the cost of a doubling or binary search over `m` monotone entries (`O(log m)`
  reads), and the comparison between `size(bₑ)`, `size(b−1)` and the paper's `q_e`, `q_d` (sizes
  at the linearization points, which differ by at most the number of operations in a block, `≤ c`).
- **Proposition 19.** Follows from `steps_le`: each step does at most one CAS. Not stated
  separately.

## Not formalized

- Section 6 / Appendix B: the bounded-space variant (persistent red-black trees, garbage
  collection, `last` array, helping) and Theorems 31–32.
- The informal claims about Java GC and word sizes.
