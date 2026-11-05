# Unbounded-Concurrency Objects — PODC 2011

Yehuda Afek, Adam Morrison, Guy Wertheim. *From Bounded to Unbounded Concurrency Objects and Back.* PODC 2011.
DOI [10.1145/1993806.1993823](https://doi.org/10.1145/1993806.1993823). Formalized version: the authors' copy of the
PODC paper (11 pages, with proofs; no arXiv version); numbering follows it.

**Verdict: 🛠️ Proof repaired.** All three results hold and are fully proved. Algorithm 1 is a wait-free
linearizable unbounded-concurrency swap. `n`-consensus objects for all `n` (with registers) give no
unbounded-concurrency consensus. The iterator stack has infinite consensus number but cannot solve
unbounded-concurrency consensus. The proof of Lemma 15 (the core of the iterator-stack impossibility) does not
work as written and needed a repaired construction; a few other proofs skip a case or a step.

## Mistakes in the paper

No mistakes in the statements.

### Typos and slips
- §4 overview: process `P₀` "with depth 0" captures the root, but in Algorithm 1 `max_depth` starts at 1, so depths
  start at 1 and the root is never captured (harmless).
- §4.1 says Line 9 looks at accessed nodes "of depth ≤ depth_i"; the pseudocode (and the proofs) use all nodes of
  depth ≤ `maxdepth_i`.
- Theorem 9's proof: "some `P_i` that returns before `P_j` starts is ordered *before* `P_j`" should read *after*.
- Lemma 14's proof: "In `e_P` (where `I[m+1]` is initially 1)" should be 2.
- Lemma 15's proof: "`o_P = write(v_P)` and `o_P = write(v_Q)`": the second is `o_Q`.

## Proof gaps (statements true)

### 🛠️ Lemma 15 (the two critical operations are not writes to the same iterator stack)
The construction that keeps the victim `R` from ever deciding can stall, and its last step can fail; the lemma is
true and we prove it with a repaired construction (`lemma_15`).

**Impact.** Statement true; the impossibility half of Theorem 11 (`no_consensus_iterator_stack`) is fully proved.

**Details.** The paper introduces new processes one by one and runs each one "until (1) it reads from `O` using an
iterator `i ∈ T`, or (2) it is about to write to `O`". Two problems:
- A process stopped at (1) is frozen forever, even if its read cannot tell the two executions apart (for instance a
  read of an iterator that has already run off the end of `V`). An algorithm can make every new process start with
  such a read. Then every new process is frozen at once, no write happens, and `R` never moves. The claim "if only
  (1) occurs, eventually all iterators in `T` become invalid … a contradiction" is false: nothing forces the
  frozen readers to read different iterators.
- After the two writes the paper schedules `R`'s read and says it "returns the value in `V[k]`". But any process may
  read any iterator, so the frozen readers may have advanced `R`'s own iterator. Two writes shift `V` by two, and
  `R`'s iterator may then point at `v_P` or `v_Q` again.

**Repair.** Freeze a new process only at a *distinguishing* read, i.e. a read whose iterator points into the two
entries holding `v_P`, `v_Q`. Such a read changes the memory identically in both executions. Keep writers pending
and execute two writes together. Re-check `R` after every frozen read: if its own read is no longer
distinguishing, let it move. Each distinguishing read strictly decreases the potential `Σ (w + 3 − pos)` over all
iterators while no write is executed, so each unblocking phase ends (`unblock`, `round`, `false_of_rel15`).
Executing writes one at a time would not obviously work: an algorithm could alternate writes with reads of `R`'s
iterator and keep `R` blocked forever.

### 🛠️ Lemma 1 (Algorithm 1: no capture in the right subtree of an unrecorded node)
The proof finds a node `u` with `v_l < u < v_r` that was accessed early and concludes that `u` lies in the right
subtree of `v` or of `v_l`; it misses the case `u = v`.

**Impact.** Statement true; repaired (`lemma1_paper`, state form `lemma1`).

**Details.** The case `u = v` is excluded because the capturer of `v` records `v` in `accessed` (Line 5) before it
starts blocking nodes, hence before `P_i` tries `v_r`. Also, the step "Lemma 1 implies wait-freedom of the capturing
phase" leaves termination implicit. It holds because successive capture attempts at a fixed depth `d` move strictly
right among the `2^d` nodes of that depth (`waitFree`).

### 🛠️ Lemma 5 and Theorem 9 (Algorithm 1: the chain)
Lemma 5's proof only shows that the input of the process with the largest captured node is not returned (not that
it is the only one), and Theorem 9 asserts without argument that Lemmas 4–8 make `⇝` a chain.

**Impact.** Statements true; repaired (`lemma5`, `theorem9_complete`, `linearizable`).

**Details.** Uniqueness follows by counting: `n` processes, `n−1` non-`⊥` returns, each value returned at most once
(Lemma 7). The chain is built by induction along the order of captured nodes: the process with the next larger
captured node returns the value of the current one. The linearization is the increasing order of captured nodes.
The paper proves linearizability for complete executions only. We extend it to all finite executions by finishing
the pending operations with solo runs (wait-freedom).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, deterministic processes, wait-freedom. Uses the CSLib-staged arrival model
  `Cslib.SharedMemory.Arrival` (`Podc/Computability/Distributed/SharedMemory/Arrival/`).
- Processes are `ℕ`, and each one performs a single invocation with its input; every step is one atomic operation
  on one base object.
- **Unbounded concurrency:** every infinite schedule is allowed, so infinitely many processes may arrive and stay
  active.
- **Bounded concurrency** (Theorem 12): the number of started-but-unreturned processes stays below a bound that
  depends on the execution and is unknown to the algorithm (`Alg2.BoundedConcurrency`).
- There is no randomness and no failure model beyond asynchrony (a process that stops taking steps has crashed).
- The impossibility results assume agreement, *weak* validity and wait-freedom. The base objects may be infinitely
  many and may start in any states.
- `c`-consensus objects: the algorithm must guarantee that at most `c` processes ever access the object
  (`AccessBounded`).
- The iterator stack (`itStack`) stores only the initialized iterators. From its initial state it behaves exactly
  like the paper's object.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `Swap.lemma1_paper` (state form `Swap.lemma1`) | `Swap/Lemma1.lean`, `Swap/WaitFree.lean` |
| Algorithm 1 wait-free (§4.2) | `Swap.waitFree` | `Swap/WaitFree.lean` |
| Lemma 2 | `Swap.Inv.lemma2` (on every reachable configuration, `Swap.inv_exec`) | `Swap/Inv.lean`, `Swap/Step.lean` |
| Lemma 3 (T&S objects accessed by ≤ 2 processes) | `Swap.Inv.tryRet_unique`, `Swap.lemma3_tst` | `Swap/Inv.lean`, `Swap/Lin.lean` |
| Lemmas 4, 5, 6 | `Swap.lemma4`, `Swap.lemma5`, `Swap.lemma6` | `Swap/Theorem9.lean` |
| Lemmas 7, 8 | `Swap.lemma7`, `Swap.lemma8` | `Swap/Lin.lean` |
| Theorem 9 (linearizable) | `Swap.theorem9_complete` (complete executions), `Swap.linearizable` (all finite executions) | `Swap/Theorem9.lean` |
| Theorem 10 | `theorem_10`; general form `no_consensus_of_rwLike_or_accessBounded` | `Theorem10.lean` |
| Algorithm 2 / Theorem 12 | `Alg2.theorem_12` (`Alg2.agreement`, `Alg2.validity`, `Alg2.bcWaitFree`) | `Alg2.lean` |
| "iterator stack has consensus number ∞" | `Alg2.solvesCons_boundedBy` | `Alg2.lean` |
| Definition 2 + Lemma 13 | `lemma_13` | `Critical.lean` |
| Lemma 14 | `lemma_14` (write/read case: `write_read_next_false`) | `Theorem11.lean`, `Lemma14.lean` |
| Lemma 15 | `lemma_15` (construction: `unblock`, `round`, `false_of_rel15`) | `Lemma15.lean` |
| Theorem 11 | `theorem_11`; impossibility `no_consensus_iterator_stack` | `Theorem11.lean` |

**Not formalized.** The unbounded F&A and snapshot objects are atomic base objects here. Their implementations from
2-consensus objects / registers ([2], [10]), and hence the composed claim "swap from 2-consensus objects", are not
formalized. The §4.1 remark replacing `max_depth` by a snapshot plus `(2k−1)`-renaming is not formalized either.
In Algorithm 1, `swap` values have any type and the output `⊥` is `none`; linearizability is our one-shot
definition `Swap.SwapLin`, tied to CSLib's `swapObj` by `Swap.swapResp_eq`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: complete executions of Algorithm 1 exist from every finite one (`Swap.exists_complete`); one consensus
object accessible to all processes solves consensus wait-free under unbounded concurrency in the same model
(`NonVacuity.consAlg_solvesCons`, `NonVacuity.lean`), so the hypotheses of Theorem 10 are jointly satisfiable and the
access bound is essential; Algorithm 2 satisfies the bounded-concurrency hypotheses (`Alg2.theorem_12`), and it is *not* wait-free
under unbounded concurrency (`Alg2.not_waitFree_infArrival`), consistent with Theorem 11.
