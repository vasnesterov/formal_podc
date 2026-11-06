# Differences between the formalization and the paper

Afek, Morrison, Wertheim, *From Bounded to Unbounded Concurrency Objects and Back*, PODC 2011
(author copy of the PODC version, 11 pages, proofs included).

No checked statement is false; the proof of Lemma 15 is broken as written (repaired), and Lemmas 1, 5 and Theorem 9
have smaller gaps. Typos (Lemma 14/15 proofs, §4 overview/§4.1 prose, Theorem 9 proof) have evident intent.

## Common model (Sections 3, 5)

- Model: `Cslib.SharedMemory.Arrival` (staged in `Podc/`): processes `ℕ`, deterministic, each one
  starting with its input (an input vector `x : ℕ → X` fixed up front; the paper's processes "arrive" — a
  process arrives at its first step, which is equivalent). One process = one invocation, as in the paper
  ("we think of each new invocation as coming from a new process"). Each step is one atomic operation on one
  base object; local computation is folded into the continuation.
- Unbounded concurrency = every infinite schedule is admissible (`infArrival`); wait-freedom = every process that
  takes infinitely many steps eventually outputs. Bounded concurrency (`Alg2.BoundedConcurrency`): the number of
  processes that have taken a step and not yet output is bounded along the execution, by a bound depending on
  the execution and unknown to the algorithm — the paper's definition.
- Consensus: agreement for all processes that took a step, validity (the impossibility results assume only *weak*
  validity — all inputs equal `v` ⇒ output `v` — which makes them stronger). Binary inputs for the
  impossibility results, arbitrary input type for Algorithm 2.
- Base objects of an algorithm may be initialized arbitrarily and there may be infinitely many of them
  (the paper fixes initial states; allowing more only strengthens the impossibility results).

## Theorem 10

- **Non-vacuity** (`NonVacuity.lean`, `consAlg_solvesCons`): with one consensus object accessible to *all* processes,
  agreement, validity and wait-freedom under unbounded concurrency hold in our model; the impossibility therefore
  comes from the access bound `AccessBounded`, not from the encoding.
- **Statement generalized.** `no_consensus_of_rwLike_or_accessBounded`: every base object is either read/write-like
  (`ObjSpec.RWLike`: each operation is read-only or a blind overwrite; registers of any value type) or accessed by at
  most `c` processes in every execution (`AccessBounded`), whatever its specification. `theorem_10` is the paper's
  special case: registers and `c`-consensus objects (`consObj`, multivalued) with bounds `c` depending on the object.
- "A `c`-consensus object can be accessed by at most `c` processes" is modelled as a requirement on the algorithm
  (`AccessBounded A i c`: in every execution at most `c` distinct processes apply an operation to `i`). The proof
  only uses the consequence that at most `c` processes can be simultaneously poised on it (`AccessBounded.card_le`).
  A different reading (the object answers arbitrarily after `c` accesses, as `consₙ` in PMB'20) is not covered.
- Proof: as in the paper (growing chain of `n`-critical executions, w.r.t. the processes `p₀, …, p_{n-1}`, rather
  than arbitrary finite sets `P`); the "standard valency arguments" are `exists_crit` (CSLib-staged) and
  `crit_same_object`/`rw_pair` here. No gap.

## Theorem 11, Lemmas 13–15

- **Model of the impossibility.** The paper does not list the base objects of algorithm `A` in Section 5.3; its
  case analysis covers "atomic register read or write, or iterator stack read or write". We take any family of
  read/write-like objects (registers) and iterator stacks (`ST B W`, indexed by `R ⊕ S`).
- **Iterator stack** (`IteratorStack.lean`). The paper's infinite iterator sequence `I` (0 = uninitialized) is
  stored as the list of initialized iterators (in every reachable state these are exactly the first `m`, `m` = number
  of writes); iterators are numbered from 0 (the paper: from 1). From the initial state the object behaves exactly as
  the paper's. Arbitrary initial states of our object (allowed by the model) include states with a position `0`
  inside the list; such iterators are incremented on reads (the paper never has them).
- **Theorem 11** (`theorem_11`) is stated as a conjunction: for every `n`, Algorithm 2 solves `n`-process consensus
  (registers + one iterator stack; "infinite consensus number"), and no algorithm from read/write-like objects and
  iterator stacks solves binary consensus wait-free under unbounded concurrency (`no_consensus_iterator_stack`).
- **Valency** (`Uni`): w.r.t. all extensions by any processes, as in the paper. `Uni α v` means "no extension decides
  `¬v`"; with wait-freedom this is `v`-valency.
- **Definition 2 / Lemma 13** (`lemma_13`): stated as the existence of `α, P, Q, v` with `α P` only `v` and `α Q P`
  only `¬v`. Bivalence of `α` and `P ≠ Q` follow (`lemma_14` proves `P ≠ Q`). The proof follows the paper
  (alternate solo runs of `P` with walks along an extension of opposite valency); the paper's remark "each step in
  `L₁` but the last keeps the system in a bivalent state" is not true for an arbitrary `L₁` but is not needed.
  The paper's proof starts from "a bivalent state `s₀`"; we construct it (input `false` for `p₀`, `true` for `p₁`,
  weak validity).
- **Lemma 14** (`lemma_14`): stated as in the paper ("both are writes to the same iterator stack"), including the
  preceding paragraph's case analysis (different objects, registers, two reads). The contradictions "`s_P` and `s_Q`
  would be indistinguishable" are made precise by running a *fresh* process (`false_of_mem_eq`): the local states of
  `P`, `Q` (and of `R`) do differ. The register case is Herlihy's argument for any read/write-like object.
  The write/read-of-next-iterator case is `write_read_next_false`; typo: "In `e_P` (where `I[m+1]` is initially 1)"
  should be 2.
- **Lemma 15** (`lemma_15`): statement as in the paper (typo: "`o_P = write(v_Q)`" should be `o_Q`). The proof
  is broken as written and needed a new construction (🛠️):
  1. the paper freezes every new process at its first read "using an iterator `i ∈ T`", even a read that cannot
     distinguish the executions (e.g. of an exhausted iterator). Then all new processes may be frozen forever
     without any write and without moving `R` — the claim "if only (1) occurs, then eventually all iterators in `T`
     become invalid … a contradiction" is false (nothing forces reads of different iterators);
  2. after two writes the paper lets `R` read "the value in `V[k]`", but the frozen readers may have advanced `R`'s
     own iterator (any process can read any iterator), so that after the two writes it points to `v_P`/`v_Q` again.
  Repair (`unblock`, `round`, `false_of_rel15`): freeze only at *distinguishing* reads (iterator position in the
  two-entry window holding `v_P, v_Q`); keep writers pending and execute two writes at once (executing one write at
  a time would not suffice: alternating writes and reads of `R`'s iterator would keep `R` blocked); re-check `R`
  after each frozen read. Termination: the potential `Σ (w + 3 − pos)` over iterators strictly decreases with each
  distinguishing read while no write is executed.
- The final contradiction is with wait-freedom of `R` in the limit execution (infinitely many processes,
  infinitely many frozen and hence active forever — unbounded concurrency), as in the paper.

## Theorem 12 (Algorithm 2), file `Alg2.lean`

- Objects: register `result` (initially `⊥`) and one iterator stack; the paper's local "atomic registers" `last`,
  `itr`, `cur` are local variables. Line 6 returns the local `last` instead of re-reading `result` (by agreement the
  same value). Unreachable branches (`last = ⊥` at line 5, ill-typed responses) are given arbitrary continuations;
  the invariant proves they never occur.
- Agreement and validity are proved for all finite executions (any concurrency).
- Wait-freedom (`bcWaitFree`) under bounded concurrency. The paper's one-sentence argument ("before `result` is
  written, only a finite number of processes can participate … so only a finite number of values can be written") is
  correct but terse: a process that read `result = ⊥` may write to the stack *after* `result` is written; the
  count works because all stack writers are active simultaneously just before the first write of `result`
  (`pot_le_active`, `pot_bound`). Loop termination also uses that each iterator is read only by its owner and that an
  iterator position is at most `|V| + 1`. Proof remarks, not gaps.
- Extra (not in the paper): `not_waitFree_infArrival`, Algorithm 2 is not wait-free under unbounded concurrency.

## Section 4 (Algorithm 1, swap), folder `Swap/`

- **Model.** Each process performs one `swap(x p)`; invocation = first step, response = output state. Base objects
  are atomic: `max_depth` F&A over `ℕ` initialized to 1 (as in the pseudocode), the unbounded snapshot `accessed`
  (`snapObj`: cell `d` = last node posted by the depth-`d` process, `scan` returns the whole array), and per tree
  node a register (values `Option V`) and a test-and-set (CSLib convention: returns the old bit, "win" = `false`).
  The implementations of F&A/snapshot from 2-consensus objects/registers ([2], [10]) are not formalized, so "swap
  from 2-consensus objects" is verified only modulo these (atomic) objects.
- **Tree.** Nodes `(depth d, index k < 2^d)`, in-order given by the dyadic key `(2k+1)/2^(d+1)` (`Swap/Tree.lean`).
- `NextUnaccessedNodeAtDepth` with an empty candidate set: the process keeps re-scanning (stuck), so wait-freedom
  genuinely needs Lemma 1 (`Inv.next_ne_none`). Line 9's bound is the value `maxdepth_i` read at Line 7, over all
  nodes of depth ≤ `maxdepth_i` (the pseudocode); §4.1's prose says "depth ≤ depth_i" (slip).
- Overview text: "process `P₀` that obtained depth = 0" captures the root; with `max_depth` initialized to 1 depths
  start at 1 and the root is never used. Harmless (slip).
- **Lemma 1** (`lemma1_paper`, as stated: whenever a process holds `cap = w` with `w` in the right subtree of `v`,
  `update(v)` has been executed; state form `lemma1`). Proof gap: the case `u = v` (resp. `cap_j = v`) is missing;
  excluded because the capturer of `v` posts `v` before blocking (🔧: proof gap, statement true).
- **Wait-freedom** (`waitFree : WaitFree (alg V) infArrival`): the paper's "Lemma 1 implies wait-freedom of the
  capturing phase" leaves termination implicit (captures at a fixed depth move strictly right among `2^d` nodes);
  proved with a lexicographic progress measure.
- **Lemma 2** (`Inv.lemma2`): stated for reachable configurations (via the invariant `inv_exec`).
- **Lemma 3**: second half `Inv.tryRet_unique`; the consequence used in the paper (each T&S accessed by ≤ 2
  processes) is `lemma3_tst`. No circularity with Lemma 1 (Lemma 1 uses only the trivial first half).
- **Lemmas 4–6** assume a complete execution (as the paper says); Lemmas 4 and 5 also need at least one process
  (degenerate). **Lemma 5**: the paper proves only that `P_big`'s input is not returned; uniqueness follows from the
  chain structure / counting (proof gap, 🔧). **Lemma 8** is `¬ TransGen RetFrom p p`.
- **Theorem 9.** Linearizability is our definition `SwapLin` (one-shot swap with infinitely many processes: a
  duplicate-free list of processes of σ containing all completed ones, the `j`-th completed returns `⊥` for `j = 0`
  and the input of the `(j−1)`-th otherwise, real-time order respected); tied to CSLib's `swapObj` sequential
  specification by `swapResp_eq`. The paper's "Lemmas 4–8 give a chain" is not argued (done by induction along the
  order of captured nodes); "ordered before `P_j`" should read "after" (slip). The paper proves only complete
  executions and asserts the general case; `linearizable` proves every finite execution (pending operations
  completed by solo runs).
