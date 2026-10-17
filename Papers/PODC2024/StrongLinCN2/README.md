# Strong Linearizability using Primitives with Consensus Number 2 — PODC 2024

Hagit Attiya, Armando Castañeda, Constantin Enea. *Strong Linearizability using Primitives with Consensus
Number 2.* PODC 2024. DOI [10.1145/3662158.3662790](https://doi.org/10.1145/3662158.3662790). Formalized
version: arXiv [2402.13618](https://arxiv.org/abs/2402.13618) v1, whose text and numbering are the same
as the proceedings version.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** All positive constructions we checked hold: the max register and snapshot
from fetch&add (Theorems 1, 2), readable test&set (Theorem 5), multi-shot test&set (Theorem 6) and
fetch&increment (Theorem 9). Each is strongly linearizable and wait-free or lock-free as claimed. But
**Algorithm 2, the set behind Theorem 10, is not strongly linearizable.** On the impossibility side, the
paper's **witness that `k`-out-of-order queues are `k`-ordering is wrong** (the claim itself holds with
other sequences).
The **proof of Lemma 12 has a gap** that breaks the stack case of Theorem 17.

## Mistakes in the paper

* **Theorem 10 / Algorithm 2 is not strongly linearizable** (false as proved). Take three processes:
  `put(1)`, `put(2)` and `take()`. Both puts do their `fetch&increment` (`Max = 3`). The take
  scans `Items[1..2] = ⊥`, reads `Max = 3` again and reads `Items[1] = ⊥`. Then `put(1)` writes
  `Items[1]` and **completes**; call this prefix `π`.
  - In one extension the take reads `Items[2] = ⊥` and returns `EMPTY` (double collect unchanged).
    Since `put(1)` completed and `1` is never taken, the take must be linearized before `put(1)`.
    So it already belongs to `h(π)`, with response `EMPTY`.
  - In another extension `put(2)` writes `Items[2]`, and the take reads it and returns `2`.

  So no prefix-closed linearization function exists. The paper linearizes an `EMPTY` at "its last
  read of `Max`", a point that depends on the future. (At that point both slots are still `⊥`;
  but its claim that *when the take returns* `EMPTY` every slot is `⊥` or taken fails here, with
  `Items[1] = 1` and `TS[1] = 0`.) This holds whether or not the never-incremented
  `taken_new` is read as a counter of failed test&sets. Theorem 10, a lock-free SL set from
  test&set, is therefore unproved. (`SetCE.alg2_not_stronglyLinearizable`)
* **Lemma 12's proof ignores helping** (proof gap; the stack case of Theorem 17 is unproved). The
  proof writes `f(F_i) = α·α'·β_i` with `β_i` made only of `p_i`'s decision operations. But during
  `p_i`'s solo simulation, `f` may also linearize *pending* proposal operations of other processes,
  so Definition 11 must allow them interleaved in `β_i` (our `KOrderingI`).
  - Queues satisfy this stronger definition (`KOrd.queue_kOrderingI`).
  - Stacks with the paper's sequences (`push(i)` / `pop^{n+1}`) do not, for any `d`
    (`KOrd.stack_not_kOrderingI`, `n = 3`). Process 0 observes `OK·0·1·2·ε` both when `α = push(1)`
    and a pending `push(2)` is linearized after the stack has been emptied, and when
    `α = push(2)`, `α' = push(1)·push(0)`. A lock-free SL stack (from CAS) whose `pop` on an empty
    stack first applies an announced push realizes this, and then the reduction `B` violates
    agreement (informal argument, not formalized).

  Under Definition 11 as literally stated, the stack example is correct (`KOrd.stack_kOrdering`): the
  definition is simply too weak for the lemma. The impossibility results for stacks and their
  relaxations, and the remark in §6 about stacks, are not established by the paper.
* **"`k`-out-of-order queues are `k`-ordering" fails for the given sequences** (wrong witness; the statement itself is true).
  With `prop_i = enq(i)` and `n = 3`, `k = 2`, `α = enq(1)`, the processes' own enqueues in `α'` are
  among the 2 oldest items. Then processes 0, 1, 2 can decide 0, 1, 2 respectively, so no `S_α` of
  size 2 works, for any `d` (`KOrd.ooo_not_kOrderingW`). Repair: `prop_i = enq(i)^k`, which works
  even for the strengthened definition (`KOrd.ooo_kOrderingI`).
* **Definition 11 is imprecise** (under-specified definition).
  - It requires the chosen process `ℓ` to have *completed* `prop_ℓ`. The stuttering examples only
    give that `ℓ` *started*, which is also all that validity needs.
  - Its condition `invs(α) ⊆ ⋃ invs(prop_x)` must be read per process: each process executes a
    prefix of its own `prop_j`.

  We use the repaired readings.
* **Theorem 3 (simple types) is only sketched** and not formalized. The forward simulation relates a
  configuration to *every* topological sort of `lingraph(G*)`. The step case needs sorts that extend
  earlier ones, and `lingraph`'s greedy edge insertion does not obviously provide them.
* **Typos.**
  - Algorithm 2's caption ("From test&set to fetch&increment").
  - `taken_new` is never incremented.
  - Theorem 9 says "maximum index `i` with `M[i] = 0`"; it means the minimum.
  - Theorem 17's proof says "queue" where it means "1-agreement object"; "1-agreement" and
    "1-ordering" are used interchangeably.
  - `|S_α| = k` vs `≤ k`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared memory with deterministic processes and atomic base objects (`Impl`).
  Executions are label lists, and every internal step is one base-object access.
* Crashes are modelled as processes that stop taking steps. Wait-freedom and lock-freedom are CSLib's
  `WaitFree` / `LockFree` on infinite executions.
* **Strong linearizability** (`Podc/StrongLin/Basic.lean`) follows Golab–Higham–Woelfel: a
  linearization function on finite executions with `α ≤ β ⇒ h α ≤ h β`.
  - Deterministic objects use CSLib's `IsLinearization`.
  - Nondeterministic objects (set, relaxed queues) use `NSpec` / `IsNLinearization`, where
    linearizations carry responses. The deterministic notion implies the nondeterministic one.
* Positive results are proved by a forward simulation into the atomic object (`Impl.LinSim` ⇒
  `stronglyLinearizable_of_linSim`), following the paper's linearization points, including helping
  at Theorem 5's first write and Theorem 6's `e_v`.
* Theorems 1 and 2 use the generic `OneAccess` theorem: single-access implementations with an
  abstraction relation are SL and wait-free.
* Base objects are atomic. The compositions with Theorems 1 and 5 (Corollaries 7, 8; the last step of
  Theorems 9, 10, 19) are not formalized, since CSLib has no composition theorem.
* Processes:
  - `Fin n` for Theorems 1 and 2;
  - any finite type for Theorems 5, 6, 9 (needed to list helped operations and for lock-freedom);
  - three processes for the counterexample.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 1: wait-free SL max register from fetch&add | `theorem1` | `FetchAdd.lean` |
| Thm 2: wait-free SL snapshot from (integer) fetch&add | `theorem2` | `FetchAdd.lean` |
| Thm 5: wait-free SL readable test&set from test&set + register | `RTAS.theorem5` | `ReadableTAS.lean` |
| Thm 6: wait-free SL readable multi-shot test&set from max register + readable test&set | `MTAS.theorem6` | `MultiShotTAS.lean` |
| Thm 9: lock-free SL readable fetch&increment from readable test&set | `FAI.theorem9` | `FetchInc.lean` |
| Thm 10: Algorithm 2 is SL — **false** | `SetCE.alg2_not_stronglyLinearizable` | `SetCounterexample.lean` |
| Def 11 (as stated / as needed by Lemma 12 / common weakening) | `KOrdering`, `KOrderingI`, `KOrderingW` | `KOrdering.lean` |
| Queues are 1-ordering | `KOrd.queue_kOrdering`, `KOrd.queue_kOrderingI` | `KOrdering.lean` |
| Stacks are 1-ordering: OK as stated, **fails** in the needed sense | `KOrd.stack_kOrdering`, `KOrd.stack_not_kOrderingI` | `KOrdering.lean` |
| `k`-out-of-order queues are `k`-ordering: **false**; repaired | `KOrd.ooo_not_kOrderingW`, `KOrd.ooo_kOrderingI` | `KOrdering.lean` |
| Packing lemmas (interleaved bits) | `comp_pack`, `pack_update_int` | `Packing.lean` |

Shared infrastructure (CSLib candidates):
* `Podc/StrongLin/Basic.lean`: strong linearizability, forward simulations, `NSpec`, `linResp` toolkit;
* `Podc/StrongLin/OneAccess.lean`: the single-access theorem;
* `Podc/SharedMemory/Objects.lean`: fetch&add, (readable, multi-shot) test&set, readable
  fetch&increment, max register, snapshot specs.

Also marked as CSLib candidates: `MTAS.linRespFrom_const`, `MTAS.runOps_const` and `FAI.run_range`.

**Not formalized.**
* Theorems 3, 4 (simple types; the proof is a sketch) and Corollaries 7, 8 (need a composition
  theorem).
* Lemma 12 with Claim 13, Corollary 14, Lemma 16, Theorems 17, 19, and the cited Corollaries 15, 18.
  The reduction needs one algorithm simulating another over readable base objects, plus execution
  surgery. We formalized Definition 11 and the examples instead, which is where the errors are.
* That Theorem 9's implementation is not wait-free.

**Trust.** No `sorry`. All theorems in the table use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
* The counterexample's executions are checked by kernel evaluation of a computable copy of
  `Impl.step`, proven equal to it.
* Non-vacuity: all positive theorems are about concrete implementations, and their `allowed`
  predicate is `True`, except for the single-writer snapshot. `queue_kOrdering` and `stack_kOrdering`
  show that the definitions of `k`-ordering are satisfiable.
