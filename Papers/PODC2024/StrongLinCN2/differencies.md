# Differences between the formalization and the paper

Attiya, Castañeda, Enea. *Strong Linearizability using Primitives with Consensus Number 2.* PODC 2024
(arXiv 2402.13618v1, the same text as the proceedings version).

Classification: **false statement** / **false only in a degenerate case** / **proof gap (statement true or
repairable)** / **under-specified definition** / **typo** / **modelling choice**.

## Errors and gaps

1. **Theorem 10 / Algorithm 2 (set from test&set): false as proved.** Algorithm 2 is not strongly
   linearizable, whether or not `taken_new` is incremented. We use three processes. `p₀` runs `put(1)` and
   `p₁` runs `put(2)`; both do their `fetch&increment`, so `Max = 3`. `q` runs `take()`. It finishes a
   whole first iteration with `Items[1] = Items[2] = ⊥`, reads `Max = 3` again and reads
   `Items[1] = ⊥`. Then `put(1)` writes `Items[1]` and returns. Call this prefix `π`. In the
   extension `B`, `q` reads `Items[2] = ⊥` and returns `EMPTY` (its double collect succeeds). Since
   `put(1)` completed in `π` and `1` is never taken, `q`'s `take` must precede `put(1)` in the
   linearization. So it already belongs to `h(π)`, with response `EMPTY`. In the extension `A`,
   `put(2)` writes `Items[2]` and `q` takes `2`. This contradicts the entry of `h(π)`. The paper's
   proof places a `take → EMPTY` at "its last step that reads `Max`", which depends on the future. At
   that point both slots are still `⊥`; but the proof's claim that *when a take returns empty* every
   slot is `⊥` or taken is false here: `Items[1] = 1` and `TS[1] = 0` at the return. The flaw does not
   depend on the `taken` test: the take sees no non-`⊥` slot, so even a classic double collect
   comparing the read `Items` values returns `EMPTY` here.
   Theorem 10 (a lock-free strongly-linearizable set exists from test&set) is therefore **unproved**,
   and Figure 1's arrow to "set" is unsupported. We did not study whether another algorithm works.
   **False statement (as proved).** (`SetCE.alg2_not_stronglyLinearizable`)
2. **Section 5: "`k`-out-of-order queues are `k`-ordering": false for the given sequences.** The
   paper takes `prop_i = enq(i)`, `dec_i = deq`, and `S_α` = the inputs of the first `k` enqueues of
   `α`. When `α` has fewer than `k` enqueues, the `k` oldest items include items enqueued in `α'`,
   which depend on `i`. Example with `n = 3`, `k = 2`, `α = enq(1)`: process `i ∈ {0, 2}` may enqueue
   `i` and dequeue `i`. Together with process 1 (which dequeues 1), this forces `|S_α| ≥ 3`, for every
   choice of `d`. **Wrong witness (proof error); the claim itself is true.** It is repaired by `prop_i = enq(i)^k`
   (`KOrd.ooo_not_kOrderingW`; repair: `KOrd.ooo_kOrderingI`). With the paper's sequences, Theorem 19
   is not established for `k`-out-of-order queues with `k ≥ 2`. With the repaired sequences the
   reduction applies (modulo item 3, which the repair survives).
3. **Lemma 12, proof gap: linearizations of other processes' pending operations.** In the proof,
   `f(F_i) = α · α' · β_i` with `invs(β_i) = dec_i`. But `F_i` extends `E_i*|A`, in which other
   processes may have pending operations of `prop_j`. A strong linearization function may linearize
   them *during* `p_i`'s solo simulation of `dec_i` (helping). So `f(F_i) = α · α' · γ`, where `γ`
   interleaves `dec_i` with up to one operation of `prop_j` per other process `j`. Definition 11 does
   not cover such `γ`. The fix is to strengthen Definition 11 accordingly (`KOrderingI`).
   * Queues (and `k`-out-of-order queues with the repaired sequences) satisfy the strengthened
     definition (`KOrd.queue_kOrderingI`, `KOrd.ooo_kOrderingI`). So Theorem 17 for queues stands,
     modulo the unformalized parts of Lemma 12.
   * **Stacks do not, with the paper's sequences** (`prop_i = push(i)`, `dec_i = pop^{n+1}`), for any
     `d` (`n = 3`). Process 0 sees `OK · 0 · 1 · 2 · ε` in two scenarios. In the first, `α = push(1)`,
     `α' = push(0)`, and the pending `push(2)` is linearized after the stack has been emptied. In the
     second, `α = push(2)` and `α' = push(1) · push(0)`. Then `d` would have to equal both 1 and 2
     (`KOrd.stack_not_kOrderingI`). The scenario is realizable (informal argument, not formalized). Take a lock-free strongly-linearizable
     stack from CAS and registers in which a `pop` that finds the stack empty first applies an
     announced pending `push` (linearization points at successful CASes). Algorithm `B` of Lemma 12
     then violates agreement. Hence the impossibility for stacks (Theorem 17 for stacks, its
     relaxations, and the remark in §6 that a stack has no wait-free SL implementation from CN-2
     primitives) is **not established** by the paper's argument. Under Definition 11 *as stated*, the
     stack example itself is correct (`KOrd.stack_kOrdering`): the definition is too weak for the
     lemma. **Proof gap; for stacks, the claimed consequence is unproved.**
4. **Definition 11 vs. its examples: the chosen process `ℓ`.** Definition 11 requires
   `invs((α·α')|ℓ) = prop_ℓ` (ℓ completed its proposal sequence). The stuttering queue/stack examples
   only establish `invs(α|ℓ) ≠ ε`, as the paper itself notes ("and possibly ≠ prop_ℓ"). Validity in
   Lemma 12 needs only that `ℓ` has started, since `M[ℓ]` is written before `ℓ`'s first operation.
   `KOrderingI`/`KOrderingW` use "ℓ has started". **Under-specified definition.**
5. **Definition 11, invocation condition.** `invs(α) ⊆ ⋃ₓ invs(prop_x)` is a set inclusion. Read
   literally, it allows histories in which process `j` executes another process's proposal, and then
   even queues are not 1-ordering. The intended condition, used in the proof (and by us), is that every
   process executes a prefix of its own `prop_j`. **Under-specified definition.**
6. **Theorem 3 (simple types from snapshots): proof sketch, not formalized.** The forward simulation
   relates `C₁` to *every* topological sort of `lingraph(G₁*)`. The step case needs sorts for
   `C₂` that *extend* a given sort for `C₁`. But `lingraph` adds dominance edges greedily along a
   topological sort of the whole graph, so new nodes can change the edges among old nodes. This is not
   addressed ("It is easy to see that…"). The correctness of the responses is deferred to [7, 27]. We
   neither confirm nor refute the proof; the result is Ovens–Woelfel's (PODC 2019). **Proof sketch.**

## Typos and slips
* Algorithm 2's caption says "From test&set to fetch&increment"; it is the set algorithm.
* Algorithm 2: `taken_new` is reset to 0 and never incremented, so the `taken` test is vacuous. Both
  readings are modelled (`countTaken`).
* Theorem 9: "the state of the implemented object is the *maximum* index `i` such that `M[i]` is 0" should
  be the *minimum* (equivalently, the number of set entries; they form a prefix).
* Proof of Theorem 17: "`A` is a lock-free strongly-linearizable queue" should be "… implementation of the
  1-agreement (1-ordering) object". The paper uses both "1-agreement" and "1-ordering" for the same notion.
* Definition 11 asks for a set `S_α` "with `k` process indexes", but the examples use `1 ≤ |S_α| ≤ k`; we use
  `|S_α| ≤ k`.
* Proof of Theorem 19: only *linearizability* and wait-freedom of Theorem 5's implementation are needed to
  preserve `B`'s (safety) correctness, not strong linearizability (remark, not an error).

## Modelling choices
* **Model.** CSLib's asynchronous shared memory: deterministic processes, atomic base objects, executions
  are label lists (`inv` / `ret` / internal step `tau`). Each internal step makes exactly one base-object
  access. Local computation is folded into the transitions, and returning is a separate step. There are no
  explicit crashes: a crashed process simply takes no more steps, and strong linearizability is a property
  of finite executions.
* **Strong linearizability** (`Podc/SharedMemory/StrongLin/Basic.lean`) is the Golab–Higham–Woelfel definition: a
  linearization function on finite executions with `α ≤ β ⇒ h α ≤ h β`. A label list determines the
  execution, so `h` may depend on internal steps. For nondeterministic specifications (the set,
  `k`-out-of-order queues), linearizations carry the responses of their operations, pending ones included
  (`IsNLinearization`). For deterministic objects we use CSLib's `IsLinearization`; it implies the
  nondeterministic notion (`StronglyLinearizable.nStronglyLinearizable`).
* **Theorems 1, 2.** Values are natural numbers. `WriteMax` returns `0` as acknowledgement, and `update`
  returns the zero view. Process `i` may only update component `i` (`allowed`). The snapshot's `fetch&add`
  register holds an integer, since the adjustment `posAdj − negAdj` may be negative; the max register
  uses a natural-number register. `ReadMax`'s decoding counts the set bits of each process (unary).
  Processes are `Fin n`.
* **Theorem 5.** `ts` is an ordinary atomic test&set (accessible by all processes) and `state` is a
  Boolean register; `false` stands for 0. Processes form an arbitrary finite type.
* **Theorem 6.** The base objects are atomic. `curr` is a max register initialized to 1, and the
  `TS[v]` (`v : ℕ`) are atomic readable test&set objects, initially 0. `TS[0]` exists in the model but
  is never accessed. `reset` returns `false` as acknowledgement. We prove the paper's linearization
  exactly: at `e_v`, first the pending test&set/read operations on `TS[v]`, then the resetter, then
  the other resets that read `v`.
* **Theorem 9.** `M` is an array of atomic readable test&set objects (`ℕ`-indexed, initially 0).
  Operations are linearized when they obtain 0. Lock-freedom (finitely many processes) is proved
  with one potential that strictly decreases at every invocation and internal step while no operation
  responds; this differs from the paper's informal argument but proves the same property.
* Composition with Theorems 1 and 5 is not formalized: Corollaries 7 and 8, and the last step of
  Theorem 9 ("the theorem follows due to this implementation and Theorem 5").
* **Algorithm 2 counterexample.** Items are natural numbers, `⊥ = none`, three processes, and `Max` is
  initialized to 1. The implemented object's `ObjSpec` is a dummy used only for the `Op`/`Resp` types; the
  specification is the nondeterministic `setSpec`.
* **Definition 11.** Sequential histories are lists `(process, operation, response)` legal for an
  `NSpec`. `S_α` has at most `k` elements. Three versions: `KOrdering` (as stated, with the per-process
  reading of item 5), `KOrderingI` (what Lemma 12's proof needs), and the common weakening `KOrderingW`.

## Not formalized
* Theorem 3 / Theorem 4 (simple types), and Corollaries 7, 8: CSLib has no composition theorem
  for (strongly) linearizable implementations.
* Lemma 12, Corollary 14, Lemma 16, Theorems 17, 19 and Corollaries 15, 18. The reduction needs one
  algorithm simulating another over readable base objects, plus execution surgery (Claim 13); this
  infrastructure does not exist yet. Corollaries 15/18 are cited impossibility results (Herlihy;
  Herlihy–Rajsbaum). We formalized Definition 11 and its examples, which is where the errors are
  (items 2–5).
