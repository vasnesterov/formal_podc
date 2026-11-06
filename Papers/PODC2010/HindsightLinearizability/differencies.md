# Differences between the formalization and the paper

Paper: O'Hearn, Rinetzky, Vechev, Yahav, Yorsh, *Verifying Linearizability with Hindsight*, PODC 2010
(10-page author copy).

## Statement-level issues

1. **Lemma 5.4 (Backbone Lemma) is false as stated** (`Counterexample.lean`: `lemma_5_4_false`,
   `lemma_5_4_as_stated_false`). The claim `i₀ = j₀ < j₁ < … < j_k = i_k` fails on a shape-legal trace
   of the algorithm itself (`add(5)` then `remove(5)`, temporal backbone `⟨H, a⟩, ⟨a, T⟩` through the
   states just before and just after the atomic section of `remove`). Each of `j_k = i_k` and the strict
   inequalities fails separately. Corrected and proved: `i₀ = j₀ ≤ j₁ ≤ … ≤ j_k` with
   `i₀ ≤ j_m ≤ i_m` (`backbone_lemma`).
   ✏️ The intended version can be recovered from the paper: the
   lemma's own clause `i₀ ≤ j_m ≤ i_m`; its proof "follows directly from Lemma 5.2", which only gives
   `i ≤ j ≤ k`; and the definition of `ι` for `contains` in Thm 7.5, which chooses "the last state at
   or before the last crossing state in which the last crossed link is a backbone link" and so presumes
   `j_k ≤ i_k`. The fix is local (inequality symbols), and no proof in the paper uses the wrong
   version.
   `j_k = i_k` would say that the last crossed link is a backbone link when it is crossed, which would
   make hindsight pointless. Nothing in the paper relies on it.
2. **Lemma 5.7 conclusion typo.** It is printed as `K_σ ∩ {u.k_σ, v.k_σ} = {u.k_σ, v.k_σ}`, which is
   true but trivial (`local_window_as_printed`). The intended interval version
   `K_σ ∩ {u.k_σ, …, v.k_σ} = {u.k_σ, v.k_σ}` is the one used in Thm 7.5 and is proved as
   `local_window` (with `Set.Icc`). The printed statement is not false.

## Proofs

3. **Lemma 5.2 (Hindsight).** We use a different, shorter proof: induction on `k`, using `δ_en`,
   `δ_bn` and "no reclamation" only. The paper's proof also uses `δ_e`, which is not needed. It also
   relies on two facts the shape properties of Def. 5.1 do not list: nodes are never reclaimed, and the
   successor of an allocated node is allocated. Both are part of the paper's memory model (§4). We add
   them explicitly: `NoReclaim` to the shape-step property and `Closed` to the shape-state property.
4. **Lemma 5.4.** We prove the corrected statement by induction, as the paper suggests, using Lemma 5.2
   at each step with `i := j_{m-1}` and `k := i_m`.
5. **Lemma 5.7.** We use only `φ_s` (sortedness along every heap path, non-strict) and the fact that the
   nodes reachable from `H` form one heap path. Acyclicity and `φ_<` are not needed. The paper's proof
   goes through "a strictly ascending sorted list between head and tail".
6. **Thm 4.1.** The paper defers the proof to a separation-logic technical report [18]. We give our own
   proof via an inductive invariant (`MemInv` + `LocInv`). Its core is an explicit backbone list `L`:
   a heap path `H → … → T` whose nodes are exactly the unmarked allocated nodes. Every state and step
   property of Fig. 4 is derived from it.
7. **Lemma 6.3 + Thm 6.4.** Lemma 6.3 (temporal traversal) is formalized for `contains` only, and in a
   combined form with Lemma 5.4. The history invariant `GhostC` says that the current node, or the link
   just crossed, was a backbone node or link at some state after the invocation; it is extended at every
   crossing by `hindsight_node`. The readable statement is `temporal_traversal`. "Traversal trail tails"
   (Def. 6.2) are not defined. The paper's proof of Thm 6.4 needs only `φ_<` and `δ_k`, not Lemma 6.3,
   and so does ours (a lexicographic potential, `WaitFree.lean`).
8. **Thm 7.5.** We follow the paper's two stages. Stage I becomes a generic criterion
   (`exists_isLinearization_of_points`, staged in `Podc/`). It orders operations by their
   linearization state, with `contains` before the `add`/`remove` of the same state, as in the paper.
   Stage II becomes the history invariant `Hist` (`History.lean`). In `ι`, "the transition in which `t`
   executes its atomic section" is read as the *successful* atomic section: with restarts, an
   `add`/`remove` may run several (failed) atomic sections. Pending `add`/`remove` operations that have
   taken effect are linearized and pending `contains` are dropped, as in the paper's completion.
9. **Lemma 7.4.** Proved as stated (`lemma_7_4`). Under our invariant, "the abstraction function is
   well defined" is automatic, because `Abs` is a total function of the memory.

## Modelling choices

10. **Shared-memory model.** CSLib's `Impl` (asynchronous, interleaving, sequentially consistent,
    deterministic threads, arbitrary scheduler). The heap is a single base object, and each primitive
    instruction or atomic section of Fig. 1 that touches shared memory is one operation on it. Purely
    local instructions are merged into these steps.
    - `p = H` (line 21) is a separate read step, and a failed validation restarts there.
    - `contains` reads `c.k` once at line 24 and uses that value for line 42. Fig. 1 reads `c.k` again,
      but keys are immutable (`δ_k`), so both values coincide.
    - Invocation and response are separate steps (CSLib convention).
11. **Threads and operations.** The paper assumes w.l.o.g. that each thread invokes at most one
    operation. We allow sequences of operations per thread (`OpId = P × ℕ`), which is more general.
12. **Memory, nodes, keys.**
    - Nodes are natural numbers; the allocated nodes are `0, …, cnt − 1`. `alloc(E)` returns `cnt`.
    - There is no memory reclamation, as in the paper. `null` is `Option.none`.
    - The initialized state is the result of `init()`: `T = 0` (allocated first), `H = 1`.
    - Keys are `WithBot (WithTop ℤ)`: `⊥ = -∞`, `⊤ = ∞`. Operation keys are integers (Fig. 1 has
      `int k`).
13. **Memory safety.** Dereferencing `null` at `c = p.n` sends the thread to an error local state
    `err`; this is the paper's `σ_error`. The only possible null dereference is `c.k` after reading a
    null `c`, and we model it at the read of `p.n`. Theorem 4.1 (`theorem_4_1_memSafe`) says `err` is
    never reached.
14. **Specification.** Fig. 2 with abstract states `Set ℤ` instead of finite sets. All reachable
    abstract states are finite (they start from `∅` and change by single inserts and erases), and the
    responses are the same.
15. **Linearizability.** We use CSLib's `IsLinearization` / `Impl.Linearizable` (the amended
    Herlihy–Wing definition: completions, real-time order). It is the standard notion. Def. 7.2 of the
    paper is garbled: it mixes indices of `H` and `π`, and "linearizable with respect to a sequential
    history". Linearizability is shown for every finite execution, which implies it for every infinite
    one.
16. **Wait-freedom.** Stated for infinite executions (`Impl.InfExec`): if a thread's `contains k`
    stays pending forever, the thread takes only finitely many steps (`theorem_6_4`).
17. **Traces.** A trace is `τ : ℕ → HeapState N K` with a length `n`, and only `τ 0, …, τ (n−1)`
    matter. Shape-legality (Def. 5.1) also includes `Closed` and `NoReclaim` (item 3). Our Def. 5.5
    takes `φ^d = φ_s` and `δ^d = δ_k`, as printed. The paper's Def. 5.6 additionally requires
    `σ ⊨ φ^s, φ^d`; we define `K_σ` for every state.
