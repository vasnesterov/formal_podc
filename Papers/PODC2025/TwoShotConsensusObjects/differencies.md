# Differences between the formalization and the paper

Nguyen, Sutra, *An Exact Characterization of the Two-shot Deterministic Objects Solving
Two-process Consensus*, PODC 2025.

The main theorem (Theorems 1–3: `(T, m)` solves two-shot two-process consensus iff it is in
`C₁ ∪ C₁.₅ ∪ C₂`) is **correct** and fully formalized (`characterization`, `Main.lean`).
The list below covers every place where the formalization departs from the text.

## Errors in the paper

1. **The AQ example (Section 4.2.5) is wrong.** *(False statement in an illustrative example;
   the main theorem is unaffected.)*
   The paper says the asymmetric queue AQ (`p₁` may only `enqueue`/`read`) is in `C₁.₅`, with
   witness: queue `[0]`, `f = dequeue`, `f' = read`, `g = enqueue(1)`, `g' = read`.
   - This witness already fails property (1). `dequeue` returns `0` whether or not
     `enqueue(1)` came first (`paper_AQ_witness_fails`, checked by `decide`). Properties (3),
     (4) and (5) fail too (`fg` and `gf` both lead to `[1]`); only (2) holds.
   - No witness works. AQ satisfies the `C₁.₅` properties for no state and no choice of
     operations, in either role orientation (`aq_not_C15Cond`, `aq_not_C15`).
     - Property (1) forces `g = enqueue(y)` and `f ∈ {dequeue, read}`. Then property (3) for
       `p₁` forces `g' = read`, `f = dequeue` and an empty queue.
     - In that case `p₁` cannot tell `gg'ff'` from `fgg'f'` (it reads `[y]` in both), so
       property (4) fails.
     - In the other orientation, `p₁`'s `f` must be `read`. Then `fg` and `gf` reach the same
       state, so property (3) fails for `p₀`.
   - AQ is in `C₂`, with the WQ witness (`aq_C2`), so it does solve consensus
     (`queues_solvable`).
   - A related side claim (in the paragraph about WQ) is imprecise: "if `fg` and `gf` are
     distinguishable to `p₀` then `f = read()`, `g = enqueue(1)` and the queue is initially
     empty". For WQ, `f = read`, `g = enqueue(y)` distinguish from *every* state, so emptiness
     is not forced; for AQ, `f = dequeue()` on an empty queue also works.
2. **Algorithm 3, line 30 (typo).** The test `v[1][1] = τᵥ(s.g c_{3^k} f, c_{3^k−1})` must read
   `v[0][1] = …`. Line 30 is executed only by `p₀`, whose local `v[1][1]` is always `⊥`. As
   written, the branch for the interleaving `g cₙ f cₙ₋₁` never fires at `p₀`. The formalized
   algorithm uses `v[0][1]` (`AlgC2Alg.lean`).
   - Taken literally, the algorithm is wrong. A brute-force search (Python, not in Lean) found a
     4-state, 3-operation object satisfying `C₂`, with `n = 1` padded to `3`, that breaks it.
   - In the run where `p₁` runs solo first (`g c₃ f c₂`), `p₁` decides `Val[1]` at line 28.
     `p₀` falls through to line 37, where its response to `c₂` coincides with `τᵥ(s.fgc₃, c₂)`,
     so `p₀` decides `Val[0]`. Agreement is violated.
   - With `v[0][1]`, the algorithm is correct (proved in Lean).
3. **Section 5.3 slips.**
   - Corollary 1's proof says "`opᵢ ∈ [0, k]`"; it should be `[0, 3^k]`. *(Typo.)*
   - The proof of Lemma 2 ("largest `k > 0` with `n = 3^{k-1} + a`, `a ≥ 0`; if `a = 0` we
     are done") is imprecise: for `a = 0` it yields `n = 3^{k-1}`, which for `n = 1` violates
     `k > 0`; and it cites the "third property" of `C₂` for the pairs of property (2). The
     intended argument (pad the sequence with `cₙ₋₁, cₙ` until `n = 3^k`, `k ≥ 1`) is the one
     formalized (`AlgC2Pad.lean`). *(Minor proof imprecision.)*
4. **Proof of Proposition 2:** "`c₁, …, cₙ₋₁ = f'` with `n ≥ 2` even" should say `n` odd
   (`cₙ₋₁ = f' ∈ m(p₀)` needs `n − 1` even). *(Typo.)*

## Gaps in the sufficiency proofs (statement true)

- **Lemma 4 (Algorithm 3).** The case analysis omits the histories in which the other process
  applies its operations on `O` after the deciding process's reads. The Lean proof
  (`decide0_ok`, `decide1_ok`) enumerates all interleavings.
- **`k ≥ 1` is genuinely needed in Algorithm 3.** The paper requires `k > 0` but justifies it
  only informally. With `N = 3⁰ = 1`, in the run `g c_N f c_{N−1}` process `p₀` has
  `op = 0 = N − 1`. Line 23 is then tested before line 30 and can wrongly return `Val[0]`.

## Gaps in the necessity proof (statement true, filled in the formalization)

5. **The critical operations may be second accesses.** Section 6 assumes that `f` and `g` (the
   operations at the critical configuration) are the *first* accesses of `p₀`, `p₁` to `O`.
   The formalization covers the other cases.
   - If `f` is `p₀`'s second access, then `p₀` can never access `O` again, so `fg` and `gf` are
     distinguishable to `p₀` (`dist_of_last`).
   - If `g` is also a second access, the object is in `C₁`. Otherwise it is in `C₁.₅`, with
     `f' := f` and alternative (5a) (`KSetup.c15`).
   - If neither process distinguishes `fg` from `gf`, both operations are first accesses.
6. **Existence of `f'` in Proposition 1 / Lemma 5.** The paper takes "the second operation `f'`
   that `p₀` calls after `fgσ_{p₁}g'`", but `p₀` might decide without accessing `O` again.
   - In that case (5a) holds, and so does the `p₀`-part of (4). Otherwise `p₀` would decide
     the same value after `gσ_{p₁}g'f`.
   - So any `f' ∈ m(p₀)` works (we take `f' = f`).
   - Every other "the process must access `O` again" step of the paper is proved explicitly
     (`must_access'`).
7. **The graph `G` of Proposition 2 must be bipartite.**
   - The paper's nodes are *operations*. An operation allowed to both processes would be a
     single node, and a path could then change sides there. The parity claim "`cᵢ ∈ m(p₀)` for
     `i` even" would fail.
   - The formalization uses nodes `(process, operation)` (`KSetup.Adj`, `KSetup.Conn`). The
     reduction argument goes through unchanged.
   - The "consistent decision" rule of the reduced algorithm is: `p` poised on `c` decides
     `p₀`'s input iff `(p, c)` is connected to `(p₀, c₀)`.
   - The edge relation is "both processes simultaneously poised on `O` after an `O`-free
     extension of `fg`". This is the paper's edge definition after the commutation step it
     uses.
8. **Minimal number of objects.** The paper fixes an algorithm with the minimal number of
   copies of `O`. We do strong induction on the number of copies (`necessity`). This needs
   the algorithm to use **finitely many copies** (`Fintype ιS` in `Solvable`); the paper
   assumes this implicitly ("minimal number").
   - The reduction (`reduction`, `NecReductionSim.lean`) builds the smaller algorithm
     explicitly. It starts from the configuration `fg`, uses fresh proposal registers and
     halts before the second access to the removed copy.
   - The paper does not prove the reduced algorithm wait-free. We prove it (the reduced
     algorithm's infinite schedules are simulated by sub-sequences of steps of the original).
   - We also prove that nobody can decide from `fg` before accessing the removed copy again.
9. **Registers at the critical configuration.** The paper only says "standard". We prove it
   for every read/write-like object (`IsRW`: each operation is read-only or a blind write),
   which includes registers.

## Modelling choices (not errors)

10. **Consensus** is binary consensus with inputs in the initial local state and outputs as
    final states (CSLib `Recoverable` model without crashes, `WFConsensus`). The paper uses a
    linearizable `propose()` object; for one-shot binary consensus the two are equivalent.
    "Return `Val[j]`" is modelled as a read of register `Val[j]` followed by an output.
11. **Wait-freedom** means: in every infinite crash-free schedule, a process that takes
    infinitely many steps eventually outputs. Crashes are modelled by a process stopping
    taking steps (finite or unfair schedules).
12. **Two-shot** means: in every execution, each process applies at most two operations to
    each copy of `O` (`TwoShot`, counted along the execution). The allowance map is enforced
    on all reachable configurations (`Allowed`).
13. **Registers** are generalized to arbitrary read/write-like objects (`IsRW`) with any value
    types. Initial values of all objects are chosen by the algorithm (Jayanti's model, as in
    the paper).
14. **Class definitions** are stated with the paper's exclusions (`C15` excludes `C1`, `C2`
    excludes `C1` and `C15`). `C15` includes the role-swapped version, as the paper says.
    `classes_iff` shows that the union equals the union of the raw conditions.
15. **Algorithm 3: the `Next_op` read.**
    - Each process reads only `Next_op[1−i]`, once, before deciding. The paper reads it inside
      the decision branches; there are no shared steps in between, so this is equivalent.
    - Lines 25 and 30 name `Next_op[0]` and `Next_op[1]`; by the parity of `op` these are
      `Next_op[1−i]` for the process that reaches them.
    - The local state stores the round values read; `op` is computed from them.
    - Lemma 2's padding uses `k = n`, i.e. `N = 3ⁿ`, with the sequence continued periodically
      by `cₙ₋₁, cₙ`. Algorithm 2's re-read of `Ret[0]` (line 32) is kept conditional, as in the
    paper.
16. **Redundancy noticed.** The `p₀`-half of property (3) of `C₁.₅` follows from property (1),
    and Algorithms 1–2 never use it.
