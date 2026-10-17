# Differences between the formalization and the paper

Paper: Fraigniaud, Lambein-Monette, Rabie, *Fault Tolerant Coloring of the Asynchronous Cycle*,
PODC 2022 (brief announcement), full version arXiv:2207.11198v1.

## False statements

1. **Theorem 3.11 (termination) is false.** Algorithm 2 is not wait-free on any `C_n`, `n ≥ 3`.
   - Execution: identifiers `0, …, n-1`; at time 1 every process takes a round; afterwards only
     processes `0` and `n-1` take rounds, simultaneously, forever.
   - Processes `1` and `n-2` stop after their first round, so their registers show their initial
     colours `(0,0)` forever.
   - Processes `0` and `n-1` alternate between the states `(1,1)/(0,1)` and `(2,2)/(0,2)` and never
     return.
   - The same prefix of length `K` shows that no bound `K` holds, even in executions that later
     become fair.
   - Lean: `theorem_3_11_false` (`C_3`, by `decide`), `theorem_3_11_false_all` (every `n ≥ 3`),
     `alg2_not_waitFree_of` (any identifiers with `X_0 = 0 < X_1` and `X_{-2} < X_{-1}`).
2. **Lemma 3.13 is false.** In the execution above on `C_3`, process 2 is a local maximum, so it is
   not a local minimum and its set `A_2(t) = ∅` is constant. Yet it fails at every activation.
   - The proof wrongly assumes that the neighbours' visible `a`-values are positive by time `t₄`.
     A neighbour that took a single round still shows its initial `a = 0`.
   - Lean: `lemma_3_13_false`.
3. **Theorem 4.4 (termination, `O(log* n)`) is false.** Algorithm 3 is not wait-free, by the same
   execution.
   - Processes `0` and `n-1` are a local minimum and a local maximum; they set `r ← ∞` at time 1 and
     never change `X` again.
   - Lean: `theorem_4_4_false`, `theorem_4_4_false_all`, `alg3_not_waitFree_of`.
   - So the headline claim of the paper (wait-free 5-colouring of all cycles in `O(log* n)` rounds)
     is not established. Its proof is also built on Lemma 3.13 (via Lemmas 4.8–4.10 and the proof of
     Theorem 4.4).
   - We do not claim that wait-free 5-colouring of `C_n` is impossible; only the algorithms fail.
4. **Lemma 3.3 is false as written (imprecise interval).**
   - With "neither neighbour is working in `(t₁, t₂)`", a neighbour that takes a round exactly at `t₂`,
     or at both `t₁` and `t₂`, may still conflict with `p` at `t₂`. Random simulation of Algorithm 1
     finds such runs, e.g. on `C_4`.
   - It holds with the half-open interval `(t₁, t₂]` and `p` failing at `t₁`. That is the version we
     prove and use: `fresh_of_conflict`, specialised to Algorithm 1.
   - It is used only inside proofs, so this is not a gap in a main result.

## Proof gaps (statements true)

5. **Theorem 3.1.**
   - The statement is proved (`theorem_3_1`), with the sharper bound `max(4, n)` instead of
     `⌊3n/2⌋ + 4` (`alg1_workActs_le`).
   - Our proof differs from the paper's.
     - Non-extremal processes: a failed round changes the colour (Lemma 3.2). `a_p` follows
       `mex{â_q}` for the unique larger neighbour `q`, which adds at most one change per level of the
       increasing chain (the change `⊥ ↦ 0`). This gives `ℓ + ℓ' + 1` (`lemma_3_9`).
     - Local extrema: after `p`'s first round, each neighbour can be responsible for at most one
       further failure of `p` (`no_two_conflicts`). This gives `≤ 4` (`workActs_le_four_of_max/min`).
   - We neither use nor formalize the paper's Lemmas 3.4–3.8, which are informal case analyses.
   - The bound "`min{ℓ, ℓ'}` is bounded by `⌊3n/2⌋`" in the proof of Theorem 3.1 is odd; it should be
     `n/2`. The final bound still holds.
6. **Lemma 3.9.** Only the term `ℓ + ℓ' + 1` is proved; the paper states `min{3ℓ, 3ℓ', ℓ+ℓ'} + 4`.
   - The `3ℓ + 4` and `3ℓ' + 4` terms rest on Lemma 3.4 for non-extremal processes, which is not
     formalized.
   - Exhaustive model checking of all schedules and all identifier orders on `C_n`, `n ≤ 6`, found no
     violation (`modelcheck/bounds1.py`).
   - Our `ℓ` (`upDist`) is the number of steps along increasing identifiers to the next local maximum.
     It is `0` for local extrema.
7. **Lemma 4.5.** The statement is true and proved (`lemma_4_5`), together with the paper's induction
   claim `X_p(t) ∉ {X_q(t), X̂_q(t)}` (`alg3_X_ne_reg`) and `X_p(t) ≠ X_{p+1}(t)` (`alg3_X_proper`).
   - The paper's induction is not valid as written.
     1. The claim alone is not inductive. One needs ghost information about what a neighbour read in
        its last step. Our invariant `Alg3Proper.Inv` adds two facts: `r̂_p ≤ r_p`, with equality only
        if `X̂_p = X_p`; and, if `q`'s last step changed `X_q` and `r̂_q = r_p`, then that step read the
        current `X_p`.
     2. In the stale-read case the paper derives `X̂_p(T+1) = X̂_p(t₀)`, but what is needed is the
        current local `X_p`. That follows from `r_p = r̂_q` and "X changes only when r changes",
        which is never stated.
     3. The step "`X_q(T+1) = f(X_q(T), X_p(T))`" ignores the cases where `q` is a local maximum or
        reduces against its other neighbour.
8. **Lemma 4.1** is stated for real `x ≥ 1`. We prove the version over `ℕ` (`lemma_4_1`, with
   `α = 3`). `F` takes odd integer values after one step, so the two versions are equivalent up to
   one step.

## Under-specified definitions / modelling choices

9. **`⊥` in Algorithm 3, lines 11–19.**
   - The paper does not say how an unwritten register enters the green-light test or the comparisons
     of identifiers.
   - We follow the proof of Lemma 4.10: an unwritten `r` counts as smaller than every counter, so it
     blocks line 11; when line 11 passes, both neighbours are awake.
   - In lines 6–10, and in Algorithms 1–2, `⊥` neighbours contribute nothing to `C`, `C⁺`, `P⁺`.
   - The counterexamples do not depend on these choices: every register they read is written.
10. **Network and registers.**
    - Nodes are `ZMod n` with neighbours `p ± 1`. The step function receives the two neighbour
      registers in a fixed order. All the paper's algorithms are symmetric in them, so this is
      harmless.
    - Registers hold the full local state; the algorithms write all their variables anyway.
11. **Identifiers.**
    - Correctness, palette and Lemma 4.5 assume only a proper colouring, as the theorems do.
    - For Algorithm 1 the identifiers may come from any linear order. This is used for the
      `a ↔ b` symmetry (`run_alg1_dual`); `theorem_3_1` is stated for `ℕ`.
12. **Schedules.**
    - The schedule is `σ : ℕ → Finset (ZMod n)`, where `σ(t)` is the set activated at time `t ≥ 1`.
      Activating a process that has returned does nothing.
    - Running time is the number of working activations (`workActs`), as in Section 2.2.
    - `WaitFreeWithin K` quantifies over all schedules (no fairness), which matches the definition of
      running time as a supremum over all executions.
13. **Theorem 4.4's `O(log* n)`** needs identifiers in `[0, poly(n)]` (assumed for identifiers in
    Section 2.1), while the theorem is phrased for any proper colouring `X`. This is moot, since
    termination fails.

## Not formalized

- **Property 2.1** (MIS is not wait-free solvable) reduces to strong symmetry breaking [6, Thm 11], a
  cited result.
- **Property 2.2** (`Ω(log* n)`) is Linial's lower bound.
- **Property 2.3** (`k ≥ 5` colours) is the renaming lower bound for 3 processes [6, 14]; both are cited.
- **Lemmas 3.4–3.8, 3.14 and 4.6–4.10.** They are intermediate steps of proofs we replaced (Theorem 3.1)
  or of false theorems (3.11, 4.4). Lemma 3.14 rests on the false Lemma 3.13.
- **Appendix A** (Algorithm 4, `O(Δ²)` colours on general graphs) is only sketched in the paper.

## Typos

- In the proof of Lemma 3.5, "`X̂_p(T+1) < Y`" should be "`< x`", and "Since `τ ≤ T`" should read `t' ≤ T`.
- In the proof of Lemma 4.10, `R` in "`r̂_{q₋ₖ₋₁}(t₀) = R − k − 1`" is undefined; it is presumably
  `r̂_p(t₀)`.
- In the abstract and §1.3: "asymptotically" is misspelled "symptotically" in the PODC abstract.
