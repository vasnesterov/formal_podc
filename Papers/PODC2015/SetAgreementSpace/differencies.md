# Differences between the formalization and the paper

Paper: Delporte-Gallet, Fauconnier, Kuznetsov, Ruppert, *On the Space Complexity of Set Agreement*,
PODC 2015, arXiv 1505.02690v2.

## Errors in the paper

1. **Figure 3 is not (m-)obstruction-free; Lemma 5 is false for it.** Adopting the value of a
   duplicated pair `(w, q)` produces the pair `(w, id) ≠ (w, q)`, so the duplicate survives and the
   process can adopt `w` forever without moving `i`. The proof of Lemma 5, Case 2, assumes the opposite
   ("as `p` changes its preferred value ... it must have found another pair that appears twice").
   - Lean: `fig3_livelock`, `fig3_not_mObstructionFree` and `fig3_not_obstructionFree`
     (`Counterexample.lean`). They cover all `1 ≤ m ≤ k < n`, `r = n + 2m − k`, any `m' ≥ 1`, one-shot
     executions, and identical inputs.
   - Construction: process 1 writes `(v,1)` into components `0..r−2` and stops before writing `r−1`.
     Processes `2..m` write prefixes `0..m+1−j` of decreasing length and crash. Every scan in this phase
     sees `⊥` in `A[r−1]` and advances. Process 1 then writes `A[r−1]`. Finally process 0 runs solo
     forever at component 0.
   - The model checker (`scripts/fig3mof.py`) also finds the 2-process livelock where
     both processes are correct.
2. **Figure 4 has the same bug.** It already shows up inside the first instance.
   - Lean: `fig4_livelock` and `fig4_not_mObstructionFree` (`Repeated.lean`), via the simulation
     `Sim`/`sim_step`/`sim_run`/`sim_soloStep` of first-instance executions of Figure 4 by Figure 3.
   - Consequences: the proofs of Theorem 8, of the upper bounds in Figure 1 for repeated set agreement,
     and of "obstruction-free repeated consensus requires exactly `n` registers" are invalid.
3. **Repair (ours).** Line 11 gets an extra conjunct: "the value in `s[j₁]` (first duplicated pair)
   differs from `pref`". Otherwise the process executes line 14. This is `fig3 true`.
   - Lemma 5 then holds, with a new proof of Case 2: all duplicates eventually lie in the frozen
     components, so the first duplicated value `w*` is constant, and a process that adopted `w*` must
     advance at its next scan.
   - Lean: `fig3Fixed_mObstructionFree`, `theorem7_corrected`.
   - The analogous repair of Figure 4 passes bounded exhaustive model checking (`scripts/fig4mof.py`):
     agreement and m-obstruction-freedom with `n = 2, k = m = 1` and 2 instances per process. It is
     **not** formalized.

## Statements changed or generalized

4. **Theorem 7** is proved for the snapshot algorithm. The claim "`min(n + 2m − k, n)` registers" also
   needs the snapshot implementations of [5] (multi-writer, `r` registers) and [1,13] (from `n`
   single-writer registers). Neither is formalized.
   - Safety (`fig3_solves`, `fig3_solves_of_le`) holds for both versions, for any `r ≥ n + 2m − k`,
     without `1 ≤ m` or `k < n`.
   - Liveness of the repaired algorithm holds for every `r ≥ 1` and every `m`.
5. **Lemma 3** is stated for configurations reached by one-shot executions. It is false for arbitrary
   reachable configurations of the model, where a decided process may be re-invoked; the algorithm is
   one-shot. The proof uses a strengthened invariant: right after an adoption, all pairs of the process
   are in component `i`.
6. **Lemma 1** is used in Theorem 2 from a reachable configuration `D_j`, to the fresh instance `s+1`.
   The paper states it only from the initial configuration.
   - We formalize the form actually used as `Lemma1Prop`: every process invoked at most `s` times, `Q`
     idle with exactly `s` invocations, `|Q| ≤ m`, distinct inputs.
   - We prove it from `BGImpossibility` (`lemma1`) by restarting the algorithm from the configuration
     (`Impl.restrict`). Wait-freedom of the restart follows from `m`-obstruction-freedom
     (`Impl.waitFree_of_restrict`).
   - `BGImpossibility` is a hypothesis (the topological impossibility is not formalized). Its form: no
     register algorithm with arbitrary initial memory and local states, in which exactly a nonempty set
     `Q` of processes may invoke, each with its own fixed input (injective), is wait-free on one-shot
     executions and solves `(|Q|−1)`-set agreement.
   - Non-vacuity of `Lemma1Prop`: `lemma1Prop_trivialImpl`.
7. **Theorem 2** (`theorem2`, `theorem2'`), hypotheses made explicit:
   - all invocations are allowed;
   - an injection `P ↪ V` (processes propose their ids, as in the proof; only `k+1` distinct values are
     really needed);
   - `m`-obstruction-freedom over all executions.
   The conclusion is `|P| + m − k ≤ |ι|` for a finite register family `ι`.
8. **Proof of Theorem 2, technical changes** (the paper's argument goes through):
   - The construction takes any list of group sizes `≤ m` summing to `k+1−m`, plus a last group of size
     `m`. The odd-sized group comes last rather than first.
   - Property 8 is formalized as "no `Q_j`-only fragment from `D_j` reaches a configuration in which a
     process of `Q_j` covers a register outside `A_j`" (`NoWriteOutside`). Hiding uses only that
     registers are read/written blindly.
   - Of property 1, only "the processes of `α_j` are outside the earlier groups `Q`" is kept.
   - `s` (the bound on invocations) is the length of the execution, not the maximum number of
     invocations.

## Modelling choices

9. **Model.** CSLib `Impl`: deterministic processes, base objects accessed atomically, invocations by the
   environment, and a separate response step (as in the paper's "steps": invocation, access, local
   computation, response). Crashes = stopping. Correct processes = infinitely many steps or eventually
   idle.
10. **`m`-obstruction-freedom** (`MObstructionFreeOn`, in `Podc/`): processes "taking infinitely many
    steps" are those with infinitely many labels, invocations included. One-shot algorithms are
    required to be `m`-OF on one-shot executions only.
11. **Figure 3.**
    - Pairs are `(value, id)` in a snapshot over `Option (V × Fin n)` (`⊥ = none`).
    - "min `j₁` with `∃ j₂ > j₁, s[j₁] = s[j₂]`" is `firstDup`.
    - If no duplicate exists at line 10, the output defaults to `pref`. This cannot happen when
      `r > m`, by pigeonhole.
    - A process's decided value is stored in `out`, and it returns in a separate step.
12. **Figure 4.**
    - Line 15: if several tuples of higher instances exist, the first one (lowest index) is used. The
      paper leaves this unspecified.
    - Line 22: taken literally. Only `⊥` and the process's own tuple block adoption; tuples of lower
      instances do not (the prose says they are "treated as ⊥").
    - `i`, `t` and `history` persist across invocations, as in the paper.
    These choices are irrelevant for the counterexample, which lives entirely in the first instance.
13. Local states, register values and inputs range over arbitrary types (`V` with decidable equality
    and a default element).

## Not formalized

14. The repaired Figure 4 (Lemmas 12–14, a corrected Theorem 8). It is model-checked only, on small
    bounded instances.
15. Section 5 (Lemma 9, Theorem 10, the anonymous one-shot lower bound) and Section 6 (Theorem 11, the
    anonymous algorithm, Appendix B).
16. Figure 1's table, and the corollaries derived from cited results (one-shot lower bound 2 from [4],
    snapshot implementations).
