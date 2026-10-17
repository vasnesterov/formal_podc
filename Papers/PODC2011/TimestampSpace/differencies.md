# Differences between the formalization and the paper

Paper: Helmi, Higham, Pacheco, Woelfel, *The space complexity of long-lived and one-shot timestamp
implementations*, PODC 2011; formalized from the full version arXiv:1103.5794v2 (numbering as there).

Classification: **[false]** false statement, **[degenerate]** false only in a degenerate case,
**[gap]** proof gap with true statement, **[spec]** under-specified definition, **[typo]**,
**[model]** modelling choice / generalization.

## Model and definitions

1. **[model] Deterministic processes.** The paper allows nondeterministic processes and proves its
   lower bounds for "non-deterministic solo-termination". We use CSLib's deterministic `Impl`, where
   this notion is obstruction-freedom (`SoloTerm`, `soloTerm_false_iff`). The paper itself fixes the
   nondeterministic choices in its proofs.
2. **[spec] Covering for nondeterministic processes.** The paper says `p` covers `r` "if there is a
   non-deterministic decision such that the one-step execution is a write to `r`". With
   nondeterminism a process may then cover several registers at once. This breaks the signature
   counting of Section 3 ("`∑ cᵢ = k`" for `k` covering processes) and the counting of Section 4.
   With fixed choices (deterministic processes) every process covers at most one object
   (`Impl.Covers.unique`); both arguments need this.
3. **[spec] Timestamp specification.**
   - We additionally require that every completed `getTS` returns a timestamp (`TSCorrect.getTS_ts`).
     The paper leaves this implicit. Without it a `getTS` returning a Boolean makes the
     specification vacuous.
   - "Any later `compare`" is read as "any `compare` invoked after the later `getTS` returned". This
     is the weakest reading, so it makes the lower bounds strongest.
   - `compare` may access shared memory (non-static timestamps, as in the paper).
   - The universe `T` is arbitrary, and may be finite; the lower bounds do not use unboundedness.
4. **[model] Base objects.** The lower bounds hold for any finite family of read/write-like objects
   (`RWLike`: every primitive is read-only or a blind overwrite). Registers with arbitrary,
   possibly different, value types and arbitrary initial values are the main example. The
   historyless extension of Theorem 1.2 (Section 7) is not formalized.
5. **[model] One-shot.** "Each process calls `getTS` at most once" (`Adm true`). The number of
   `compare` calls is unrestricted, and correctness and progress are only required on such
   executions.
6. **[model] Invocations are separate steps** (CSLib labels `inv`/`tau`/`ret`), and idle processes
   are those that never invoked anything. A quiescent or idle process never covers an object.

## Lemma 2.1 (Ellen, Fatourou, Ruppert)

7. **[model] Form of the lemma.** Formalized (`lemma_2_1`) in the form used by the paper. The
   complete `getTS` of the `Uᵢ`-only execution `βᵢ` is by a process `qᵢ ∈ Uᵢ` that is idle in `C`
   and invokes only this `getTS` in `βᵢ`. The other processes of `Uᵢ` are arbitrary. The hypothesis
   "does not write outside `R`" is weakened to "the memory outside `R` is unchanged at the end of
   `βᵢ`", which makes the lemma stronger. The paper cites this lemma without proof; we prove it.
   The proof uses the `compare` operation: after the two orders `πB₀β₀πB₁β₁πB₂` and
   `πB₁β₁πB₀β₀πB₂`, which reach the same configuration, `q₀` runs `compare(t₀,t₁)` solo.

## Section 3 (Theorem 1.1, long-lived)

8. **[model] Lemma 3.2 generalized** to any set `S` of `≥ 2k` processes instead of `P_{2k}`
   (`lemma_3_2`).
9. **[gap] Lemma 3.1, missing hypothesis.** The conclusion is stated "for any quiescent
   configuration `D`", but the proof applies the hypothesis to later configurations and uses
   solo-termination, so it needs `D` to be reachable. We assume this (`lemma_3_1`).
10. **[gap] Commutation of the first two block writes.** The proof of Lemma 3.2 uses
    `πBᵢπB₁₋ᵢπB₂η(C₀) = C₁` without justification. It holds because `πB₂` obliterates whichever of
    the two first block writes came last (`blockWrite_swap`).
11. **[gap] Three disjoint covering sets in Lemma 3.1.** Their existence relies on every process
    covering at most one register. This is true for fixed nondeterministic choices (see 2) and
    implicit in the paper (`exists_triple`).
12. **[typo]** In the proof of Lemma 3.2, "`πBᵢλπB₁₋ᵢπBⱼη(C₀)`" should be `πB₂`.
13. Theorem 1.1 is proved in the form `⌊n/2⌋ ≤ 3m` (`theorem_1_1`), hence `m ≥ ⌊n/6⌋`
    (`theorem_1_1_div`) and `m > n/6 - 1` (`theorem_1_1_real`), as the paper states.

## Section 4 (Lemma 4.1, Theorem 1.2, one-shot)

14. **[model] Lemma 4.1 output.** `lemma_4_1` returns the schedule as *moves* (process, labels):
    `πc₀ M₀ πc₁ M₁` with `{c₀, c₁} = {B₀, B₁}`, `|M₀| + |M₁| = |U| - 1` and `|M₀| ≥ ⌊|U|/2⌋`. Each
    process of `M₀`/`M₁` covers an object outside `R` right after its own segment, and hence also at
    the end (`SD.moved_U`). This is the paper's (a)–(f) plus the per-prefix information the proof of
    Theorem 1.2 needs. The proof is the paper's induction (`two_choice`, `iter`, `assemble`).
15. **[gap] Case 2 counting, and an off-by-one in the log term.** The paper claims
    `|participants(σσ')| ≥ ⌈|idle(C_k)|/2⌉` in Case 2. But `γ_{k+1}` may cut `σ'`, so only the
    participants of `σ` (at least `⌊|idle|/2⌋`) are guaranteed to leave the idle set. The idle set
    therefore shrinks to `≤ ⌈|idle|/2⌉`, not `≤ ⌊|idle|/2⌋`, and Case 2 occurs at most `⌈log₂ n⌉`
    times, not `log n` times. For example, idle sizes `5 → 3 → 2 → 1` allow three Case-2 steps,
    while `log₂ 5 ≈ 2.3`. The proof therefore gives
    `#objects ≥ ⌊√(2n)⌋ - ⌈log₂ n⌉ - 2`, not `⌊√(2n)⌋ - log n - 2`. Theorem 1.2's
    `√(2n) - log n - O(1)` is unaffected (`theorem_1_2`; `theorem_1_2_real` gives
    `> √(2n) - log₂ n - 4`). Also **[typo]** "`idle(Cᵢ) < idle(Cᵢ₊₁)`" should be `>`.
16. **[gap] Bound on `poised(C_{k+1}, Q)` when `γ_{k+1}` is empty.** The paper derives
    `|poised(C_{k+1}, Q)| ≤ Σ(ℓ_k - c - 1) + 1` from the minimality of `γ_{k+1}`. After a Case-2 step
    `ℓ` decreases, so the next configuration may already contain a full set `Q'` w.r.t. the new `ℓ`.
    Then `γ_{k+2}` is empty and minimality says nothing. Our invariant keeps sparsity w.r.t. the
    *previous* threshold, `Inv.sparse`: no nonempty `S ⊆ R̄` has all counts `≥ ℓ + 1 - j - |S|`.
    This is preserved in both cases and suffices for all bounds.
17. **[gap] The final counting ("`|idle(C_last)| ≤ 1` is impossible").** The paper uses
    "each `Cᵢ` is `ℓᵢ`-constrained", which is not part of the stated construction invariant
    (a)–(e) and is not proved for the columns in `Rᵢ`. It also uses an "association" of processes to
    the last register they cover, with `g(r) = |poised(C_{f(r)}, {r})|`. This equality is inexact:
    block-writers can cover other registers after their write, and a process may be associated with
    a register it does not cover at time `f(r)`. We replace this with an inductive invariant,
    `Inv.nbound`: the number of non-idle processes covering no object outside `R` is at most
    `Σ_{c=1}^{j}(m - c)`. Together with `Inv.sparse` it gives `n - |idle| ≤ m(m-1)/2 ≤ n - 2`, so at
    least two processes are always idle (`idle_ge_two`). This also gives the paper's invariant (c),
    which we do not need to carry.
18. **[gap] Counting equality in the step.** The paper says
    `|poised(C_k, R̄_k)| + |idle(C_k)| = |poised(γ_{k+1}(C_k), R̄_k)| + |idle(γ_{k+1}(C_k))|`. After
    their write, block-writers may cover registers outside `R_k`, so only `≤` holds. This is the
    direction needed.
19. **[spec] "Every register in `R_last` is covered by at least one process".** This may fail: the
    threshold `ℓ - j` can be `≤ 0` in the last step. It is not needed: only `|R_last| ≤ #objects` is
    used.
20. **[model]** `log` is read as `log₂`; `m = ⌊√(2n)⌋` is `Nat.sqrt (2n)`. We assume `n ≥ 3`, as
    the paper does, and `#objects ≤ m` (otherwise the bound is trivial).

## Section 5 (Lemma 5.1, simple one-shot algorithm)

21. **[typo]** The comment says register `R[i]` is written by processes `2i` and `2i+1`, but the code
    (`i = ⌈p/2⌉`, 1-based) gives processes `2i-1` and `2i`. We use 0-based ids with register `p/2`.
22. **[spec]** `sum := sum + R[i]` is ambiguous: it may re-read `R[i]` or use the value just
    written. Both readings are formalized (`reread` flag) and both are correct.
23. **[model]** `R[i] := R[i] + 1` is a read followed by a separate write.
24. The proof is correct. Its key step, "registers never decrease", really needs one-shot: with two
    `getTS` calls per process the algorithm is incorrect, as shown by a Lean counterexample for
    `n = 2` (`SimpleTS.cex_not_correct`, `SimpleTS.not_isTS_longLived`).

## Section 6 (Algorithm 4, Theorem 1.3)

25. **[model] Atomic scan.** As in the paper ("we treat it as atomic"), `scan` is atomic. In CSLib an
    atomic multi-register scan needs a single base object, so the memory is one object holding an
    unbounded array `ℕ → Option Val` (1-based), with primitives `read i`, `write i v` and
    `scan k` (returns `R[1..k]`; the algorithm scans `R[1..myrnd+1]`, the only entries it uses).
    "Uses `m` registers" means that every accessed index lies in `[1, m]`. The Afek et al. double
    collect is not verified (it would be correct here: every write to a given register writes a
    distinct value). Consequently the upper bound's base object is not `RWLike`.
26. **[model]** Line 2 reuses the value read at line 1. Line 10 is a separate read, as in the proof
    of Claim 6.13. The getTS-id of an invocation is `(p, number of completed operations of p)`,
    which is distinct per invocation.
27. **[gap] Lemma 6.5's final count.** "`Σ_{ϕ=1}^{Φ} ϕ ≤ 2M`" counts the last, possibly
    incomplete, phase as having `Φ` invalidation writes. Claim 6.10 only covers completed phases;
    the honest count gives `⌈2√M⌉ + 1` registers. The statement is still true. Repair: the getTS that
    starts a phase never makes a "first invalidation" (`I₃`) write, since its line-11 writes are in
    phase `myrnd` and hence not invalidations by Claim 6.11. Its unused credit gives
    `#invalidations + Φ ≤ 2M`, hence `K² + K + 2 ≤ 4M` for every written index `K`. This recovers
    exactly `⌈2√M⌉` (`sq_le_of_written`, `alg4_written_lt`, `alg4_space`).
28. Correctness (Lemma 6.4) holds for *every* execution, with no bound on the number of `getTS`
    calls (`alg4_correct`). Wait-freedom (Lemma 6.14) is proved for executions with at most `M`
    `getTS` calls (`alg4_waitFreeUpTo`), as stated. Obstruction-freedom holds in general
    (`alg4_obstructionFree`).
29. Bounded model checking (atomic scan, all interleavings, `M ≤ 5`; random schedules up to
    `M = 25`) found no violation; the largest written index observed is about `√(2M)`.

## Model notes moved from the paper review

30. **[spec] Nondeterministic covering** (see 2): with nondeterministic choices "`p` covers `r`" lets
    a process cover several registers. This is a definitional imprecision, not an error of the
    proofs, which fix the choices.
31. **Algorithm 2 needs one-shot** (see 24): this matches the paper's claim, which is only for
    one-shot. The counterexample shows the restriction is essential, not that the paper is wrong.
32. **Non-vacuity of Theorem 1.1.** The paper does not need this, but we add the folklore "max + 1"
    long-lived algorithm from `n` registers (`MaxAlg.lean`, `MaxTS.maxTS_isTS`).

## Not formalized

- The historyless-object version of Theorem 1.2 (Section 7 remark).
- Nondeterministic and randomized implementations (see 1, 2). They reduce to deterministic ones
  with the same registers: before each step, read all registers and take the choice with the
  shortest solo-termination distance. This reduction is not formalized.
