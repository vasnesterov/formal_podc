# Differences between the formalization and the paper

Every checked statement is true as written; the issues below are gaps in proofs or modelling choices.

## Proof gaps and repairs

1. **Lemma 4.2, proof (genuine gap, 🛠️).** "Let `z` be a value whose root-to-leaf path in `T₂` does not
   include `r₁`. Such a value must exist since `r₁` is not the root of `T₂`." False for complete decision trees:
   root reads register 1, both children read register 0; every path reads 0 (`lemma_4_2_gap`). The remainder of
   the proof is correct and proves `lemma_4_2_core` (= `Sec4.caseA`). Lemma 4.2 as stated ("`T₁` and `T₂` have the
   same root") is stated inside the proof by contradiction of Theorem 4.1, i.e. under its hypotheses; since
   these are contradictory, it holds trivially once Theorem 4.1 is proved (`lemma_4_2`, from `setting_false`).
   This is the normal status of an intermediate step of a reductio, not a defect; the defect is that its
   proof does not establish it. We did not find a direct proof of "same root" from the facts available at that
   point (Lemmas 3.3–3.4, invisibility, atomicity), and none is needed. `lemma_4_2_gap` refutes the inference
   "r₁ not the root of T₂ ⇒ some path of T₂ avoids r₁" for abstract complete decision trees without repeated
   registers; it is a claim inside a proof, not a stated lemma. Lemma 4.2 itself is true; only its proof is wrong.
2. **Theorem 4.1, repaired structure.** The main argument (writes `W₀(a) W₁(z) W₂(b)`) only needs that `b`'s path
   in `T₂` reads the root register `ρ` of `T₁`. We case-split on "some path of `T₂` avoids `ρ`". If yes, we use
   the Lemma 4.2 argument (`caseA`). If no, every path of `T₂` reads `ρ` at some depth, and we use the main
   argument (`caseB`). In Case 1, `R₂` runs entirely at one memory where `ρ = 1`. If it returned `b`, its path
   would be `b`'s path, which reads `ρ` at some depth and gets 0 in the quiescent state after `W₂`. Contradiction.
3. **Theorem 4.1, Case 1 when the first write of 1 to `x` is inside `W₁`.** Then `R₁` (prefix before `W₁`, last
   read right after that write) returns `b` although only `a`, `z` were written: regularity is already violated.
   The paper's continuation would also work if `R₂` is scheduled after `W₁` ends; we treat the case separately
   (Case 1a in `caseB`).
4. **Theorem 4.1, Case 2 wording.** "`R₁` cannot return `b`, since `R₁` read 0 in `x`" — `R₁` need not read `x` at
   all. Correct argument (formalized): regularity forces `R₁` to return `b`, so its path is `b`'s path, whose last
   read is `x` with value 1; but `x = 0` throughout `R₁`.
5. **Theorem 4.1, exhaustiveness of the two cases.** The first write of 1 to `x` and the first write of 0 to `r`
   in `W₂` are different steps because one step writes one register (`wMem_succ_eq_of_ne`); the paper uses this
   silently.
6. **Lemma 3.3, depth bound.** The paper bounds the depth of every path of the decision tree by the step bound;
   the bound only applies to paths realized in executions (code on unrealized branches is unconstrained, the
   tree as defined may be infinite there). We count only the paths realized by the executions `σ_v`. They are a
   prefix-free family of `k` binary strings of length `≤ log₂ k` (`SeqReads.prefixFree`), so they are exactly
   the strings of length `log₂ k` (`complete_of_prefixFree`). Routine.
7. **Theorem 3.2, last step.** With only *reads* bounded, the simulated read may write. "`WP` writes 1 to each of
   the `log₂ k` registers read" needs that the reader did not write them itself. Lemma 3.4's argument shows more:
   every read of the first read accesses a register for the first time (`SeqReads.fresh`, `lemma_3_4`), so the
   value read is the one left by the write. Minor gap.
8. **Theorem 3.2, "WLOG the initial value of every base register is 0".** Instead of relabelling we pick the path
   whose bits are the complements of the initial memory (`SeqReads.exists_far`, for any memory `M₀`).

## Statements: differences in form (results at least as strong)

9. **Theorem 3.1** counts base *reads* (paper: steps; a strengthening, since reads ≤ steps), and does not assume `k` is a power of 2: some read has
   `k ≤ 2^#reads`, i.e. `⌈log₂ k⌉ ≤ #reads`. The witness is the first read after a solo write.
10. **Theorem 3.2 / Corollary 3.5.** `k = 2^m` as in the paper. Hypothesis: every read operation of one reader
    `r` performs at most `m` base reads (paper: "the simulated read", presumably of all readers). Conclusion: some
    write operation of `w` performs at least `m` base writes (paper: "the simulated write uses at least `log₂ k`
    writes" in the worst case); the witness is a solo write from the initial configuration.
11. **Theorem 4.1.** Hypothesis: two readers `r₁ ≠ r₂` whose read operations take at most `m` steps each
    (paper: "a simulated read that takes at most `log₂ k` steps, assuming there are at least two readers").
    `k = 2^m > 2` as in the paper. `k > 2` is necessary (`theorem_4_1_needs_k_gt_two`).
12. **Only first reads matter.** All proofs use only the first read of each reader. The hypotheses are stated for
    all read operations of the named readers, as in the paper.

## Model choices

13. CSLib's shared-memory model: deterministic processes (the paper's decision trees presuppose determinism),
    finite executions as label lists, no crashes (crashes are irrelevant to the constructed executions). A return
    is a separate step that accesses no base object; the costs count base accesses only.
14. Single writer: `Impl.allowed` is arbitrary; the consistency conditions are required only in executions in
    which only `w` writes (weaker hypothesis than requiring it in all executions). Readers are any processes
    allowed to read.
15. Consistency conditions need an initial value `v₀` of the simulated register; the paper does not mention it.
    All constructed reads start after a completed write, so `v₀` never matters.
16. Atomicity = linearizability with CSLib's (amended Herlihy–Wing) `IsLinearization`, including pending
    operations. Regularity / safety are defined on histories (`RegularValue`: `v₀` if no write precedes the read,
    or the value of a write that does not follow the read and is not overwritten before it). Atomic ⇒ regular ⇒
    safe is proved (`regularHist_of_atomicHist`), so Theorem 4.1 uses safety/regularity where the paper does.
17. Base registers have arbitrary initial values (`memInit`); the paper assumes 0 WLOG.
18. Wait-freedom: CSLib's `WaitFree` (no process takes infinitely many steps in one operation); the proofs use
    only obstruction-freedom (`WaitFree.obstructionFree`), which gives termination of the solo operations.

## Not formalized

19. Tightness claims (abstract, Section 1): the algorithms of [6] (safe) and [4] (regular) matching the bound
    of Theorem 3.2, and the upper bound `1 + 2·log₂ k` of [5] for the atomic case.
20. The closing remark of Section 4: one reader suffices if its first two reads start by reading the same
    register (the hypothesis is not precisely defined in the paper; the second read's tree depends on the first
    read's outcome).
