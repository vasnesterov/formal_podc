# Differences between the formalization and the paper

Paper: Baïg, Hendler, Milani, Travers, *Long-Lived Snapshots with Polylogarithmic Amortized Step
Complexity*, PODC 2020, full version HAL hal-02860087v1. References `[4]` = Aspnes, Attiya,
Censor-Hillel, Ellen (J. ACM 2015), `[12]` = Baig et al. (DISC 2019).

## Errors in the paper (statement level)

1. 🛠️ **Lemma 3.3 is false** (`Counterexample.lemma_3_3_false`, `n = 4`, `m = 16 = n²`, 4-bounded
   increments, every helping period `X`). The order defined by linearization rules 1–3 puts
   `MaxUpdate(right, 3)` (rule 3: at `Q`'s write of `MA_0.right`) before the `MaxScan` of `S` (rule 1:
   at its later scan of `MA_1`), which returns `(16, 0)`. Claim 4 and the "value of `O`" of
   Definition 3.2 fail on the same execution: when the active array jumps from `MA_0` to `MA_1`, the
   right component of `O` drops from `3` to `0`. The paper's rules are formalized generally
   (`stepPC`, `Rule3Point`, `Rule1Point`); following the paper's wording "(line 11 or line 12)", rule 3
   counts the reads of `MR_right` at line 12 only (adding line 10 changes nothing in the
   counterexample), and rule 1 is applied to `MaxScan` operations.
   The algorithm itself is linearizable (item 5).
2. 🔧 **Lemma 3.4 is false as stated** (`Counterexample34.lemma_3_4_false`, `n = 4`, `m = 16`,
   `b = 4`, `X = 4`). After `K = 3` unsuccessful iterations of `S`, only `3` `MaxUpdate`s were invoked
   during `S`, while the lemma claims `⌈(K−2)m/b⌉ = 4`. The proof's step "each `WriteMax` that takes
   effect during `S` belongs to a `MaxUpdate` that started during `S`" ignores the up to `n − 1`
   `MaxUpdate`s that started before `S`. The fix changes
   what is counted, and the proof reasons with the wrong version. The corrected statement, counting
   the `WriteMax` steps during the iterations, is `WaitFree.lemma_3_4`. The number of unsuccessful
   iterations is `S`'s counter `c`, which Algorithm 1 increments once per unsuccessful iteration.
   *Helping period.* The Lean execution uses `X = 4`, whereas the paper's period at `n = 4`, `m = 16`
   is `⌊4/16⌋ = 0` (intended `⌈4/16⌉ = 1`). The statement of Lemma 3.4 does not involve helping, and
   the flaw does not depend on `X`: for large `n` with `m = n²` (e.g. `n = 2^12`, where
   `⌊n/log² m⌋ = 7 ≥ 3`, so no collect happens in the first three iterations), `n − 2` pending
   `MaxUpdate(left, ·)`s and one pending `MaxUpdate(right, ·)`, invoked before `S` with
   `MR_left = MR_right = m − 1`, make the first two iterations fail and bring `MR_left` to
   `2m − 3n`; three new `MaxUpdate`s then make the third fail, so `3 < n = ⌈m/n⌉` `MaxUpdate`s start
   during `S`. (Reviewer's sketch, not formalized.)
3. ✏️ **Helping period `⌊n/log² m⌋` (lines 23, 25)**. With `m ≥ n²`, `log² m ≥ 4 log² n > n` for all
   `n < 256` (when `m = n²`), so the period is `0` and line 25 is `c mod 0`. Moreover, line 25 is
   reached already for `c = 0`, before the first collect of line 24, and then compares with an
   undefined `h₀`. Read as "never collect again", period `0` disables helping; a scanner can then
   starve, because a fast updater crosses a multiple of `m` during each of its iterations (sketch,
   not formalized). The proof of Lemma 3.5 uses `⌈n/log² m⌉`, and the text
   says that line 25 is "not the first collect". We model the intended version: a parameter `X`
   (`≥ 1` for wait-freedom), first collect at `c = X`, further collects at `c > X` with `c % X = 0`
   (`afterFail`). Under the literal reading, the useless collect at `c = 0` also costs `n` extra steps
   for every `CompScan` whose first iteration fails; we did not analyse whether this breaks the
   amortized bound, because the intended version does not have it.

## Proof gaps (statements true)

4. **Lemma 3.1 / Claims 1–2** are not formalized separately. The real-time property of our
   linearization comes from the max-array criterion. Claim 1 (an indirect view was computed inside
   the reader's interval) is part of the invariant: `PFL` for `col`, `HInv`, and the timestamp
   argument in `pfl_col`.
5. 🛠️ **Theorem 3.7, linearizability.** Repaired (`alg1_linearizable`). We use certified views
   (`Cert`): the time `t₀` of the line-11 read, the time `t₁` of the line-17 scan, constant
   high-order bits on `[t₀, t₁]`, `MR(t₀) ≤ view ≤ MR(t₁)`, and components that are actual values of
   the max registers. Certified views are ordered by `t₁` (`cert_le`). Every completed operation has
   a certificate inside its interval (`OpCert`). Every nonzero component is the value of an invoked
   `MaxUpdate` (`WInv`). The PODC 2012 criterion `exists_isLinearization_maxArr` then applies.
   Claim 3 corresponds to the facts in `pfl_scanMA` / `pfl_chkR`, and Observations 1–3 to
   `pair_of_sum` / `ma_facts`. The proof holds in **every** execution and for every `m` (also
   `m < n²`), because the max registers are atomic. The bounded-increment hypothesis of the theorem
   is only needed for the black box `[12]`.
6. 🔧 **Lemma 3.5 (wait-freedom).** Proved (`WaitFree.iterations_le`: at most `2X + K` iterations when
   `2nℓ < (K−2)m`, which is the paper's `⌈(K−2)m/ℓ⌉ ≥ 2n+1`; `WaitFree.steps_le`: at most
   `(2X+K)(n+9)+1` accesses per operation; `WaitFree.waitFreeOn_BIExec`). The paper's proof uses the
   false Lemma 3.4, and its interval `I₁` is one iteration short, since the first collect happens in
   iteration `X + 1`. Counting `WriteMax` steps inside `I₂` gives three writes by one process, hence
   two complete `CompScan`s inside `I₂`. `I₃` needs only `X − 1` iterations, so the total `2X + K`
   is unchanged. Requires `X ≥ 1` (item 3).
7. **Lemma 3.6 (amortized `O(log² n)`).** Only the counting core is formalized:
   - `Amortized.fails_le`, per process: the number of unsuccessful iterations is at most the final
     `h* = ⌊MR_left/m⌋ + ⌊MR_right/m⌋` (Observation 6);
   - `Amortized.lemma_3_6_unsuccessful`: `m · |L_u| ≤ n · ℓ · |W|` (eqs. (6)–(7));
   - `lemma_3_6_unsuccessful_of_le`: `|L_u| ≤ |W|` when `nℓ ≤ m`.

   Here `|W|` is the number of line-4 `WriteMax` steps. The step costs of the black boxes (`O(log n)`
   amortized for `[12]`; `O(log m)`, `O(log² m)` for `[4]`) and the final summation (eqs. (3)–(5)) are
   not formalized; they are routine given the counting bound.
8. 🔧 **Bounded max arrays of `[4]`.** Algorithm 1 relies on `[4]`'s `(m × m)` max array being
   linearizable; as published it is not (Theorem 3.4 of `[4]` is false; see
   `Papers/PODC2012/LimitedUseSnapshots`). We take `MA_j` atomic, i.e. we assume the erratum's
   corrected max array. Its `MaxUpdate₁` costs `O(log² m)`, which eq. (4) already charges per
   iteration through the `MaxScan`. Whether Algorithm 1 is correct over the uncorrected max array
   (every `MaxUpdate` of Algorithm 1 is followed by a `MaxScan` of the same process, unless it
   crashes) is not checked.
9. **Lemmas 4.1 and 4.2.** Proved over atomic max arrays for arbitrary trees, with bound
   `|leaves of the child|` (`2^{h−1}` for the balanced tree) and `n` for `root.MR`
   (`Section4.lemma_4_1`, `Section4.lemma_4_2`, `lemma_4_1_access`). Differences from the paper:
   - The proof is an invariant (`RepInv`: `count_j ≤ seq[x]_j + owe`), not the paper's history
     argument. The paper's induction on height, which uses Theorem 3.7 for the lower max arrays, is
     not needed with atomic objects. The composition step (real-time precedence of non-atomic
     `WriteMax`) is not formalized.
   - Claim (1) implicitly uses `[4]`'s invariant that an index is the sum of leaf pointers.
   - ✏️ Claim 5 leaves `(L_u, R_u)` undefined when no `MaxUpdate` of `I` touches `u.MA`, and `v'` may
     be the initial `0`; we take `(0, 0)` and `0`.
   - ✏️ Index slip: `x` of height `h + 1` with bound `2^{h−1}`.
   - The proof of Lemma 4.2 (embedding into a `2n`-process tree) is replaced by the same invariant at
     the root.
10. 🔧 **Theorem 4.4.** The paper's proof is a reference to `[4]` §4.1, whose linearization points are
    wrong. The statement holds with the repaired points (`Snapshot.theorem_4_2`, re-exported as
    `Section4.theorem_4_4_linearizable`), for unbounded atomic objects and therefore unlimited use.
    Wait-freedom and the per-operation weighted costs come from `[4]`'s Lemma 4.3 as formalized
    there (`theorem_4_4_update_cost`, `theorem_4_4_scan_cost`). The amortized `O(log³ n)` (Lemma 4.3
    of this paper) is the sum of the black boxes' amortized costs and is not formalized.

## Modelling choices

11. All base objects are atomic: `MR_left`, `MR_right` (unbounded max registers), `MA_j` (max arrays;
    only values `< m` are written to them, which is not enforced), `H[i]` (registers). CSLib has no
    composition theorem; the composition with `[12]` and `[4]` is by locality, informally.
12. Definition 2.1 is stated on the sequence of values written to a max register. With atomic writes,
    "precedes" is the order of the steps. `boundedIncr_iff_stepBounded` shows it equivalent to
    "each write is at most the previous maximum plus `ℓ`".
13. `Collect(H)` reads `H[0], …, H[n−1]` in this order, one access each. Line 27 picks the least
    eligible `j` (the paper allows any). Line 18 reads `MR_left` first, and reads `MR_right` only if
    the left test passed. Lines 20–21 are one step: the local increment and the write.
14. `MaxUpdate` returns the dummy response `(0, 0)`. The max array is `maxArrObj` of the PODC 2012
    formalization (`upd0` = left, `upd1` = right).
15. Rule 3 says the reads of `MR_side` happen "in line 11 or line 12": line 11 for the left side and
    line 12 for the right side (the line-10 read `r₁` is never written to an `MA`), which is what
    `isReadMR` formalizes.
16. The concrete counterexample of Lemma 3.3 is checked for every `X` with a small tactic
    `kernel_decide_fvar` (`of_decide_eq_true rfl`, evaluated by the kernel), because `decide +kernel`
    refuses goals with free variables. The Lemma 3.4 counterexample uses `X = 4` and plain
    `decide +kernel`.
