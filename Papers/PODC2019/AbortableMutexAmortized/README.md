# Constant Amortized RMR Abortable Mutex — PODC 2019

Prasad Jayanti, Siddhartha Jayanti. *Constant Amortized RMR Abortable Mutex for CC and DSM.* PODC 2019.
DOI [10.1145/3293611.3331592](https://doi.org/10.1145/3293611.3331592). Formalized version: arXiv
[1809.04561](https://arxiv.org/abs/1809.04561) v1 (full version with all proofs); numbering follows it.

**Verdict: ⚠️ Minor statement issues.** The headline results hold for Algorithm 1: mutual exclusion,
starvation freedom, O(1) amortized RMRs per attempt in both the CC and DSM models, O(1) worst-case
Exit, Fast Abort and O(n) space. The new fairness property AFCFS is false as defined, because the
definition forgets passages that end with an abort; a corrected version holds. The distance function
of the starvation proof misses the case of line 11. The invariant of Theorem 4.1 is true but not
inductive, so its proof needs an extra conjunct.

## Mistakes in the paper

### ⚠️ Theorem 4.2 (AFCFS)
As defined, AFCFS fails whenever `p` aborts the last attempt of its passage: if `p` completes its
doorway and then aborts for good, a later process `p'` splices out `p`'s node and enters the CS
although `p` never enters the CS in that passage (`afcfs_literal_false`, a 13-step run with `n = 3`).

**Impact.** Only the new fairness notion is affected; the algorithm is as fair as intended. Under
the paper's definition no starvation-free abortable lock can satisfy AFCFS: a process that leaves
after its doorway would block every later process forever. The evident fix is local, and we prove
it: `p'` does not enter the CS before `p` enters the CS *or the Abort section* (`theorem_4_2`).

**Details.** A passage ends with a successful attempt "or the last attempt" (`j = k`). If `p`'s last
attempt is aborted and `p` never returns, the passage consists of aborted attempts only, and the
A-precedence relation is based on the doorway of that last attempt. The failure needs the strict
reading of "`p'` does not enter the CS before `p` enters the CS" (`p'` must wait for an entry of `p`
that never comes). Under the weaker reading "if both enter, `p` enters first", the definition already
says what is intended and Theorem 4.2 holds. Three things show the intended exception: the airline
analogy ("people behind you occupy your original position"), the paper's proof (it only orders
processes while they are in `Q`, and "leaves `Q` from any position" includes aborting), and the
fact that the strict reading cannot be met by any starvation-free abortable lock. We count it as a
definitional slip with an evident, local fix (R3). It is borderline, because AFCFS is the paper's own
new definition and the abstract lists it. It is not ❌, because the fix only adds the missing case
"unless `p`'s passage ends with an abort", the proof reasons with the intended version, and the
algorithm is unchanged.

**Repair.** `theorem_4_2` assumes that `p` is at line 3 at time `T` (it has just completed lines
1–2) and that `p'` begins a passage at a time `t' ≥ T` (`PassageStart`: `p'` is in the Remainder,
and its last step, if any, completed the Exit section). It concludes that whenever `p'` is at line 7,
`p` was at line 7, 9, 10 or 11 at some time in between. The proof keeps `p` ahead of `p'` in the
queue (`before_step`) and uses `I10`.

### ⚠️ Definition 4.1 / Lemma 4.4 (the digit function `f` misses line 11)
Equation (1) gives no value of `f` at line 11, so `δ(p)` is undefined when the prefix leader `q_m`
is an aborted process at line 11 (marked node, about to wake its successor), a case the proof of
Lemma 4.4 itself lists.

**Impact.** This is a local fix. With `f(11) = 4`, the only value between `f(10) = 5` and
`f(1) = 3`, Lemma 4.4 and Theorem 4.5 hold (`lemma_4_4_part1`, `lemma_4_4_part2`, `theorem_4_5`).

### Typos and slips
- Figure 1, `I7`: `*mynode_p` should be `*mynode_{q_i}`; `I9`: `go_{q₁}` should be `&go_{q₁}`.
- Lemma 4.4 should exclude an aborting step of `p` itself, after which `δ(p)` is undefined.
- Appendix C, Lemma 5.3, lines 3, 7, 9: the proof writes `α_CC(11)` for `α_CC(9)`.

## Proof gaps (statements true)

### 🛠️ Theorem 4.1 (the invariant `I` is not inductive)
The induction step for line 3 (case 3, splicing out an aborted predecessor) fails from a
configuration satisfying `I` in which the new predecessor's node still holds the spliced process's
go-address, after which `I7` fails (`paperInv_not_inductive`: `n = 3`, `Q = [r, x, π]`, `r` at line 3
with `*a_r = &go_x`, `x` aborted at line 11, `π` at line 3).

**Impact.** The statement is true: `I` holds in every reachable configuration (`theorem_4_1`). The
appendix's "the rest of the invariants continue to hold since they are unaffected" is the gap.

**Repair.** We add one conjunct (`Loc.x1`): an aborted queue member at line 1, 10 or 11 never has
its own go-address in its predecessor node, since it erased it at line 9. With this conjunct the
invariant is inductive (`inv_step`), and it implies `I` verbatim (`paperInv_of`). An exhaustive model
check of all 11 413 reachable configurations for `n = 2`, plus random runs for `n = 3, 4`, agrees.

### 🛠️ Lemma 5.3 (CC constant for lines 8 and 11)
The proof claims `α_CC(8), α_CC(11) ≤ 4`, but the write `*v ← true` also invalidates `go_q` in
`q`'s cache, which adds one more unit of potential, so the true bound is 5.

**Impact.** The statement ("bounded by a constant") is true (`lemma_5_3`, with exact per-line bounds
0, 1, 2, 5). The bound 5 is attained for `n = 2`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory with `n` processes `Fin n`, deterministic, no crashes, and an arbitrary
  scheduler (any schedule `σ : ℕ → Fin n × Bool`). Processes that have not "joined" yet are
  processes that stay in the Remainder section. The shared objects support Fetch&Store, read and
  write.
* One step is one shared-memory operation plus the local actions after it, as in the paper. Line 1
  is the Remainder section and line 7 is the CS.
* Abort signal: a step carries an abort flag that is used only at lines 4–6. An aborting step there
  jumps to the Abort section and executes line 9 in the same step. This follows the paper's
  convention that a step is one shared-memory operation plus any local actions, and a jump is a
  local action. Lemma 4.4 also holds when the jump is attached to the preceding operation instead.
  It would fail only if the jump were a separate, memory-free step, which the paper's convention
  rules out; see `differencies.md`.
* Starvation freedom assumes a fair schedule: every process outside the Remainder eventually takes a
  step. The process under consideration never aborts.
* RMR cost models:
  - **DSM:** an arbitrary placement of variables with `go_p` in `p`'s partition.
  - **CC:** per-process caches. Reads hit or miss; every Fetch&Store or write costs 1 and invalidates
    all copies. Caches start empty.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.1 (invariant `I`, Figure 1) | `theorem_4_1` (`PaperInv` = Figure 1 verbatim) | `PaperInv.lean` |
| Theorem 4.1 (uniqueness of `k, A, Q`) | `theorem_4_1_unique`, `unique_of_I1_I4` | `PaperInv.lean` |
| `I` is not inductive (proof gap) | `paperInv_not_inductive` | `NotInductive.lean` |
| Strengthened inductive invariant | `inv_step`, `Reachable.inv` | `Invariant.lean` |
| Corollary 4.1.1 (mutual exclusion) | `mutual_exclusion` | `PaperInv.lean` |
| Theorem 4.2 (AFCFS) as stated: **false** | `afcfs_literal_false` | `AFCFS.lean` |
| Theorem 4.2 corrected | `theorem_4_2` | `AFCFS.lean` |
| Lemma 4.3 | `lemma_4_3` | `Starvation.lean` |
| Lemma 4.4 (with `f(11) = 4`), `Ψ ≠ ∅` | `lemma_4_4_part1`, `lemma_4_4_part2`, `promoters_spec` | `Starvation.lean` |
| Theorem 4.5 (starvation freedom) | `theorem_4_5` | `Starvation.lean` |
| Theorem 5.1 (space: `2n + 2` shared variables) | `theorem_5_1` | `RMR.lean` |
| Lemma 5.2 (DSM line costs, paper's constants) | `lemma_5_2` | `RMR.lean` |
| Lemma 5.3 (CC line costs) | `lemma_5_3` | `RMR.lean` |
| Theorem 5.4 (≤ 8 DSM / ≤ 12 CC RMRs per attempt) | `theorem_5_4_dsm`, `theorem_5_4_cc` | `RMRTheorem.lean` |
| Theorem 5.4 (worst-case Exit, Fast Abort) | `theorem_5_4_exit`, `theorem_5_4_fastAbort`, `dsmCost_le_one`, `ccCost_le_one` | `RMR.lean`, `RMRTheorem.lean` |

**Proof remarks.**
* The invariant is stated through pointers rather than indices. `Struct` says that `Q` is a
  `pred`/`mynode` chain from `a₀` to `tail` (`Chain.lean`). Membership in `Q` is read off locally:
  lines 3–7, 9, 10, or line 1/11 with a marked node. `Loc` holds the remaining conjuncts plus `x1`.
* Each step changes `Q` in one of four ways (`QStep`): unchanged, append, splice, or removal of the
  head. Lemma 4.4 and AFCFS are proved from this.
* In Appendix B, "one digit fewer ⇒ smaller" needs a nonzero leading digit, which follows from `I6`
  and `I8`. Theorem 4.5 also needs `Ψ(p) ≠ ∅`, which follows from `I11`.
* Theorem 5.4's "the lines outside the loop are executed at most once per attempt" becomes a
  remaining-budget potential `Σ_p c(pc_p)`.
* Theorem 5.4's Fast Abort bound of six shared-memory instructions is correct; we prove the
  sharper bound of five own steps (`theorem_5_4_fastAbort`), because line 1 belongs to the
  Remainder section.

**Not formalized.** Nothing of substance. "Space O(n)" is formalized as the count of shared
variables.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Counterexamples are checked by `decide +kernel`. Non-vacuity checks:
* `fair_roundRobin`: a fair schedule exists.
* `stdHome`: a DSM placement with `go_p` local to `p` exists.
* `afcfsRun`: the AFCFS hypotheses are met.

The Python model checkers used to validate the invariant, Lemma 4.4 and the per-line costs are in
[`modelcheck/`](modelcheck/); they are not part of the Lean development. The model is paper-local and
does not use CSLib's shared-memory framework. CSLib candidate: the generic pointer-chain lemmas
of `Chain.lean`.
