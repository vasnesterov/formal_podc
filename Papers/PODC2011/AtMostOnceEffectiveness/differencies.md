# Differences between the formalization and the paper

Paper: Kentros, Kiayias, *Solving the At-Most-Once Problem with Nearly Optimal Effectiveness*, PODC 2011;
full version arXiv 1107.2990v2 (TCS 2013). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Model (Section 2)

1. **I/O automata → deterministic step model.** Every process is a deterministic program whose state
   determines its unique enabled locally controlled action: read, write, `do_{p,j}`, internal step, or
   none (terminated). `KK_β` has this form: every status enables exactly one action. Per-action
   fairness of the paper is then equivalent to per-process weak fairness, which is what we use.
2. **Crashes as fairness exemptions.** `stop_p` is not an action. A run is `Fair F` if each process
   outside `F` steps infinitely often or terminates, and runs may stutter (`ev k = none`). A paper
   execution with crash set `F` and a finite fair execution followed by stuttering are both such runs,
   and conversely. So `effectiveness` is exactly the paper's `min_{α ∈ fairexecs_f} Do(α)`, written
   as an `sInf`.
3. **Jobs and registers.** Jobs are the numbers `1..n`, and `0` means "no job". The `done` matrix is
   modelled by unbounded lines `done q j` (`j ≥ 1`). By the invariant, writes only ever go to positions
   `≤ n`, and readers check `POS ≤ n` as in the paper.
4. **Process identifiers.** Processes are `Fin m`, with paper identifier `p.val + 1`. The loop index
   `Q_p` is stored 0-based. `TMP_p` is not stored, since it only carries values within one action.
5. **`FREE_p` is defined as `J \ DONE_p`.** The paper updates `FREE_p` and `DONE_p` in lockstep, so
   this equality is invariant; no behaviour changes.
6. **`rank` is clamped.** `rank(S, k)` returns the element of rank `min k |S|`. The paper's rank is
   undefined for `k > |S|`, which can occur only for `β < m`. For `β ≥ m` the clamping never triggers
   (`kIdx_le_avail`).
7. **`compNext` rank.** The paper's rational `TMP_p = (|FREE_p| − (m−1))/m` and the rank
   `⌊(p−1)·TMP_p⌋ + 1` (if `TMP_p ≥ 1`, else `p`) become `kIdx m p F` in ℕ: if `2m − 1 ≤ F` the rank
   is `p·(F − (m−1))/m + 1` (0-based `p`), else `p + 1`. These are the same for `m ≥ 1`.
8. **Theorem 2.1 for deterministic algorithms.** `effectiveness_le_sub` is proved for all algorithms
   of our model, i.e. deterministic processes, which includes every algorithm of the paper. Kentros
   et al. state it for all I/O automata, including nondeterministic ones. We do not need the paper's
   assumptions `n ≥ m` and `f < m`.

## Statements

9. **Lemma 4.1** (`lemma_4_1`): proved for every `β ≥ 1`, with any `m` and `n`. For `β = 0` a process
   may "choose" from an empty set; the paper's algorithm is undefined there. The paper says
   correctness holds also for `β < m`, where its `rank` is undefined. With clamping, safety holds for
   all `β ≥ 1`. Slip, not a statement error (typo item in README).
10. **Lemma 4.2** (`lemma_4_2`, `lemma_4_2_extend`). The paper's "for any finite execution α ∈ execs"
    must be read as "with at most `f ≤ m − 1` crashes". Otherwise the lemma is trivial in IOA, where
    `stop_p` is always enabled, or false if stops are excluded and all processes crashed. The
    hypothesis `Do(α) ≤ n − (β + m − 1)` is stated additively as `Do + (β + m − 1) ≤ n` to avoid ℕ
    truncation. We also prove the stronger fact that no process has terminated (`lemma_4_2`). Rule:
    R4 (implied assumption), recorded as a proof-gap item (🛠️), since the intended statement is true.
11. **Lemma 4.3** (`lemma_4_3`). Stronger than the paper: for `β ≥ m`, *every* run takes finitely many
    steps, with no fairness or crash-bound hypothesis. An infinite run is always fair for the set of
    processes that step finitely often, so this is equivalent to "no infinite fair execution". The
    paper's proof has a gap, since `POOL_α` ignores jobs held by terminated processes. It is repaired
    with `pool` (README 🛠️ item). The paper's Cases A/B and A.1/A.2 are merged: any synchronised
    `compNext` of `p₀` whose `TRY` was gathered late enough picks `x₀`.
12. **Theorem 4.4.**
    - The lower bound `E ≥ n − (β + m − 2)` is proved for all `f ≤ m − 1` (`theorem_4_4_ge`), and per
      fair run (`theorem_4_4_do_ge`).
    - Equality is proved for `f = m − 1` and `n ≥ β + m − 1` (`theorem_4_4`). The adversary is
      `exists_fair_run_do_le`: processes `1..m−1` announce distinct jobs and crash, and process `m`
      runs solo. The paper only sketches it ("it is easy to see").
    - **False for `n ≤ β + m − 2`** (`theorem_4_4_false_small`: `m = n = β = 2`, `f = 1`, `E = 1 ≠ 0`).
      Rule R2 (degenerate: the claimed value is `≤ 0`, a parameter corner outside the range the
      paper uses), hence ⚠️ rather than ❌.
    - **False for `f < m − 1`** (`theorem_4_4_false_few_crashes`: `m = 2`, `β = 4`, `n = 5`,
      `f = 0`: the formula gives `1`, but `E ≥ 2`; proof in `FewCrashes.lean` via the invariants
      `u1`, `invA`, `invB` and wait-freedom). Model checking gives more cases inside the paper's
      hypotheses, e.g. `(9, 2, 6, 0)` (`E = 4` vs `3`) and `(8, 3, 6, 1)` (`E = 2` vs `1`, with a
      crash). The paper's adversary crashes `m − 1` processes, so its proof only covers `f = m − 1`.
      Rule: not excused by R4, since Theorem 4.4 explicitly says "for any β ≥ m, f ≤ m − 1" and
      Definition 2.4 makes `f` a genuine parameter (the paper itself computes `E = (m − f)·n/m` for the
      trivial algorithm); not excused by R3, since restricting to `f = m − 1` drops content of the
      claim. Hence ❌.
    - Borderline call (R5/R6): ❌ rather than 🚨. The abstract's headline "effectiveness `n − 2m + 2`"
      is `β = m`, compared there with the bound `n − m + 1 = n − f` for `f = m − 1`, so it is read as
      the worst case `f = m − 1`, which is proved (`kk_m_effectiveness`, `n ≥ 2m − 1`). For `β = m`
      and `f < m − 1` no counterexample was found (model checking `m = 2`, `n ≤ 7`; `m = 3`, `n ≤ 6`
      partially). Even under a reading of the headline for all `f`, it would only be unestablished,
      which R5 also rates ❌.
13. **Theorem 2.1** (`effectiveness_le_sub`): holds without `n ≥ m`, `f < m` or `0 < m` (see 8).

## Not formalized

14. Section 5 (work complexity `O(nm log n log m)` for `β ≥ 3m²`, Definitions 5.1–5.3, Lemmas 5.1–5.5,
    Theorem 5.6). This would need a work-cost model of the red-black-tree operations.
15. Section 6 (`IterativeKK(ε)`, Lemmas 6.1–6.2, Theorems 6.3–6.4) and Section 7 (Write-All, Theorem 7.1).
16. The remarks on `β = O(m)` being asymptotically optimal, and the comparison with [26] (`n − log m · o(n)`).
