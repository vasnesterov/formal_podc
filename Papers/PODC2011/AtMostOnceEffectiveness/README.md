# At-Most-Once with Nearly Optimal Effectiveness — PODC 2011

Sotirios Kentros, Aggelos Kiayias. *Solving the At-Most-Once Problem with Nearly Optimal Effectiveness.*
PODC 2011. DOI [10.1145/1993806.1993847](https://doi.org/10.1145/1993806.1993847). Formalized version: arXiv
[1107.2990](https://arxiv.org/abs/1107.2990) v2 (Dec 2013, the full TCS version with all proofs); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** `KK_β` never performs a job twice (Lemma 4.1), is wait-free for `β ≥ m` (Lemma 4.3), and
with up to `m − 1` crashes has effectiveness exactly `n − (β + m − 2)` (Theorem 4.4 for `f = m − 1`), which for
`β = m` is the abstract's `n − 2m + 2`; Theorem 2.1 (`E ≤ n − f` for every algorithm) holds too. Theorem 4.4 claims
the same value for *every* `f ≤ m − 1`, and with fewer crashes the effectiveness can be larger, so "=" becomes "≥"
there, and the proof of Lemma 4.3 needs one definition changed. The work bounds, `IterativeKK(ε)` and Write-All were
not checked.

## Mistakes in the paper

### 🔧 Theorem 4.4 (equality for `f < m − 1` crashes)
The theorem claims `E_{KK_β}(n, m, f) = n − (β + m − 2)` for every `f ≤ m − 1`, but with fewer
crashes `KK_β` can be forced to perform more jobs: for `m = 2`, `β = 4`, `n = 5 = β + m − 1` and
`f = 0` the formula gives `1`, yet every fair execution performs at least `2` jobs
(`theorem_4_4_false_few_crashes`).

**Impact.** The lower bound `E ≥ n − (β + m − 2)` holds for all `f ≤ m − 1` (`theorem_4_4_ge`), and
the value is exact for `f = m − 1` (`theorem_4_4`), which is the case the abstract's `n − 2m + 2`
and its comparison with the bound `n − m + 1 = n − f` refer to. Only the "=" for `f < m − 1` is
false. The paper's matching adversary crashes `m − 1` processes, so its proof covers only `f = m − 1`.

**Details.** With `m = 2`, `β = 4`, `n = 5` and no crash, process 1 always picks the smallest
available job, and process 2 always picks an element of rank `≥ 2`. So process 2 never announces
job 1 (`u1`), and process 1 performs job 1 in its first iteration (`invA`). Process 2's first
target is job 3. While only job 1 is done, process 1 announces only jobs 1 or 2, so process 2's
first `check` cannot fail and it cannot terminate before performing a job other than 1 (`invB`). By
wait-freedom and fairness both processes terminate, so at least two jobs are performed
(`kk254_do_ge`). Exhaustive model checking ([kk_modelcheck.py](kk_modelcheck.py)) finds more
counterexamples, also with crashes and well above `n = β + m − 1`: `(n, m, β, f) = (9, 2, 6, 0)`
has `E = 4` against `3`, and `(8, 3, 6, 1)` has `E = 2` against `1`.

**Repair.** Theorem 4.4 with `f = m − 1` (`theorem_4_4`), plus the lower bound for all `f ≤ m − 1`
(`theorem_4_4_ge`).

### ✏️ Slips
- Theorem 4.4 (small `n`): for `n ≤ β + m − 2` the formula `n − (β + m − 2)` is `≤ 0`, the regime where the
  paper's guarantee is vacuous (fewer than about `β + m` jobs), but `KK_β` can be forced to perform jobs: for
  `m = n = β = 2` and one crash the effectiveness is `1`, not `0` (`theorem_4_4_false_small`). As long as no job has
  been performed, process 1 always targets job 1 and process 2 always targets job 2, so no `check` fails and no
  process can reach `end` before some job is done (`noJob_inv`); a fair run with at most one crash therefore performs
  a job (`kk222_do_pos`), and Theorem 2.1 gives `E ≤ n − f = 1`. Our exhaustive model checker shows the same for
  other small cases: `n = m = β = 3` with `f = 2` also has `E = 1`, against a formula value of `−1`. For
  `n ≥ β + m − 1` and `f = m − 1` the theorem holds as stated (`theorem_4_4`).
- Lemma 4.2: stated for "any finite execution", which in the I/O-automaton model is trivially true (the input
  `stop_p` is always enabled), whereas the intended statement needs at most `m − 1` crashes and an extension by a step
  of a live process; it holds in that reading (`lemma_4_2_extend`). We also prove the stronger form: while fewer than
  `n − (β + m − 2)` jobs are done, no process has terminated (`lemma_4_2`).
- `rank(FREE_p, TRY_p, p)` is undefined when `|FREE_p \ TRY_p| < p`, which can only happen for `β < m`. The text
  nevertheless says correctness holds for `β < m`. We clamp the rank; safety holds for all `β ≥ 1`.

### Typos
- Fig. 1 declares `TMP_p ∈ {0, …, n}`, but `compNext` stores the rational `(|FREE_p| − (m−1))/m` in it.

## Proof gaps (statements true)

### 🔧 Lemma 4.3 (wait-freedom, the set `POOL_α`)
The proof claims that no process other than `p₀` ever holds the job `x₀` of rank `k_{p₀}` in
`POOL_α = J \ (J_α ∪ STUCK_α)`, but `STUCK_α` excludes only jobs of *crashed* processes, while a
*terminated* process keeps its last, possibly abandoned and unperformed, job (maybe `x₀`) in `next`.

**Impact.** Statement true; repaired (`lemma_4_3`).

**Repair.** Define `POOL` as the unrecorded jobs minus the `next` values of *all* processes that stop
taking steps, crashed or terminated (`pool`). With this change the paper's argument goes through. We
prove a stronger statement: `KK_β` has no infinite execution at all, fair or not.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory with `m` deterministic processes (`Fin m`) and atomic read/write registers
  (`Model.lean`). Each process has exactly one enabled locally controlled action per state, as in the
  paper's I/O automaton.
- `KK_β` is transcribed action by action from Figure 2 (`kk`, `Algorithm.lean`). `FREE_p` is not
  stored but defined as `J \ DONE_p`, which the paper's updates keep invariant.
- Crashes are fairness exemptions: a run is `Fair F` if every process outside `F` steps infinitely
  often or terminates. Runs may stutter, so finite fair executions (all live processes terminated) and
  infinite ones are both runs. This matches the paper's `fairexecs_f`, where at most `f` processes
  receive `stop`.
- The adversary is omniscient and online, i.e. it chooses any schedule. There is no randomness.
- `Do(α)` counts the distinct jobs of `{1, …, n}` performed. Effectiveness is the infimum of `Do` over
  fair runs with at most `f` crashes (Definition 2.4).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.1, 2.2, 2.4 | `Alg.Run.Do`, `Alg.AtMostOnce`, `Alg.effectiveness` | `Model.lean` |
| Theorem 2.1 (`E ≤ n − f`) | `effectiveness_le_sub` | `UpperBound.lean` |
| Algorithm `KK_β` (Figs. 1–2) | `kk` | `Algorithm.lean` |
| Lemma 4.1 (at-most-once) | `lemma_4_1` | `Safety.lean` |
| Lemma 4.2 | `lemma_4_2`, `lemma_4_2_extend` | `Progress.lean` |
| Lemma 4.3 (wait-freedom) | `lemma_4_3` | `WaitFree.lean` |
| Theorem 4.4, lower bound | `theorem_4_4_ge`, `theorem_4_4_do_ge` | `Main.lean` |
| Theorem 4.4, adversary | `exists_fair_run_do_le`, `exists_fair_run_do_eq` | `Adversary.lean` |
| Theorem 4.4 (`f = m − 1`, `n ≥ β + m − 1`) | `theorem_4_4` | `Main.lean` |
| Abstract: effectiveness `n − 2m + 2` | `kk_m_effectiveness` | `Main.lean` |
| Theorem 4.4 fails for `n ≤ β + m − 2` | `theorem_4_4_false_small` | `Degenerate.lean` |
| Theorem 4.4 fails for `f < m − 1` | `theorem_4_4_false_few_crashes` | `FewCrashes.lean` |

**Proof remarks.**
- Safety (`Inv`, `Safety.lean`) is one inductive invariant. Its core replaces the paper's case analysis
  on the order of events by two invariants. `K`: two processes that announced the same job and read
  each other saw it. `L`: a process that read `next_p` after `p` claimed the job has it in `TRY` or
  `DONE`, or will read it from `p`'s line of `done`.
- Lemma 4.3 is proved by contradiction (`WaitFree.lean`). First, after a time `K0` the `done` matrix
  and the non-stepping processes are frozen. A measure shows that every live process keeps cycling
  through `compNext … check`. Then three stable predicates are established: `Synced`, `TryFull` and
  `GoodNext`. Finally the smallest live process picks `x₀` and passes `check`.
- Theorem 2.1 uses the standard round-robin adversary: it crashes a process exactly when the process
  is about to perform a new job. Such a job can never be performed by anyone else.

**Not formalized.** Section 5 (work `O(nm log n log m)` for `β ≥ 3m²`, Lemmas 5.1–5.5, Theorem 5.6),
Section 6 (`IterativeKK(ε)`, Lemmas 6.1–6.2, Theorems 6.3–6.4) and Section 7 (Write-All, Theorem 7.1). For `β = m` and
`f < m − 1` the exact value is not proved: the formula agreed in every case we could model-check (`m = 2`, `f = 0`,
`n ≤ 7`; `m = 3`, `n = 5` with `f ≤ 1` and `n = 6` with `f = 0`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: the effectiveness bounds are attained by explicit fair runs (the
adversary of Theorem 4.4 and the round-robin adversary of Theorem 2.1). The exhaustive model checker
used for small parameters (outside Lean) is [kk_modelcheck.py](kk_modelcheck.py).
