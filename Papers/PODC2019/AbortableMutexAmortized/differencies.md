# Differences between the formalization and the paper

Paper: P. Jayanti, S. Jayanti, *Constant Amortized RMR Abortable Mutex for CC and DSM*, PODC 2019;
formalized from the full version arXiv 1809.04561v1 (numbering as there).

## Model

- **Processes.** A fixed finite set `Fin n`. The paper allows an unbounded number of processes
  with arbitrary names that "join" over time; a process that has not joined yet is modelled as a
  process that stays in the Remainder section (line 1). Every result is stated for every `n`.
- **Granularity.** One step = one shared-memory operation (the numbered line) plus all local
  actions that follow it, exactly the paper's convention (Section 3.2). Line 1 = Remainder,
  line 7 = CS (the paper's convention in `I10` / Corollary 4.1.1; this also covers the "sidestep"
  of an aborting process that reads `token` at line 9 and goes to line 7 without using the CS).
- **Abort signal.** A step carries a Boolean abort flag. It only matters at lines 4, 5, 6; there an
  aborting step jumps to the Abort section *and performs line 9 in the same step* (the jump is a
  local action, merged into the next shared operation). Elsewhere the flag is ignored (the paper:
  the jump is allowed "only after performing Line 3, 4, 5 or 6"; a signal arriving at line 2/3
  takes effect after line 3). *Remark:* if the jump were a separate, memory-free step (so that a
  process can sit at line 6 and then jump to line 9), Lemma 4.4 would fail with the paper's `f`
  (`f(6) = 2 < f(9) = 6`): our exhaustive model checker finds 540 violating transitions for `n = 2`.
  This separate-step reading is *not* the paper's model: the paper says a step performs one
  shared-memory operation "but can perform any number of local actions", the jump (a `goto`) is a
  local action, and the paper requires the process "to execute Line 3 and all local actions
  associated with Line 3 before jumping". So the jump belongs to a shared-memory step, and the
  540 violations are not an error of the paper. Merging the jump with either the preceding or the
  following shared operation is consistent with the paper's convention. We merge it with the
  following one. The review re-checked the preceding-merge variant (a step performing line 3, 4, 5
  or 6 that leaves the process in the loop may end at line 9) for `n = 2`: 14 593 reachable
  configurations, the strengthened invariant holds, and Lemma 4.4 has 0 violations. The two models
  differ only in the local `PC` between the two steps.
- **Impossible values.** Where the invariant shows a case cannot happen (`*v ← true` with `v` not
  a go-address; `v_p = &go_q`, `q ≠ p`, read at lines 3/6/9) the model does something harmless
  (no-op / no `pred` update). The invariant (`Loc`) proves these cases unreachable.
- **`v_p` initial value.** "Arbitrarily initialized": we use `nil`; `v_p` is never read before it
  is written.
- **Executions.** `exec σ` for an arbitrary schedule `σ : ℕ → Fin n × Bool` (every schedule is
  admissible, `step` is total and deterministic); finite runs `run init ls`.
- **Fairness (Theorem 4.5).** `Fair σ`: every process outside the Remainder section eventually
  takes a step. This is the paper's "no process stays in the CS forever and no process stops
  taking steps while in the Try, Exit or Abort sections". A process at line 4 with `go = false`
  takes no-op steps (busy waiting).
- **RMR cost models.** DSM: an arbitrary placement `home` of the shared variables with `go_p` in
  `p`'s partition (the paper fixes only this); an access costs 1 iff the variable is not in the
  accessing process's partition. CC: per-process caches; a read is free iff the variable is cached
  (and then caches it); every non-read operation costs 1 and invalidates all copies (Section 1).
  CC caches start empty; the paper instead "thinks of `go_p` as initially in `p`'s cache, at the
  cost of charging one unit to a joining process".

## Statements

- **Theorem 4.1 (invariant).** Stated verbatim as `PaperInv` (Figure 1) and proved for every
  reachable configuration (`theorem_4_1`), uniqueness of `k, A, Q` from `I1`–`I4`
  (`theorem_4_1_unique`, `unique_of_I1_I4`). Lists are 0-based (`a_i = A[i]`, `q_{i+1} = Q[i]`).
  Typos fixed: in `I7` "`*mynode_p`" is `*mynode_{q_i}`; in `I9` "`go_{q₁}`" is `&go_{q₁}`.
  `I4` ("`N = {a₀} ∪ {mynode_p}`") is read as: every node is `a₀` or some `mynode_p` (with
  `|N| = n + 1` this forces `mynode` injective and `a₀` nobody's node, `cover_inj`).
- **Proof gap in Theorem 4.1 (🛠️).** `I` is *not inductive*: `paperInv_not_inductive` gives a
  configuration satisfying `I` whose successor (line 3, case 3: splicing an aborted predecessor)
  satisfies no instance of `I` (`I7` fails for the new predecessor, whose node still holds the
  spliced process's go-address). The appendix's "the rest of the invariants continue to hold
  since they are unaffected" misses this. Repair: the extra conjunct `Loc.x1` ("an aborted queue
  member at line 1, 10 or 11 does not have its own go-address in its predecessor node"); with it
  the invariant is inductive (`inv_step`). Since `I` itself holds in all reachable configurations,
  the statement of Theorem 4.1 is true (rule R1: a proof gap → 🛠️).
- **Corollary 4.1.1** (`mutual_exclusion`): as stated.
- **Theorem 4.2 (AFCFS) — false as stated (⚠️, borderline ❌).** `afcfs_literal_false`: a run in which
  `p` completes the doorway of its only attempt, aborts it (lines 9, 10) and never returns; `p'`
  begins its first passage afterwards, splices out `p`'s node and enters the CS. `p`'s passage
  (one aborted attempt, the last one: `j = k` in the passage definition) A-precedes `p'`'s, and `p'`
  enters the CS although `p` never does. The definition cannot be met by *any* starvation-free
  abortable lock (a process that leaves after its doorway would block all later processes
  forever). Corrected statement proved (`theorem_4_2`): `p'` does not enter the CS before `p`
  enters the CS **or the Abort section**. The definition of "attempt", "passage", "begins"
  is encoded semantically (`PassageStart`: `p'` in the Remainder, and its last step, if any, was
  an Exit step at line 7 or 8); the doorway completion is "`p` at line 3". Classification: the
  missing case ("unless `p`'s passage ends with an abort") is evident from the airline analogy
  (people behind you may take your spot when you leave) and the proof (which only uses that `p`
  stays ahead in `Q` while it is there); the fix is local, so R3 → ⚠️. Borderline because AFCFS
  is the paper's own new definition and is listed in the abstract; we judged it a definitional
  slip, not a false claim about the algorithm. The counterexample needs the strict reading of
  "`p'` does not enter the CS before `p` enters the CS" (`p'` must wait for an entry of `p` that never
  happens). Under the weaker reading "if both enter, `p` enters first", the literal definition is
  already the corrected one and Theorem 4.2 holds as stated. This ambiguity is a further reason
  against ❌. On the sidestep (line 9 reads `token`, then line 7): `theorem_4_2` counts line 9 as
  "entering the Abort section". For a successful last attempt that sidesteps, it therefore only
  gives "`p` reached line 9 by the time `p'` is at line 7", not "`p` reached line 7 first". This is
  harmless because the sidestep is a degenerate CS entry by the paper's own convention (`I10`).
- **Definition 4.1 / Lemma 4.4 — `f` undefined at line 11 (⚠️).** `f` in eq. (1) has no value for
  `PC = 11`, but `q_m` can be at line 11 (aborted, node marked, about to wake its successor), and
  the proof of Lemma 4.4 itself lists `11` among the cases. We set `f(11) = 4`, the only value
  between `f(10) = 5` and `f(1) = 3` (R3: missing case with evident fix).
- **Lemma 4.3** (`lemma_4_3`): as stated (for `p` in the Try section or CS; `p ∈ Q` follows from
  the invariant).
- **Lemma 4.4** (`lemma_4_4_part1`, `lemma_4_4_part2`): we exclude an *aborting step of `p`
  itself*, after which `p` is no longer in the Try section and `δ(p)` is undefined (the paper's
  statement silently assumes this). We also prove that `Ψ(p)` is nonempty and consists of processes
  outside the Remainder (`promoters_spec`), which Theorem 4.5's proof uses without proof
  (it needs `I11`: if `q_m` waits at line 4 with `go = false` then `m = 1`).
- **Theorem 4.5** (`theorem_4_5`): as stated, for fair schedules in which `p` never aborts; we also
  allow `p` at line 2. The hypothesis forbids aborting steps of `p` at *all* times, including later
  attempts. This is harmless: the conclusion depends only on the prefix up to `p`'s CS entry, and the
  schedule can be changed after it.
- **Proof remark (Appendix B).** "The `m`-th digit decreases" / "one fewer digit" needs the leading
  digit to be nonzero (`f ≥ 1` on queue members, which needs `I6`/`I8`: no queue member is at line 2
  or 8). Made explicit in `StarvationDefs.lean`.

- **Theorem 5.1** (`theorem_5_1`): "space `O(n)`" is formalized as the number of shared variables,
  `|Var n| = 2n + 2` (`tail`, `n + 1` nodes, `n` go-flags); each holds one word.
- **Lemma 5.2** (`lemma_5_2`): exactly the paper's constants (1 for lines 1, 2, 3, 7, 9; 2 for
  8, 10, 11; 0 for 4, 5, 6), for every placement of nodes/`tail`, `go_p` local to `p`, and every
  configuration satisfying the invariant.
- **Lemma 5.3 — proof slip (🛠️-level, statement true).** The statement only claims "a constant";
  the proof claims `α_CC(8), α_CC(11) ≤ 4`, but the write `*v ← true` also invalidates `go_q` in
  `q`'s cache, raising `1{notcached(q)}` too: the true bound is 5 (`lemma_5_3`, `boundC`; our
  exhaustive check for `n = 2` attains 5). Also the proof's "`α_CC(3), α_CC(7), α_CC(11) ≤ 1`"
  should read `α_CC(9)`. Neither affects Lemma 5.3 or Theorem 5.4.
- **Theorem 5.4.** Amortized: `theorem_5_4_dsm` (≤ 8 RMRs per attempt) and `theorem_5_4_cc`
  (≤ 12 per attempt), for every finite execution from the initial configuration, where an attempt
  is a step at line 1 (the paper's ratio `x/y`; infinite runs: every prefix). The paper's proof
  ("lines outside the loop are executed at most once per attempt") is made precise by a
  remaining-budget potential `Σ_p c(pc_p)`. CC with empty initial caches: the potential term
  `1{notcached(p)}` is replaced by `1{notcached(p) ∧ pc_p ≠ 1}`, which charges the missing unit to
  line 1 (the paper's "charging one unit to a process newly joining"); this costs nothing in the
  bound's form. Worst-case Exit: `theorem_5_4_exit` (2 own steps from line 7) and every step costs
  ≤ 1 RMR (`dsmCost_le_one`, `ccCost_le_one`). Fast Abort: `theorem_5_4_fastAbort` — from any
  configuration, a process taking only aborting steps returns to the Remainder within 5 own steps.
  The paper's "within six shared instructions" is a correct but weaker bound: it counts line 1,
  which is the Remainder section. This is not an error.
