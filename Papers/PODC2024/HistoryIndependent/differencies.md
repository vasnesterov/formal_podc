# Differences between the formalization and the paper

Paper: H. Attiya, M. A. Bender, M. Farach-Colton, R. Oshman, N. Schiller, *History-Independent
Concurrent Objects*, PODC 2024 (arXiv 2403.14445v1, which contains the appendices).

## Model (Section 2) — `Cslib/Computability/Distributed/SharedMemory/`

1. **Executions are label lists.** Processes and objects are deterministic, so a finite execution is
   identified with its list of labels `inv p o` / `ret p r` / `tau p`; configurations are computed
   (`Impl.run`). Infinite executions are sequences of configurations and labels (`InfExec`).
2. **Returning is a separate step** (label `ret`, no memory access) instead of "the step that
   accesses the last object also returns". Harmless generalization; the history is the projection
   of the labels.
3. **Operation identities** are pairs `(p, k)` (`k`-th operation of `p`); linearizations are lists
   of such instances with their operations (`IsLinearization`): duplicate-free, contain all
   completed operations (pending ones optional = the paper's "completion"), respect real time,
   legal for the sequential specification. This is the paper's definition, made explicit.
4. **Access disciplines.** `Impl.allowed p o` restricts which operations a process may invoke
   (needed for single-writer single-reader registers, Cor. 18, Prop. 19, Alg. 2, Alg. 4). The paper
   leaves this implicit.
5. **Initial memory** is part of the implementation (`Impl.memInit`); the `init` field of the base
   objects' specifications is unused.
6. **Progress conditions.** Wait-free: in every infinite execution, a process whose operation stays
   pending forever takes only finitely many steps. Lock-free: every infinite execution with
   infinitely many (non-invocation) steps has infinitely many responses. Obstruction-free: from
   every reachable configuration, a pending process running solo returns. (Paper: informal
   one-line definitions.) `WaitFree → ObstructionFree` is proved.
7. **History independence (Def. 4)** is `Impl.HIwrt E`: there is a linearization function `h`
   (a linearization of *every* finite execution) such that executions in `E` with
   `state(h α) = state(h α')` have equal memory. Perfect / state-quiescent / quiescent HI as in
   Defs. 5, 7, 8. `E` may depend on the final configuration.
8. **Read-only / state-changing** operations as in the paper (`ReadOnly o := ∀ q, δ(q,o).1 = q`).
9. The paper's standing assumption "all states reachable from `q₀`" is not needed (for `C_t` every
   state is reachable in one `ochange`).

## Implicit assumptions made explicit

10. **Two processes (implicit scope assumption, not an error).** All impossibility results (Prop. 6/14, Thm. 17, Cor. 18, Thm. 20, Prop. 19)
    need at least two processes with suitable access rights (a reader allowed `oread`, a changer
    allowed the state-changing operations). With a single process they are false: the process can
    keep the abstract state in its local memory and leave the shared memory constant, which is
    trivially (perfectly) history independent and wait-free. The theorems take two distinct
    processes `c ≠ r` as hypotheses. Lean counterexample for one process: `prop14_needs_two_processes`
    (`OneProcess.lean`: a 3-valued register, no base objects at all, wait-free and perfect HI).
11. **Prop. 14's proof of "distinct canonical representations"** ("an `oread` that runs solo from
    the same memory representation must return the same response") needs the solo reader to be a
    process whose *local* state is the same in both executions — we use a second process `p'` that
    has taken no steps (`Agree`, `soloOp_eq_of_agree`). With the same process the claim is false in
    general (its local state may differ).

## Statements

12. **Prop. 6** (`prop6`): stated for a fixed linearization function `h` (`HIwrtWith`), for
    `q₁` reached by a sequence of operations of one process `p` and `q₂` reached from `q₁` by one more
    operation of `p`; "distance ≤ 1" is `MemDist1` (any two coordinates where the memories differ are
    equal), which avoids assuming finitely many base objects. Proof typo: "`α′` consists of a single
    operation … and `state(H(α)) = q₂`" should read `state(H(β)) = q₂`.
13. **Prop. 14** (`prop14`): holds for `t ≥ 2` (the paper says `t ≥ 3`; `t = 2` is trivial). The
    paper's proof says "Since `o_change` returns a different response…" — typo for `o_read`.
14. **Def. 13 (`ClassC`)**: the `ochange` operations are part of the data (a function
    `ochange q q'`), so that access disciplines (single writer) can be expressed; the partition is a
    surjection `cls : State → Fin t`.
15. **Theorem 17** (`thm17`) is derived from a general *avoidance lower bound*
    (`not_waitFree_stateQuiescentHI`, `Avoidance.lean`) that also yields Theorem 20. Instead of the
    partition `R₁,…,R_t` of all responses (Lemma 15, which needs footnote 4 "no unused values") we
    use one representative state per class and only track responses of representatives; this
    removes footnote 4.
16. **Lemma 16 gap: `q_k = q_{k+1}`.** The construction may choose `q^i_{k+1} = q^i_k`, for which
    `ochange(q, q)` is undefined (Def. 13 only provides `ochange(q,q')` for `q ≠ q'`). Fix: the changer
    performs no operation in that round (`AvoidData.move`). Morally trivial.
17. **Lemma 16: the reader's next step may be a return (artifact of the Lean model, not a paper
    error).** In the paper's model every step accesses an object; in ours returning is a separate
    step, so this case must be handled. In the formalization this case is the contradiction case (Lemma 15 applied
    to all `t` executions, `Good.ret_resp`).
18. **Theorem 17's proof** assumes "the local state of a process contains its complete history" to
    argue that the reader returns in all executions simultaneously. Not needed: in our model the
    return is determined by the reader's local state, which is the same in all executions. The proof
    also says "we must have `r ∉ X_i`" — typo for `r ∉ R_i`.
19. **Infinite execution.** The paper concludes from "arbitrarily long executions" that wait-freedom
    is violated; we build the limit infinite execution explicitly (`exists_infExec_of_chain`): the
    executions of index 0 form a prefix chain, the reader is pending forever and takes a step in
    every round.
20. **Obstruction-freedom of the changer.** The changer's operations are run solo to completion
    (`soloOps`); their existence uses `WaitFree.obstructionFree`.
21. **Theorem 20** (`thm20`) holds for every domain size `t ≥ 1` (paper: `t ≥ 2`). Responses are
    `Option (Fin t)`. Appendix C typos: Lemma 38 speaks of "`t` executions" for `i = 0,…,t` (should be
    `t+1`), and Theorem 20's proof cites Lemma 16 instead of Lemma 38. The queue is unbounded.
22. **Cor. 18** (`cor18`): stated for any implementation from binary registers in which a writer `w`
    may write and a different reader `r` may read (in particular SWSR).
23. **Prop. 19** (`prop19`): "the reader never writes" is formalized as `Impl.NeverWrites r`: every
    access by `r` (in a reachable configuration) leaves the accessed object's state unchanged. The
    access discipline is exactly SWSR (`allowed ↔ RWOp.SWSR w r`), so that a state-quiescent
    configuration has an idle writer; we also use that `write v` is state-changing (`t ≥ 2`).

## Algorithm 2 / Theorem 9 (`Alg2.lean`)

24. Values and array indices are 0-based (`Fin K`); the result holds for every `K ≥ 1` (for `K = 1` a
    write is read-only, so a write may be pending at a state-quiescent point; handled).
25. A failed `TryRead` restarts directly inside the step that reads `A[K-1] = 0` (no separate
    "return ⊥" step).
26. Linearizability goes through a general criterion for single-writer registers
    (`SWSRReadsFrom`: value, no read from the future, no overwritten value, no new–old inversion),
    which is exactly the paper's "reads-from" linearization; the read-before-read cases of App. A are
    recast as forward invariants of a ghost run (which write last wrote each cell). No gap found.
27. Lock-freedom is proved in the stronger form "every infinite execution has infinitely many
    responses".

## Algorithm 4 / Theorem 12 (`Alg4*.lean`)

28. 0-based values `Fin K`, any `K ≥ 1`. The reader's `val` is an `Option`; a Read returns
    `val.getD v₀`, and Lemma 10 shows `none` never occurs.
29. Line 14 reads `flag[2]` first and short-circuits; the scan of line 11 stops at the first 1;
    line 19 (`last-val ← v`) is merged into the return step. All equivalent to the paper's code.
30. Lemma 10 only needs a weak form of Lemma 34 ("some Write performs line 16 during the failed
    TryRead"); the "reaches line 18" part is not used. Lemmas 35/36 are proved as forward invariants;
    Lemma 11 via a ghost "last writer of `B[x]`". Reads that read `B` read from "the write before the one
    that wrote `B[j]`" (the paper's placement), fed to the SWSR reads-from criterion.
31. Typos: Theorem 12, case (2) says "Line 6" (should be Line 8); the HI proof writes "`A[v] = 0`" for
    `A[j] = 0` and repeats the `B` argument; Lemma 10's proof writes `W` for `W₂`.
32. Remark (checked by hand only, not in Lean): the order of the two flag reads in line 14
    (`flag[2]` before `flag[1]`) and the reader clearing `flag[1]` before `flag[2]` matter; with the
    opposite read order a quiescent configuration can keep `B ≠ 0`.

## Universal construction (Section 6, `Universal*.lean`)

33. Algorithm 5 is formalized over *atomic* R-LLSC base objects (`rllsc`, operations carry the
    process id). The blue right-hand sides of `∥` (lines 6R, 18R, 25R) are omitted: with atomic base
    objects the left side completes in one step, which is a legal schedule.
34. Line 12 applies the value loaded at line 11 (equal to `op` by the invariant). Read-only operations
    are linearized at their `Load`, not in invocation order within a segment (still a valid
    linearization). Responses, operations and `⊥` are kept apart by sum/option types instead of the
    assumption `R ∩ O = ∅`, `⊥ ∉ R ∪ O`. `A` needs a decidable read-only predicate.
35. One inductive invariant (`inv_run`) replaces Invariants 21–22 and Lemmas 23, 24, 26, 39.
36. Algorithm 6: the CAS cell holds `(v, Finset P)`; Lemma 29 counts linearized (not returned)
    context-changing operations; Lemma 30 is proved under the extra hypothesis that the process is
    not in the context; lock-freedom needs finitely many processes.
37. **Paper issues found:** (a) lines 6R.1/18R.1 read "wait until `Load(announce[i]) ∉ R`" — must be
    `∈ R` to match the proofs of Invariant 21 and Claim 33 (typo). (b) *Unclear / immaterial:* in the proof of Theorem 32, "after at most `n` mode transitions
    `priority_j = π(op)`" — the subagent counted `n + 1` (a priority value read before the announcement),
    an independent reviewer counts `n` (`1 + (n−1)`); we did not settle this precisely, and it does not
    affect the result (our proof uses its own potential). (c) **Gap in Theorem 32:** abandoned `LL`s (lines 6R/18R/25R jump
    away while the left-side `LL` is still pending) make the per-object histories seen by the R-LLSC
    implementation non-well-formed (a process has two pending operations on the same object), so
    Theorem 28 (linearizability of Alg. 6 for well-formed histories) is applied outside its hypothesis;
    a rigor gap, easily patched by a white-box argument (an abandoned `LL` never takes effect). (d) Lemma 41 only discusses the `RL` of line 22; the `RL` of
    line 18R.2 can run while the process is still in `announce[j]`'s context from an earlier iteration
    (reachable), and needs the same argument.
38. **Theorem 32 — weaker than the paper's statement.** `theorem32` is proved for **one deterministic
    resolution of each `∥` (strict alternation)** and for the **flattened** algorithm — *not* for every
    interleaving of `∥`, and *not* compositionally (Lemma 25 + Theorem 28 + Lemma 27). It captures the
    existence claim (a wait-free state-quiescent HI universal implementation from CAS exists).
    Linearizability and HI are plausibly interleaving-independent (an abandoned Alg. 6 `LL` never takes
    effect), so the restriction matters essentially for wait-freedom. Details: it is proved for the
    *flattened* implementation `flat A n`: Algorithm 5
    with every R-LLSC operation inlined as the Algorithm 6 code over `n + 1` CAS objects, and each `∥`
    resolved by one admissible schedule (strict alternation starting left; once the wait condition
    holds, the right side runs to completion). This proves the existence claim; it is not a
    compositional (black-box) proof. Wait-freedom uses an explicit potential instead of Lemmas 29–31,
    41 and Claim 33. An auxiliary pc `rl18` (line 18R.2) was added to the atomic version
    (unreachable there). The SC/RL guard of Alg. 6 is re-checked before the CAS (equivalent).

## Not in the paper

39. `alg2_not_waitFree`: Theorem 9 + Corollary 18 ⇒ Algorithm 2 is not wait-free for `K ≥ 3`.
40. `alg4_reader_writes`: Theorem 12 + Prop. 19 ⇒ the reader of Algorithm 4 must write.
41. Tightness / non-vacuity: `register_tight` (a `t`-valued register has a wait-free perfect HI
    implementation from one base object with `t` states — the trivial atomic implementation,
    `Cslib/Computability/Distributed/SharedMemory/Atomic.lean`); `prop14_needs_two_processes` (item 10).
