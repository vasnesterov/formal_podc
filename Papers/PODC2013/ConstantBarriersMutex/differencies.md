# Differences between the formalization and the paper

Paper: Attiya, Hendler, Levy, *An O(1)-Barriers Optimal RMRs Mutual Exclusion Algorithm*, PODC 2013
(extended abstract, 11 pp., author copy). Section numbers and statement numbers refer to it.

## Statement-level issues (verdict rules)

1. **Lemma 2(c) is false, also under sequential consistency** (`lemma2c_false_sc`). With 2 processes, a
   process signalled in its current passage reaches `pc = 48` after `lock ← next`; `signal[r]` is
   true but `r` does not own the lock. Rule R3 does not excuse it. The fix `< 48` is an index change,
   but the paper's proof reasons with the wrong range: case 4 claims statement 47 cannot violate (c),
   and case 5 applies (c) to the exiting process at `pc = 48`. Label ❌ (non-headline numbered
   lemma). *Borderline*: the intended content (the signalled process waiting in the entry section
   owns the lock) is recoverable and is what the later proofs use (Lemma 6).
2. **Lemma 2(c) under TSO** (`lemma2c_false`): a stale `signal[r] = true` remains in memory while
   `r`'s reset (statement 17) is buffered. Same label; our corrected version restricts to statements
   23–27 (after the barrier).
3. **Lemma 2(b) under TSO** (`lemma2b_false`): at `pc = 48` the write `lock ← next` may still be
   buffered. Rule R4 does not excuse it: the paper's model is TSO (Section 3), and `C.lock` is the
   memory value. Under SC (b) holds. Label ❌ (same lemma).
4. Verdict: worst label ❌ (R6). Headline (Theorem 1, the algorithm's properties) is true (R5: no 🚨).

## Proof gaps (statements true)

5. **Safety under TSO.** The proof of Lemma 2 treats issued writes as performed. Replaced by the
   inductive invariant `Inv` (`InvDefs.lean`). It records buffer contents per program counter; lock
   ownership (`Holds`, `Hands`); the logical memory `lv` (the lock owner's view) for `promQ`,
   `inPromQ`, `exits`; a TSO version of (c) (`sig`); and `exits` against a ghost counter of CS
   entries (`ex1`–`ex4`).
6. **Lemma 7 / Claim 2, base case.** The paper does not use the `exits − e ≥ 2` disjunct of statement
   25 explicitly and does not treat a process stuck at statement 25. Repaired by `Run.waiting_entry`.
7. **Claim 2, inductive step.** "Let `t′` be the point when `n^k_p` is last written in `EE1`" and "by
   total store ordering, `t ≤ t1 ≤ t2`" are made precise via the number `perf` of performed
   doorway writes (`Doorway.lean`). We use the minimal level among starved processes instead of
   induction on the level (equivalent). The stabilization time of Claim 1 is the maximum over the
   finite set of starved processes.
8. **Lemma 9.** The case `r = q′` is missing; case 1 implicitly needs `r` to have remained in its
   entry section since its node write. Both are handled in `BoundedWaitingCore.lean`. Our Lemma 9
   statement is the TSO version: "`p` has been promoted in `[t₁, e]` (it is in the promotion order
   `BW.Q`: the handed process followed by the logical queue), or some exit section reads `anc p l`
   at statement 34 before `q`'s `(l+2)`-th entry, after a time at which `anc p l` holds `p` from `p`'s
   current doorway". The paper's `s(P)` (enqueue time) is replaced by membership in `BW.Q`.
9. **Lemma 8** holds with `log n + 2` (`lemma8`). The paper's `log n + 3` is a corollary.
10. **Lemma 10.** The proof's "at most 4 RMRs at statement 25" is wrong: 6, attained by
    `stmt25_tight`. Its "a single RMR at statement 27" is wrong: 2, attained by `stmt27_two`, because
    the first read counts. Our total bound is `19·log n + 23` per passage (explicit constant).
11. **Footnote 4** (reads never hit the own store buffer) is false: statements 36, 37, 42, 45
    read `inPromQ`/`promQ` entries written earlier in the same exit section with no barrier in
    between. (Statement 32 is not an instance: `exits` is written only there, and the previous
    write is followed by the barrier of statement 50.) Not used
    anywhere.

## Modelling choices

12. `n = 2^h` processes `Fin (2^h)`; `log n = h`. The tree is in heap numbering (root 1, children `2v`,
    `2v+1`, leaf of `p` is `2^h + p`). The paper's tree has `n` leaves; other `n` can be padded with
    idle processes.
13. Node values `Option (Fin (2^h))` (`none` = −1); `lock : Option`; `exits : ℕ` (unbounded, as in
    Algorithm 1; Observation 1 not formalized).
14. **TSO semantics** (Section 3):
    - `flush p` events perform the oldest buffered write at any time (adversary).
    - A barrier step with a nonempty buffer performs one write; otherwise it proceeds.
    - A CAS performs the whole buffer first. The paper says "the adversary performs all these writes
      (and those preceding them)" only for writes to the CAS variable. At statements 23 and 26 the
      buffer is empty anyway (`LI`), so this makes no difference.
    - Reads take the newest own buffered write, else memory.
15. **Granularity:**
    - One shared access per step.
    - Statement 25 is two steps (read `exits`, then read `lock`).
    - `exits ← exits + 1`, `promQ.enqueue`, `promQ.dequeue` read (own view) and issue the write in one
      step. They are executed only by the lock owner (`corollary4`), and their writes are buffered as
      usual.
    - `promQ` is a single shared variable holding a list (the paper does not fix its
      implementation).
16. Statement 35's set `{q1,q2,q3} \ {−1,p}` is processed in order of first appearance among
    `q1, q2, q3`, without duplicates (the paper leaves the order open). No proof depends on the order.
17. The critical section is one local step. A step in the remainder section starts a passage
    (issues statement 17). Processes may stay in the remainder section forever.
18. **Fairness** (`Run.Fair`): a process outside the remainder section eventually takes a step. No
    fairness for flushes is needed (barriers drain buffers). Safety, bounded waiting and RMR bounds
    hold for every schedule.
19. **Definition 1.** The exit section ends when the write of statement 43/48 is performed:
    `Cfg.InCSX` counts a process at statement 50 with a nonempty buffer. "Waiting section" =
    statements 24–27 (`PC.Waiting`), i.e. after the CAS of statement 23 was performed. The doorway
    ends there, as in the paper.
20. **Bounded waiting** is counted as: while `p` is in its waiting section at all times in
    `[t₁, t₂]`, the number of steps `t ∈ [t₁, t₂)` at which `q ≠ p` enters the CS.
21. **RMR model** (`RMR.lean`):
    - Every issued write and every CAS costs 1 RMR.
    - A read served by the own buffer costs 0.
    - A read from memory costs 1 iff it is the first read or another process *performed* a
      write to the variable since the reader's last read (any write, as in the paper).
    - A failed CAS is not a write.
    - "Passage" = interval in which the process is not in the remainder section
      (`Run.WithinPassage`, `Run.Passage`).
22. **Starvation freedom** is stated as: in a fair run, a process in its entry section at `T` is in
    the CS at some `t ≥ T`.
23. Lemma 6 is generalised: any process to which the lock was handed (`lock = p` in memory, `p` in
    entry) enters the CS. Lemma 5(b) is stated for `p ∈ lv.promQ`.

## Not formalized

24. Section 6: Lemma 11 (writes performed by the comparison-object simulation of Golab et al.) and
    Theorem 12 (read/write version). They depend on a large external construction whose full proof
    is "in the full paper".
25. Observation 1 (bounded `exits` modulo `(n−1)(log n+2)+1`).
26. The appendix (experiments) and the remark that with PSO deadlock-freedom fails (no claim proved
    in the paper).
