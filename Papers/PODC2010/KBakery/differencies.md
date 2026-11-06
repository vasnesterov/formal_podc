# Differences between the formalization and the paper

Danek, *The k-Bakery*, PODC 2010 (author copy, 9 pp.), with proofs from Danek's PhD thesis (Toronto 2010,
Chapter 5) where the paper omits them.

## Main finding

- **❌ Theorem 10.** It claims that the algorithm of Figure 3 satisfies k-exclusion with non-atomic
  (safe) reads and writes. It does not (`NonAtomic.counterexample`, `N = 3`, `k = 1`). The title
  ("… Using Non-atomic Reads and Writes") and the abstract ("Finally, we present a modification … that
  works with non-atomic reads and writes") present it as a primary contribution, and the claim is about
  the paper's specific algorithm.
- Not an implied assumption: the paper explicitly fixes the semantics of non-atomic accesses ("behave the same as
  … single-writer … safe registers"; "if a non-atomic read and write access the same variable
  concurrently, then the read returns an arbitrary value") for all variables, and Figure 3 keeps `Ticket`
  a single, non-duplicated register. Making `Ticket` atomic/regular is a change of the model, not an
  implied assumption.
- Not a degenerate case: `k = 1` is ordinary mutual exclusion, `N = 3` processes, no crashes. The paper
  allows `k = 1` explicitly (k-FCFS "makes sense for all `k ≥ 1`"; Section 6 itself uses `k = 1` for its
  scenario against Figure 2).
- The introduction calls the *atomic* algorithms "our main contribution" and the abstract introduces the
  non-atomic variant with "Finally", but the title is "The k-Bakery: … Using Non-atomic Reads and Writes".
  The claim (Theorem 10, Table 1) is about the paper's specific algorithm, Figure 3, with `Θ(N)` RMRs, and
  no repaired local-spin non-atomic algorithm is known or verified here.
- Theorems 8 and 9 (and Lemmas 1–7) are true as stated: proved.

## Modelling choices (Figure 2, atomic registers)

1. **Processes.** A finite type `P` with a linear order (`N = |P|`); the paper's ids `1..N` and the
   tie-break `(Ticket[p], p) < (Want[i][p], i)` use this order.
2. **One algorithm, two variants.** `fife = false` removes lines 17, 22, 23 (the unshaded algorithm,
   Theorem 8); `fife = true` is the full algorithm (Theorem 9). With `fife = false`, `captured` stays
   `false`, exactly as in the unshaded code.
3. **Granularity.** Each step performs at most one shared access followed by local computation. Lines
   17–18 (local) are merged into the last step of line 16; a `foreach` with nothing left to visit takes
   one local step. Line 15 is `N` read steps (including the own `Ticket[p]`) and one write step.
4. **Own ticket.** At lines 14, 16, 21, 22, 23 the process uses `Ticket[p]` in the same step as the
   accompanying access (only `p` writes `Ticket[p]`, so the value is the same). Consequence for RMR
   counting: re-reads of `Ticket[p]` are not counted. In DSM they are local anyway. In CC they cost at
   most one RMR per passage (thesis, proof of Lemma 5.8), which the stated CC bounds do not include.
5. **`foreach` order.** Arbitrary: the adversary chooses the next index at every step (`Admissible`).
   This is more general than any fixed order.
6. **Executions.** Infinite schedules `Run` (process + `foreach` choice at each time). Every process has
   an enabled step in every configuration, so every finite execution is a prefix of a `Run`; safety is
   also proved for all `Reachable` configurations.
7. **Crashes and finite CS.** `Run.Crashed q` iff `q` takes finitely many steps and stays outside the NCS
   from some time on (the paper: "stops taking steps while outside the NCS"). A process in the NCS that is
   never scheduled again is not faulty. The CS is one location left at the next step of the process, so
   "the CS is finite" holds for non-faulty processes. No other fairness assumption.
8. **Bounded exit** is not stated separately; the exit protocol is `N` write steps plus one local step.

## Statements

9. **k-exclusion** (Lemma 4, thesis Lemma 5.15) is proved in a stronger form: at most `k` processes are
   at line 23 or in the CS (`card_qual_le_of_inv`); `k_exclusion` is the CS version for reachable
   configurations, `Run.k_exclusion` for executions.
10. **Starvation freedom** (Lemma 5): "at most `k − 1` processes crash" is written
    `(univ.filter Crashed).card < k`. For `k = 0` the hypothesis is unsatisfiable, matching the paper's
    implicit `k ≥ 1`. Conclusion: every non-crashed process that is in the trying protocol (lines 14–23)
    at time `t₀` is in the CS at some time `≥ t₀`.
11. **k-FCFS** (Lemma 6): "all processes in `Y` finish the doorway before `p` starts the doorway"
    becomes: at time `t₀`, `p` is in the NCS and every `q ∈ Y` is in its waiting room (lines 16–23).
    Processes of `Y` already past the CS at `t₀` satisfy the conclusion trivially and are left out.
    "`p` does not enter the CS before some `q ∈ Y` does" becomes: if `p` is in the CS at `t₁ ≥ t₀`,
    some `q ∈ Y` is in the CS at a time in `[t₀, t₁]`. Proved for both variants (the thesis' Theorem
    5.20 also claims k-FCFS for the FIFE algorithm).
12. **FIFE** (thesis Lemma 5.16): "p finishes the doorway before q starts the doorway, and q enters the
    CS before p" becomes: at `t₀` `p` is in its waiting room and `q` in the NCS, `q` is in the CS at
    `t₁ ≥ t₀`, and `p` is not in the CS during `[t₀, t₁]`. "Bounded number of its own steps" is made
    explicit: after `4N + 7` steps of `p` from `t₁` on, `p` has been in the CS.
13. **RMR complexity** (Lemma 7). A passage starts with the step leaving the NCS (time `t₀`) and lasts
    while `p` is not back in the NCS. `Θ(N)` is proved as follows. DSM: every prefix of a passage makes
    at most, and every complete passage exactly, `4(N − 1)` (unshaded) / `5(N − 1)` (full) RMRs. CC:
    every prefix makes at most `9N − 6` / `13N − 6` RMRs, every complete passage at least `3N − 1`.
    The CC model is write-through/write-invalidate; a write leaves the writer's own cached copy as it
    is. The paper's remark that the results also hold for write-back caches is not formalized.
14. **Lemmas 1–3 and thesis Lemmas 5.13–5.14** are not stated as such; their role is played by the
    invariant `Inv` (`s1`: removed processes are `Safe`; `s3`, `s5`: capture witnesses have fewer than
    `k` unsafe processes; `s4`: qualified processes have fewer than `k` unsafe processes). Lemma 1 is
    used inline in `k_fcfs` (`FcfsQ`) and `fife` (`FifeQ`).

## Proofs

15. All proofs are new (invariants and measures instead of the precedence relations `→`, `⇢` on
    operation intervals). The paper's proof sketches are correct up to routine details:
    - Lemma 5: the sketch ("eventually the only processes in `p`'s predecessor set are crashed")
      does not treat non-stuck processes that keep re-entering. We use a measure argument: after `m`'s
      ticket is fixed, every such process passes through a fresh doorway whose ticket exceeds `m`'s
      (`reach_good`).
    - Lemma 7 (CC) and Theorem 9 have no proof in the paper ("omitted due to space limitations"). The
      thesis' proofs are correct; ours are an amortized potential (`Bw ≤ 4`, `Bc ≤ 2`, matching the
      thesis' 5 and 3 RMRs) and the invariant above.

## Figure 3 (non-atomic), Theorem 10

16. **Model** (`NonAtomic.lean`, separate from Figure 2's model). All registers hold values in
    `ℕ ∪ {∞}`. A write is two steps of the writer (begin: busy; end: value stored). A read is one step
    and returns the stored value if the register is not busy, otherwise an adversary-supplied value.
    This is a sub-model of the interval semantics of safe registers (zero-length reads), so every
    execution exhibited is legal in the paper's model.
17. Reads of the process's own `Ticket[p]` and `Capture[p][i][1]` take no step (it is their only
    writer and never reads them during its own write). `foreach` loops follow a fixed list `ord` of all
    processes (`[0, 1, 2]` in the counterexample), one of the orders the paper allows. Crashes and
    liveness are not modelled (not needed for a safety counterexample).
18. **Result.** `counterexample`: `N = 3`, `k = 1`, a legal 246-step execution ending with processes
    `0` and `1` in the CS. Hence k-exclusion fails, and the rest of Theorem 10 (starvation freedom,
    FIFE, `Θ(N)` RMRs) was not examined.
19. **Thesis.** The thesis' Lemma 5.21 (`Cp → Cq ⇒ tp < tq`) is false for Figure 5.6. In the
    counterexample `C_r → C_p` but `t_p = 3 < t_r = 101`. Lemma 5.25 (the non-atomic analogue of
    Lemma 5.14) and Theorem 5.33 are false as well. These are not statements of the PODC paper.

## Not formalized

20. Section 5's claim that the unshaded algorithm violates FIFE (the `k = 2`, four-process scenario),
    Section 6's claim that Figure 2 fails with non-atomic registers, Table 1 and Section 2 (related
    work), the conclusion's remarks on ticket resetting. A repaired Figure 3 (atomic or regular `Ticket`)
    is not verified.
