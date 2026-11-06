# Differences between the formalization and the paper

Paper: W. Golab, *A complexity separation between the cache-coherent and distributed shared memory
models*, PODC 2011 (arXiv:1109.5153v1).

## Statement-level issues in the paper

1. **Corollary 6.14 omits "terminating" (✏️, false as stated).** The statement says "for any
   deterministic algorithm". The proof begins "some deterministic terminating algorithm". Without
   termination there is a counterexample. `spinAlg`: `Poll()` reads the caller's own variable
   forever; `Signal()` returns at once. Specification 4.1 constrains only completed polls, so
   `spinAlg` solves the problem, and `rmr τ = 0` for every execution
   (`corollary_6_14_needs_terminating`, `NonTerminating.lean`). It uses only reads, so it is an
   algorithm "using atomic reads and writes, and either CAS or LL/SC" in the literal sense. The
   intended statement is recoverable from the proof and the fix is local (one word). The same
   counterexample shows that the `Terminating`/`SoloTerminating` hypothesis of our
   `theorem_6_2` cannot be dropped.
2. **Theorem 6.2: "N large enough" and the meaning of "constant" are implicit (not counted as a
   mistake).** Read literally (algorithm `A` for a fixed `N`, then "for any constant `c`"), the
   theorem is false for fixed `N`. A signaler that writes `true` to every process' own flag makes at
   most `N − 1` RMRs per history, so `c = N` is a counterexample. This example is not formalized.
   The proof explicitly assumes "`N` large enough", and "constant" conventionally means independent
   of `N`. We formalize `∀ c, ∃ N₀, ∀ N ≥ N₀, ∀ A, …`. The theorem also asks for a constant `k` (🔧). In
   the branch through Lemma 6.11, the paper's contradiction history has
   `k = c + ⌊N^{1/3^c}/2⌋`, which is not constant. Our version gives `k ≤ c² + c + 1` in all
   branches: in Lemma 6.11 we keep only `c² + 1` unstable processes, and
   `(c²+1)(c+1) > c(c + c² + 1)`.

## Proof gaps (repaired; the statements we need are proved)

3. **Regularity condition 3 (Definition 6.6) is not maintained by the construction of Lemma 6.10 (🛠️).**
   In the erasing case only conflicts with variables previously written by *active* processes are
   removed. A kept unstable process may write a variable previously written by a *finished* process
   (for example a shared variable written by a rolled-forward process). Then the variable has two
   writers and the last one is active, which violates condition 3. Erasing finished processes is
   impossible, and there may be many such writers. Moreover, under condition 3 a variable whose last
   writer is finished may have many active earlier writers (the left-over writers of a roll-forward
   round). A new write to it then conflicts with all of them, so "for each process we add at most
   one edge" (average degree ≤ 2) fails.
   *Repair:* condition 3 is replaced by `SoleW`: if the last writer of `v` is active, then after
   erasing it the last writer of `v` is not active (`Regular.lean`). Every step preserves it:
   `SoleW.snoc_write`, `Regular.erase`, the roll-forward (`roll_forward`), and the special handling of
   the roll-forward variable in `round_rollforward`. Write conflicts then have out-degree ≤ 1. It is
   exactly what the rest of the proof needs: after erasing any set of active processes, every
   variable holds a value written by a finished process, by the reader itself, or its initial value
   (`SoleW.erase_writer_not_mem`, `SoleW.writer_of_erase`).
   Consequently Lemma 6.10 *as stated* (`S(i)` with regularity in the sense of Definition 6.6) is
   neither proved nor refuted; we prove the variant with `SoleW` (and the constants of item 8).
   Since Lemma 6.10 is not refuted, this is a proof-level issue, not a false statement.
4. **Lemma 6.13: termination is applied to unfair histories (🔧).** The stable processes "complete any
   pending call", and `s`'s `Signal()` "must eventually terminate". In the histories considered,
   the other active processes are stopped in mid-call, so the history is not fair and termination
   says nothing. *Repair:* `s` runs `Signal()` solo after *all* stable processes are erased; there
   every other participant has terminated. For each stable `p` we compare with the history in which
   only `p` is kept. If `s` accesses neither `p`'s module nor a variable last written by `p`, its
   run is the same. Then `p`, running solo (where again everybody else has terminated), completes
   its pending call and one more `Poll()`. That poll returns `false` by Specification 4.1 applied to
   the same run without `s`, which contains no signal. But it began after `s`'s `Signal()`
   completed: contradiction (`final_stable`). The paper's step "first complete the pending polls"
   is not needed.
5. **Lemma 6.13: one RMR per stable process needs disjointness (🔧).** "`s` performs one such RMR for
   each stable process" requires the sets `D(p) =` "variables in `p`'s module or last written by
   `p`" to be pairwise disjoint over the stable processes and remote for `s`. Disjointness follows
   from regularity conditions 2 and 3; the paper does not say so. We prove it and count with
   `card_le_rmr_of_injOn`.
6. **Lemma 6.13: choice of `s` (🔧).** "Some process `s` whose memory module is not written in `H`" does
   not exclude `s ∈ Par(H)`. A finished `s` cannot call `Signal()`, and an active one is not solo.
   We choose `s` outside `Par(H)` and outside the modules written remotely by the stable
   processes. This needs `N > c + 2M + M·c(c+1)` with `M = c(c+1) + 1`.
7. **Lemma 6.10: roll-forward needs termination in a fair history too (🔧).** The rolled-forward
   process `r` completes its `Poll()`. We run it solo in the history where all other active
   processes are erased, so that every other participant has terminated. We erase exactly the
   active processes whose module or last writes `r` accesses, and replay (`roll_forward`). Each
   erased process costs `r` a distinct RMR (same disjointness as item 5), so at most `c(i+1) ≤ c²`
   processes are erased. The paper's per-step erasure argument amounts to the same thing.

## Changed constants and structure (no effect on the results)

8. **Shrinking of the active set.** The paper's invariant is `|Act(H_i)| ≥ N^{1/3^i}`. We use
   `|Act(H_{i+1})| ≥ keep c |Act(H_i)|` with `keep c n = ⌊√(n/3)⌋/5 − (c² + 3)` and show that
   `keep^[c](N) → ∞` (`iterate_keep_unbounded`). Each round picks the largest of three classes,
   which is simpler than the paper's mixture: stable processes (erase the others); unstable
   readers (independent set, ≥ 1/5); or unstable writers. For writers, either `⌊√X⌋` of them write
   the same variable (roll-forward: we also drop the owner of the variable and its last writer), or
   one writer per variable is kept, followed by an independent set.
9. **Invariant `S(i)`.** Properties 3–4 are merged into "every active process is stable or has
   performed at least `i` RMRs". Property 5 (bounds on the RMRs of finished processes) is not kept.
   Where bounds are needed (the module count of Lemma 6.13, the roll-forward erasures), they come
   from the contradiction hypothesis applied to histories with at most `c + 1` participants.
10. **Lemma 6.11.** Instead of `⌊N^{1/3^c}/2⌋` unstable processes we use `5(c²+1)` of them. We take
    an independent set w.r.t. "touches or sees in the next RMR" (≥ 1/5) and keep `c² + 1`, which
    then perform their next RMRs. The independent set is an artefact of our replay lemma (`advance`
    runs each process' local prefix and its RMR consecutively). The paper's "in any order" is also
    fine if all local prefixes are run first.
11. **Turán's theorem** is used in the paper as "average degree `d` ⇒ independent set ≥ `n/(d+1)`".
    We prove a greedy variant for digraphs of out-degree ≤ `d`: `|I| ≥ n/(2d+1)`, which is what the
    application needs (`Cslib.exists_indep_of_outdeg`). Out-degree 2 (owner and last writer of the
    target) gives the paper's 1/5.
12. **Order of next RMRs.** The paper applies all next reads first and then deals with writes. Our
    rounds never mix reads and writes, so the order issue does not arise.

## Modelling choices

13. **Executions are event lists that record the accessed variable and the value read.** Validity
    = local consistency of each process' events + every read returns the latest write. The
    algorithm interface (`invoke`, `act` with `read`/`write`/`ret`) mirrors
    `Cslib.SharedMemory.Impl` over registers. The CSLib label model (`tau` steps without data) was
    not used directly, because erasing (Lemma 6.7) and the "last writer" notions need the data on
    the events. No bridge to `Impl` is formalized.
14. **Termination = staying idle forever.** There is no explicit terminate step. A process that
    stops in mid-call is not crashed; such a history is just unfair, or a prefix. The paper's
    "terminating" is `Algorithm.Terminating` (fair infinite histories, at most one `Signal()`). The
    lower bound uses only `SoloTerminating`: from any execution with ≤ 1 signal in which all other
    processes are idle, the current call of `p` completes when `p` runs solo. We prove
    `Terminating → SoloTerminating`, so the formal theorem is at least as strong as the paper's.
15. **Specification 4.1 only in executions with at most one `Signal()` call.** This matches the
    variant "one signaler" and is a weaker hypothesis than requiring it in all executions. The
    witness execution has exactly one `Signal()`.
16. **Participants** include processes whose only event is an invocation. This can only increase
    `k`, so the conclusion `rmr > c·k` is at least as strong as with the paper's "takes at least one
    step".
17. **Histories `H_A`** are all finite valid executions. The paper's `H_A` consists of complete
    histories and their finite prefixes, and for a terminating algorithm every finite execution is
    such a prefix.
18. **`ret` steps are separate local steps** (no memory access, no RMR), as in CSLib's model.
19. **CC RMRs (Section 5)** follow the paper's loose definition (`ccRMR`). A read is free if the
    process read the variable before and no other process has written it since. Writes always cost
    1, which is conservative. We prove ≤ 2 RMRs per process (the paper says `O(1)`), in executions
    with one signaler.
20. **Section 5's algorithm** stores `B` in process `0`'s module. The placement is irrelevant in the
    CC model. It requires `N ≥ 1` (`NeZero N`).
