# Differences between the formalization and the paper

Paper: Chockler, Spiegelman, *Space Complexity of Fault-Tolerant Register Emulations*, PODC 2017,
arXiv 1705.07212v1 (numbering follows the arXiv version).

## Model (Section 2, Appendix A) — `Model.lean`

1. **Base operations take effect at their response.** A low-level read or write is applied to the
   register atomically when it responds (`resp` event). The paper allows a pending write to be
   linearized earlier. It adopts our convention in the proof anyway (Assumption 1). Restricting
   runs only weakens hypotheses that quantify over all runs, so the lower bounds become stronger.
2. **Failures are not events.** A failure pattern `(Fc, Fs)` (crashed clients, crashed servers)
   enters only the fairness predicate `Alg.Fair`. Crashed clients take finitely many steps and
   invoke finitely many operations. Registers on crashed servers respond finitely often. Correct
   clients are scheduled infinitely often. Every pending operation of a correct client on a correct
   server eventually responds. Pending operations of crashed clients may still take effect, as in
   the paper.
3. **Clients** are arbitrary deterministic automata (`Alg`). They act whenever scheduled, also
   between high-level operations, e.g. to re-trigger writes as Algorithm 2 does. A client may have
   several pending operations, also on the same register. High-level invocations are environment
   events and are ignored while the client is busy. Each pending operation carries a per-client
   identifier.
4. **Obstruction freedom** (`Alg.ObstructionFree δ f Wr`) is the paper's definition specialized to
   the form the proof uses. Fix a fair run with at most `f` crashed servers in which only clients in
   `Wr` invoke writes. If a correct client invokes an operation and no other correct client is busy
   from then on, the operation returns. The paper's definition implies this one.
5. **Safety.** We assume only `Alg.SeqSafe`: in a *sequential* run (high-level operations never
   overlap), a read returns the last written value (`v₀` if there was no write). The paper's WS-Safety
   (a linearization of all writes and the read exists, for every read that is not concurrent with a
   write in a write-sequential run) implies `SeqSafe`. We did not formalize the linearization-based
   definition of WS-Safety or WS-Regularity. Since all lower bounds assume the weaker `SeqSafe`, they
   hold a fortiori for WS-Safe algorithms.
6. **`k`-register.** The writers are given as `w : ℕ → C`, injective on `{0, …, k-1}` and contained
   in `Wr`. We need one more client `rd` that is not among these writers (the paper's `c_rd`). The
   paper's client set is unbounded, so such a client exists there.
7. **Values.** The paper uses `k` distinct values `v₁, …, v_k`. We only need two values `v₀ ≠ v'`
   (consecutive writes differ, `altVal`). This is a strengthening.
8. **Resource consumption.** We count all base registers (`Fintype.card B`, the paper's
   `|δ⁻¹(S)|`) for Theorems 1 and 6, and registers covered by pending writes for Theorem 8.

## Lower bound (Section 3.2, Appendix C)

9. **Adversary `Ad_i` (Definitions 1–3).** Our adversary `rstep`/`zSet` freezes the servers
   `Q ∪ G`. Here `Q = Q_i`, and `G = F \ F_i` whenever `|Q_i| < |F_i ∩ F|`. The paper instead takes
   `G_i = M_i ⊆ F \ F_i`, the servers of `F` that have a covered register. This simplification
   removes `M_i` and its stability argument (Lemma 2.7–2.8, Corollary 1 for `M_i`). We also freeze
   the **reads** of the writer on frozen servers, not only its writes. Then the infinite strategy run
   is itself fair, with the frozen servers crashed.
10. **Lemma 3** (the write returns). In the paper the hypothetical crash run "crashes the servers in
    `Q_i ∪ M_i` immediately after `r`", where `r` ends at the invocation. The writer's reads on these
    servers keep responding in the adversary run (Definition 3.3(a)), so the two runs are not
    indistinguishable. The crash must happen at the stabilization time `t'`. With our adversary,
    which also freezes reads, the strategy run is literally fair (`fair_solo`, `exists_ret_of_solo`).
11. **Lemma 4** is proved in the form we need (`fresh_resp`). After a complete write by a fresh
    writer during which only that writer acts, the registers outside `Cov(t_{i-1})` whose value
    changed span more than `f` servers. The proof is the paper's argument (crash those servers,
    flush the covering writes in both runs, run a reader solo). We flush one covering write per
    covered register; this suffices. No adversary is needed. The paper's statement
    `|δ(Tr_i(t_r) \ Cov(t_{i-1}))| > 2f` follows from ours together with `Q ∩ F_i = ∅`. We use it in
    this form for Theorem 5 (`round_main` returns disjoint `Q`, `P` with `|Q| = f`, `|P| > f`).
12. **Corollary 2 / Lemma 2.9–2.10** are folded into the round invariant `RInv` (`small`:
    `|Q| < f → Q = covF ∧ fr ⊆ F`).
13. **Lemma 1(b)**: after the write returns, the paper extends the run "by Definition 3.3(a)" until
    no register of `F` is covered. This does not follow if the writer keeps triggering writes on `F`
    after returning. One must stop scheduling the writer. We do so: only the writer's pending
    writes on `F` respond (`flush_mem` in `lemma1_step`).
14. **Lemma 1** is stated for any `F` with `|F| ≤ f + 1` (the paper: `|F| = f + 1`). It includes the
    extended items (a), (b), (d) and (e). We state (d) as "f servers outside `F` each hold a
    register of `Cov(t_{i+1}) \ Cov(t_i)`", which is slightly stronger than the paper's (d). Item
    (c) appears only through Theorem 5. Lemma 1 says "there exist `k` failure-free runs `r_i`,
    `0 ≤ i ≤ k`", which is `k + 1` runs (typo).
15. **Lemma 2** has no separate statement. Its items that matter are the fields of `RInv`
    (`Round.lean`). Item 2.11 is written with `δ⁻¹` where `δ` is meant (typo). Items 2.6 and 2.8 are
    trivial.

## Theorems

16. **Theorem 1.** The proof's last step applies Lemma 1 with `F = G`, but `G` (the set of servers
    holding at least `⌈kf/(|S|-(f+1))⌉` registers) can have more than `f + 1` elements. The fix
    applies it to a subset of `G` of size `f + 1` (`load_bound`). We assume only `|S| ≥ f + 1` (the
    paper: `|S| ≥ 2f + 1`, `k, f > 0`).
17. **Theorem 5** holds for every `f`. It needs one writer and one further client.
18. **Theorem 6** as in the paper (`|S| = 2f + 1`, `f > 0`).
19. **Theorem 7.** The hypothesis `|S| > 2f + 1` is unnecessary. We need `k, f > 0`. The proof is
    shorter than the paper's: `kf ≤ |Cov(t_k)| ≤ m(|S| − f − 1)`.
20. **Theorem 8 is false as stated.** "There is no `f`-tolerant algorithm that emulates a WS-Safe
    obstruction-free `k`-register with resource complexity adaptive to point contention." `k` is
    fixed and `M` may depend on the algorithm, so every algorithm with finitely many registers is
    adaptive with the constant `M = |B|`. Algorithm 2 (Theorem 3) is such an algorithm. The proof
    shows only that the resource consumption grows by `f` per write over `k` writes, i.e. up to
    `kf`. Our version, `theorem8`: for every `M` there is a `k` such that every `k`-register
    emulation has a sequential run (point contention 1) with more than `M` covered registers. We
    express "point contention 1" by "the run is sequential" (`hist = seqHist _`) and do not define
    point contention.
21. **Theorem 2** (`MaxRegisterLowerBound.lean`) is proved by a direct covering argument in CSLib's
    shared-memory model, not by the paper's reduction to Theorem 1 (which runs `2f+1` copies of the
    implementation and multi-writer ABD on top). The hypotheses are weaker than the paper's:
    linearizability and obstruction freedom only on executions where only the `k` writers write;
    wait-freedom is not needed. A reader distinct from the writers is required (with a single
    process, `k = 1` and no reader, 0 registers suffice). `k > 0` is not needed.
22. **Theorem 4 / Lemma 5** (`MaxRegisterCAS.lean`, CSLib shared-memory model). Lemma 5
    (linearizability) holds over every linear order. **Theorem 4 (wait-freedom) is false for a
    dense order.** The paper defines the max register over "some domain of ordered values V". Over
    `ℚ`, one `write-max(1)` can run forever while another process completes
    `write-max(1 - 1/(j+2))` between each of its reads and CASes (`ratImpl_not_waitFree`). The
    paper's proof assumes, without saying so, finitely many values between `v'` and `v`. Exact
    condition: `waitFree_iff`, i.e. every interval `[v₀, c)` has no infinite increasing sequence.
    Over every linear order the algorithm is lock-free (`lockFree`). Minor point: the specification
    "highest written value, or `v₀`" matches the algorithm only if `v₀` is the minimum. We use
    `max(v₀, written values)`. A pending write-max is linearized at its first step that observes
    `b ≥ v`; for completed operations this is Definition 4.
23. **Theorem 3 / Algorithm 2** (`Algorithm2*.lean`, in our model).
    - **Error (indexing slip with evident intent): the writer-to-set mapping.** The paper's mapping `j = ⌊i/z⌋` (1-based `i`) overloads a
      register set, and then the algorithm is not WS-Safe (`Alg2.Counterexample.not_seqSafe_paperMapping`,
      run with `n = 4`, `f = 1`, `k = 3`). We prove the algorithm correct for every `Layout`: writers'
      sets lie on distinct servers, non-writers own no registers, and
      `#(other writers sharing a set with c) · f + 2f + 1 ≤ |R c|`. The fixed mapping `⌊(i−1)/z⌋` is
      such a layout, with exactly `kf + ⌈k/z⌉(f+1)` registers (`Alg2.theorem3`, `Alg2.theorem3_wsRegular`).
    - `collect` triggers reads of all registers in parallel and waits until all registers of some
      `n − f` servers have responded. The paper scans each server sequentially. Triggers and
      re-triggers (lines 8–10, 30–32) are queued and issued one per client step. Late read responses
      are accepted.
    - Wait freedom (`Alg2.WaitFree`) is stated in our fairness model: every operation of a correct
      client returns in every fair run with at most `f` crashed servers. It implies our
      `ObstructionFree`.
    - WS-Regularity (`Alg2.WSRegular`) is stated by a one-pass scan of the history: in a
      write-sequential history, every complete read returns the value of the `t`-th write for some
      `t` between the number of writes completed before the read started and the number of writes
      invoked before it returned (`v₀` for `t = 0`). For write-sequential histories this is
      equivalent to the existence of a linearization of the writes and the read. We do not prove
      that equivalence.
    - Lemma 7's claim "every low-level write triggered after `t` has a bigger timestamp" is false
      (`Alg2.Lemma7.retrigger_old_timestamp`), but the conclusion of Lemma 7 holds. The counting
      "each writer covers at most `f` registers" (Observation 3, Lemmas 6–7) has to be done relative
      to the coverage at the start of `W` plus the registers released since then.
24. **Not formalized:** the table's max-register/CAS upper bound `2f + 1` (the multi-writer ABD
    observation in the introduction); Section 3.1 (intuition).
