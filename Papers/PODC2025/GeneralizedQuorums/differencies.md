# Differences between the formalization and the paper

Paper: A. Naser-Pastoriza, G. Chockler, A. Gotsman, F. Ryabinin, *Tight Bounds on Channel Reliability via Generalized
Quorum Systems*, PODC 2025 (arXiv:2505.02646v1, identical to the proceedings version plus appendices).

## Model (`Podc/Computability/Distributed/MessagePassing/ChannelFailures/Model.lean`)

1. **FIFO channels.** The paper's channels are unordered. Our channels are FIFO (`deliver q p` delivers the head).
   This only restricts the adversary, so the lower bounds (Lemma 2, Theorems 2 and 6) are *stronger* in our model:
   an algorithm only has to be safe and live on FIFO executions. (For the protocol of Figure 3, whose safety we
   check in `QuorumAccess*.lean`, FIFO channels make the safety claim slightly weaker than over unordered channels.)
2. **Failures are not events.** A crash is "the process takes finitely many steps", a disconnection is "a suffix of
   the messages on the channel is never delivered". A failure pattern `f = (procs, chans)` only enters fairness
   (`Fair f`): every process that is not crashed (= not in `f.procs`, or in `f.procs` but taking infinitely many steps)
   takes infinitely many spontaneous steps, and every channel not in `f.chans` between non-crashed processes eventually
   delivers each message. With FIFO channels this is exactly the paper's `f`-compliant fair execution ("from some
   point on the channel drops all messages" = the undelivered messages form a suffix). Finite executions are hence
   failure free; they are exactly the finite prefixes of executions with failures.
3. **Algorithms** are deterministic, event driven, with total transitions `handle p i l` for an invocation, a
   spontaneous step `tick c` (with a clock reading `c`, ignored by asynchronous algorithms — the adversary chooses it
   in the asynchronous model) or a reception. Fairness requires infinitely many *spontaneous* steps of each correct
   process (the paper: "takes infinitely many steps"; our condition is stronger, so the set of fair executions is
   smaller and the lower bounds stronger). Blocking `wait`s are expressed by keeping information in the local state.
   Determinism is no loss of generality for the lower bounds: the paper's liveness notions require termination in
   *every* fair execution (no probabilistic termination is considered), so a nondeterministic algorithm can be
   replaced by any deterministic refinement (its fair executions are fair executions of the original). Randomized
   algorithms with probability-1 termination are outside the scope of both the paper and the formalization.
   In the asynchronous model the clock reading `c` of a `tick` is chosen by the adversary; the paper's (clockless)
   algorithms correspond to algorithms ignoring it. Safety (`Satisfies`) is required for all finite executions,
   including non-monotone clock readings; under partial synchrony an algorithm can clamp readings to the maximum seen
   so far, so this does not strengthen the hypothesis either.
4. **Well-formed clients** are built into the model: an invocation at a process with a pending operation is ignored,
   and a response is recorded only for a pending operation.
5. **Failure patterns** are arbitrary pairs of sets; the paper's requirement that `C` only contains channels between
   correct processes is not needed. Termination mappings must satisfy `τ(f) ⊆ P \ f.procs` — in the paper this is part
   of the definition of a termination mapping; we state it as a hypothesis (`hτ`).
6. **Obstruction-freedom** (`ObstructionFree f T`): for every fair `f`-execution, every `p ∈ T` and every effective
   invocation of `p` at time `t₀` that *eventually executes solo* (`EventuallySolo`: from some time `T₁ > t₀` on, all
   effective invocations are by crashed processes, and every other process with an operation pending at `T₁` crashes),
   the operation returns (`Returns`: a response label of `p` at some time `≥ t₀`). The lower-bound proofs use it only
   for executions where the operation is the only one ever invoked.
7. **Safety** (`Satisfies Spec`): every finite execution's history satisfies `Spec` (the paper: all executions are
   safe).
8. **Partial synchrony** (`PartiallySynchronous f ev time`, §7): a timed execution with discrete, monotone, unbounded
   time; clock readings are monotone; there are `GST` and `Δ` such that after `GST` clocks do not drift (reading =
   time + per-process offset), every correct process takes a spontaneous step at every time unit, and every message in
   transit at a time `≥ GST` on a reliable channel between correct processes is delivered within `Δ`. The paper allows
   arbitrary delays for messages sent before GST; we deliver them by `GST + Δ` (DLS style), i.e. a smaller class of
   executions, which only strengthens Theorem 6. Real-valued time and timers are replaced by discrete time and a
   spontaneous step per time unit.
9. Processes are a finite type (`Fintype P`); messages and local states are arbitrary types.

## Definitions (`Defs.lean`)

10. **"Strongly connected in `G \ f`"** (f-availability, Proposition 1, `U_f`) is read as *mutual reachability in
    `G \ f`* (paths may leave the set), as in the proof of Proposition 1 and the definition of `U_f` as "the strongly
    connected component containing `U`". Under the *induced subgraph* reading Proposition 1 is false
    (`proposition_1_false_induced`, `Examples.lean`).
11. `U_f` is defined as `{p | ∃ u ∈ U, u ⇝ p ∧ p ⇝ u}`; we prove it is strongly connected, non-empty for `f ∈ F`
    and maximal (`Uf_stronglyConnected`, `Uf_nonempty`, `mem_Uf_of_reach`). `U_f` depends on `(R, W)`, not only on `F`
    (`Uf_not_unique`, `Counterexamples.lean`); the remark after Theorem 2 that "`U_f` is the largest set of processes for
    which termination can be guaranteed" has to be read for the quorum system built in the proof.
12. Definition 1 vs Definition 2: we prove their equivalence when no failure pattern of `F` has failed channels
    (`isGQS_iff_isQS`), which is the paper's hypothesis "`C = ∅`".

## Objects (`Objects.lean`)

13. **Lattice agreement** over any partial order `V` (the paper: a join-semilattice). Upward validity `y ≤ ⨆ X` is
    stated as "`y` is below every upper bound of the proposed values", which is equivalent in a join-semilattice and
    needs no `⊥`. The specification only constrains *single-shot* histories (no process proposes twice); Downward
    validity is "`x ≤ y` for the proposal `x` of the deciding process".
14. **Consensus**: Agreement and Validity, for single-shot histories.
15. **MWMR registers**: linearizability w.r.t. CSLib's `register V v₀` (a `write` returns the written value as a dummy
    acknowledgement).
16. **SWMR snapshots**: our own `snapObj P V v₀` (one segment per process, `update i v`, `scan`); linearizability is
    required for histories in which every process only updates its own segment; `update` returns the constant view
    `fun _ => v₀` as a dummy acknowledgement (it must carry no information: an `update` returning the previous view
    would be a strictly stronger object, an "update-and-scan", and the theorem would only cover algorithms for it).
17. **Non-trivial value domains (missing hypothesis).** The paper's proofs pick two incomparable lattice elements; our
    theorems assume two incomparable elements (lattice agreement) or two distinct values (registers, snapshots,
    consensus). The hypothesis is necessary: lattice agreement over a chain is solved by returning one's own proposal,
    with no communication, under a fail-prone system that has no generalized quorum system
    (`theorem_2_false_of_chain`).

## Proofs

18. **Lemma 2 and Theorem 2 are proved for every object with "conflicting operations"** (`Conflict`: two solo
    histories whose sequential composition is unsafe), not only lattice agreement. Registers, snapshots and consensus are
    obtained directly (`conflict_reg`, `conflict_snap`, `conflict_cons`), **not via the constructions of [2], [11]**
    (snapshots from registers, lattice agreement from snapshots) or "consensus implements an MWMR register", which the
    paper uses without detail (with obstruction-freedom restricted to `τ(f)`, and, for consensus, needing infinitely many
    single-shot instances). Those reductions are not formalized.
19. The liveness assumption is used only through `SoloTerm` (after any finite prefix without invocations, a solo
    operation of `p` followed by a canonical round-robin continuation returns). Both asynchronous and partially
    synchronous obstruction-freedom imply it (`soloTerm_of_obstructionFree`, `soloTerm_of_obstructionFreePS`); so
    Theorem 6 is proved directly (the paper: "the lower bound for lattice agreement remains valid since σ is finite";
    one also needs the executions `α₁`, `β₁` to be partially synchronous, which our canonical continuation is,
    `ps_extend_canon`).
20. The executions `α₁`, `β₁` of the paper "fail the processes and channels of `f` at the beginning"; ours never
    schedule `f.procs` and never deliver on `f.chans` (canonical continuation).
21. **Gluing without reordering.** The paper builds `σ = α₃|_{R_f∖W_f} · α₃|_{W_f} · δ|_{R_g}` (Theorem 2) and
    `σ = α₃|_{R_u} · δ · α₃|_{S_u}` (Lemma 2). We use `σ = α|_{X₁} · δ|_{X₂}` with `X₁ = R_f`, `X₂ = R_g` (Theorem 2) and
    `X₁ = R_u ∪ S_u`, `X₂ = R_u ∪ R_v ∪ S_v` (Lemma 2), where `β = α|_{A₁} · δ` with `A₁ = R_f ∖ W_f` resp. `R_u`; the key
    condition is `X₂ ∩ X₁ ⊆ A₁` (Claims 2–3). In Lemma 2 our `σ` runs `u`'s operation first and then `v`'s (the paper:
    `v`'s first). Claims 1–3 are the closedness facts `closed_reachTo`, `closed_reachTo_not` and the inclusion
    `X₂ ∩ X₁ ⊆ A₁` in `lemma_2_of_soloTerm` / `theorem_2_of_soloTerm`.
22. In Theorem 2 we choose one representative `t_f ∈ τ(f)` and set `W_f` = SCC of `t_f`, `R_f` = processes reaching
    `t_f`; by Lemma 2 this is the paper's "SCC containing `τ(f)`".

## Not formalized

23. Theorem 1 (upper bound for registers, snapshots, lattice agreement), Theorem 4 (liveness of Figure 3, which also
    needs message forwarding, assumed w.l.o.g. in §5), the register protocol of Figure 4 and its linearizability
    (Appendix B, Theorem 7 from Adya's thesis), Theorem 5 and the consensus protocol of Figure 6.
    Proposition 2 (no proof in the paper) is proved in an abstract real-time form, not tied to the event model: after
    GST process `p` is in view `v` during `[a_p + C·v(v−1)/2, a_p + C·v(v+1)/2)` (`proposition_2`).
    (Example 9's claim that `F'` admits no generalized quorum system is proved: `example_9`. In Figure 1 we read
    `f_i` as: process `i+3` may crash, and among the others exactly the channels `(i+2, i)`, `(i, i+1)`, `(i+1, i)`
    are reliable, as stated for `f₁` in Example 1 and rotated.)
24. For Figure 3 we formalize the protocol (without the message forwarding needed only for liveness) and prove its
    safety: Validity (`QA.validity`) and Real-time ordering, which includes Lemma 1 (`QA.realtime_ordering`), in
    `QuorumAccess.lean` / `QuorumAccessProof.lean`, using only Consistency of the quorum families. Encoding choices: the
    opaque state is the set of identifiers of the applied updates (an update is identified by its `quorum_set`
    invocation, `(p, k+1)` for the `k`-th operation of `p`); `quorum_get` returns the list of states of the chosen read
    quorum; each process keeps, per sender, the `GET_RESP` with the highest clock (the wait at lines 8/20 is for a read
    quorum whose latest clocks are large enough); waits are re-evaluated after every step; Validity is stated for a
    history ending with the `quorum_get` response.
