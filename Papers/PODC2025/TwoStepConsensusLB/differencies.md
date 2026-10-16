# Differences between the formalization and the paper

Paper: Ryabinin, Gotsman, Sutra, *Revisiting Lower Bounds for Two-Step Consensus*, PODC 2025 (brief
announcement); full version arXiv:2505.03627v2 (numbering follows it).

## Model (both directions)

1. **Discrete time, one tick = Δ** (`Model.lean`). At every time `τ` an alive process receives the messages
   delivered at `τ` together with an optional invocation, makes one atomic transition and sends messages (they
   arrive at `≥ τ + 1`). Round `k` of the paper is the step at time `k − 1`; "decides by time `2Δ`" is "decides
   in the state after its step at time `2`" (`DecidedBy2`, state at time `3`). The paper's continuous time with
   instantaneous local computation is coarser in our model only in that a process cannot act between two
   message arrivals; in synchronous runs, where all messages arrive at multiples of `Δ`, this changes nothing.
2. **Delivery order is adversarial.** Messages delivered to a process at the same time are processed in an
   order chosen by the run (`Run.ord`, must be a permutation). The paper's "there exists an `E`-faulty
   synchronous run" (Definitions 4, 5) quantifies over this order. This matters for the upper bound: the paper's
   two-step argument chooses which `Propose` is received first. (With a fixed processing order the paper's
   protocol would not satisfy Definition 4 (2).)
3. **Processes see the global time** (synchronized clocks, `step p τ …`). For the lower bounds this only makes
   them stronger (it gives protocols more power).
4. **Reliable links connect correct processes only.** A batch from or to a faulty process may be lost
   (`Run.Valid` constrains only correct→correct batches: delivered in `[τ + 1, max τ gst + 1]`). The paper's
   proofs need this too: after `crash(F ∪ {p})` the round-2 messages of the crashed processes, which differ
   between the two merged runs, must never be delivered ("any continuation of one run is also a continuation of
   the other"). This is the standard "perfect links between correct processes" semantics; in a model where every
   message of a process that crashes later must still be delivered, the paper's construction (and ours) does
   not apply verbatim.
5. **Deterministic protocols**, as implicitly assumed in the paper (the proofs use that a process with the same
   input starts identically in two runs).
6. **Consensus object** (§2, §A). Invocations are part of the run (`Run.inv`); a run is well formed if each
   process invokes at most once. A response is a decision exhibited after an invocation (`RespondsAt`).
   Linearizability of the consensus object is stated as agreement of responses plus "a returned value was
   proposed before it was returned" (`SolvesObject.validity`), which is equivalent for one-shot consensus.
   Wait-freedom: every invocation by a correct process returns.
7. **Agreement is uniform** ("no two decisions are different", decisions of processes that crash later
   included), as in the paper. Safety and liveness are required only in runs with at most `f` crashes.
8. **Definition 5 (1)** does not say when `p` calls `propose`; we allow any time `t₀` (existential, so this
   only weakens the hypothesis of the lower bound).

## Lower bounds (Theorems 1, 2 "only if"; §B) — statements true, proofs repaired

9. **Hypothesis `n ≥ 2`** (paper: `n ≥ 3`). Needed: for `n = 1` "decide your own input" is `1`-resilient and
   `0`-two-step although `1 < max {2e+f, 2f+1} = 3` (`theorem_1_fails_n_one`). False only in a degenerate case
   outside the paper's assumptions.
10. **Proof gap (true statement): only `n = 2e + f − 1` (Thm 1) and `n = 2e + f − 2` (Thm 2) are treated.**
    "We now prove the rest by contradiction. Thus, assume n = 2e+f−1" — smaller `n` are not covered by the
    construction as written (the partition sizes `|F₀| + |F₁| = f − 1` require equality). The reduction
    (an `f`-resilient protocol is `f'`-resilient for `f' = n − 2e + 1 ≤ f`) is not stated. We prove the bounds
    for every `n` directly (Lemma 3 with `|F₀| + |F₁| = n − 2e ≤ f − 1`; in Theorem 2 `|F| = n − 2e ≤ f − 2`).
11. **Lemma 2** ("proof omitted") is proved (`syncRun_st_eq`).
12. **Proof gap: validity of the fast decision in Lemma 3 (base case) and in the conclusion of Theorem 1.** "In
    σ′ all correct processes propose 0. Thus, in σ′ the decided value is 0": Validity only says the decision
    is the proposal of *some* process, and the crashed processes of `E₁` propose 1. One needs Lemma 2 first
    (move the run to the configuration where everybody proposes 0). (`syncRun_decides_eq`)
13. **Lemma 3 strengthened.** We prove that *every* process deciding by `2Δ` in *every* `E₀`-faulty
    synchronous run from `Iₖ` decides `0`; the paper's existential form follows with Definition 4 (1).
14. **The merge argument is proved once** (`Merge.lean`): for an `X`-faulty and a `Y`-faulty synchronous run
    with `X ∩ Y = ∅`, deciders `d ∉ X`, `d' ∉ Y` and the same behaviour of `Z = Π \ (X ∪ Y)` in round 1,
    the two merged runs are indistinguishable for `(X ∪ Y) \ {d, d'}` forever, provided
    `|Z ∪ {d, d'}| ≤ f`. All three contradictions of §B (base case, induction step, conclusion of Thm 1) and
    §B.2 are instances. Our runs differ in details from the paper's `σ₀`, `σ₁`: we crash `Z ∪ {d, d'}` at time 3 in
    both runs, and all delayed messages between correct processes are delivered at GST = 3.
15. **Theorem 2's proof (§B.2) is restructured.** The paper builds `σ`, takes a continuation `σ̂` "during which
    a decision is taken", assumes w.l.o.g. that `1` is decided and then builds `σ′`. Two gaps: (a) in the
    object model the correct processes `E₀* ∪ E₁*` never invoked `propose`, so wait-freedom forces no decision
    — some correct process must invoke `propose` in the continuation (we let a correct `r ∉ {p, q}` invoke at
    time 3); (b) the decided value may be a third value (the one `r` proposes), the w.l.o.g. needs the remark
    that it then differs from `0`. We use instead the same symmetric merge as for Theorem 1 (`merge_object`),
    which needs only `|Z| + 2 ≤ f`. Only Definition 5 (1) is used, as the paper remarks
    (`theorem_2_lower_of_item1`).
16. **Typos in §B.** B.1 base case: `σ₀ = 1σ_{E₀′∪F₀} …` should read `E₀` (no `E₀′` in the base case).
    B.2: `σ′ = … decide(p, 1) …` should be `decide(p, 0)`; "`F ∪ {p, q} = f`" should be `|F ∪ {p, q}| = f`;
    `E₀*`, `E₁*` require `p ∉ E₁`, `q ∉ E₀` (implicit). Brief announcement Fig. 1, lines 33 and 35: `∀ q ∈ Q_f` should be
    `∀ q ∈ S` (correct in arXiv v2).
17. **Introduction (EPaxos remark).** "EPaxos decides within two message delays under `e = ⌈(f+1)/2⌉` failures
    while using only `2f + 1 = 2e + f − 1` processes; Lamport's bound requires `2f + 3 = 2e + f + 1`": both
    equalities hold only for even `f`. For odd `f` (e.g. `f = 1`, `e = 1`), `2f + 1 = 2e + f`, which is the
    task bound, and Lamport's bound is `2f + 2`. Imprecision in a motivating remark; not formalized.

## Upper bounds (Theorems 1, 2 "if"; §3, §C)

18. **Object protocol not wait-free: false claim (§C.3, Theorem 2 "if").** Formal counterexamples on the
    abstract transition system: `Fig1.object_not_wait_free_omega` (Ω stable on a correct `l ≠ r` that never
    invoked; `r` invokes after all processes moved to a slow ballot; `n − f − e ≥ 1`, i.e. all admissible
    parameters) and `Fig1.object_not_wait_free` (`p` proposes, only `r` accepts, `p` crashes, `r` invokes
    later; any leader election; `n − f − e ≥ 2`, e.g. `n = 7, f = 3, e = 2`). In both, no process ever decides
    from the reachable configuration on, whatever the schedule. **Fix** (`Config.fallbackVal`, `Impl.fig1`
    with `obj = true`): at lines 37–38 the leader falls back to its own `val` when `initial_val = ⊥`
    (safe: line 37 is reached only when no value can be fast-decided and `b_max = 0`), and leaders rotate.
    The fix alone does not repair the Ω version (first counterexample).
19. **Ω replaced by rotating clock-driven ballots** (`Impl.lean`): ballot `b ≥ 1` starts at time `5b − 3`
    (first timeout at `2Δ`, then every `5Δ` as in §C.1) and is owned by `owner b` (round robin). The owner
    sends `1A(b)` only if `b > bal` (line 22). Termination needs only `f < n`.
20. **Interpretation of line 10**: `bal` is the process's *current* ballot (2B messages of the current
    ballot). Reading it as the message's ballot breaks safety; the paper's text confirms the current-ballot
    reading. The line-9 (2B) handler fires only while `decided = ⊥` and needs a nonempty sender set, so the fast
    path needs `n − e ≥ 2`. The 1B handler (line 24) fires once per ballot, on exactly `n − f` distinct
    senders (the first to arrive). At lines 33/35 the maximal candidate is chosen. In line 28, `proposer = ⊥`
    counts as "not in `Q`".
21. **Lemma 1 / Lemma 5** are stated for any 1B quorum of any ballot, sent before or after the fast decision:
    lines 26–38 can select `v` and nothing else (`Fig1.lemma1`, `Fig1.lemma5`). **Lemma 5 proof gap**: the
    subcase where `v` has exactly `n−e−f` votes and another `w` satisfies line 33 is not handled by the
    paper's counting. It is excluded by the line-35 argument. Lemma 1 omits the same subcase, which counting
    excludes there.
22. **Lemma 4 proof gap** (line-30 case: `Decide` need not come from the leader of `vbal_q′`); agreement of two
    fast decisions (needs `n > 2e` and single votes at ballot 0) is never argued. Agreement is proved via a
    "potentially chosen" invariant (`Fig1Safety.lean`).
23. **Validity needs `n − f − e ≥ 1`** (with an empty `S`, line 36 would pick a maximal element of `V`). This
    follows from `e ≤ f` and `n ≥ 2f + 1`.
24. **Abstract system.** It is an asynchronous interleaving system over the set of all messages ever sent,
    so safety holds under any scheduling. Any process may start its own ballots; ballots have unique owners.
    `Decide` messages carry a ghost ballot, and processes record their `propose` argument as ghost state. The
    concrete protocol refines it handler by handler (`Impl.absState_reachable`); only a permutation delivery
    order is needed for agreement, not validity of the run.
25. **Two-step property of the protocol (§3).** In Def. 4 (1) the chosen proposer is a correct process with
    the maximal input, and its `Propose` is put first in every inbox at time 1. In Def. 4 (2) and Def. 5 the
    target process's `Propose` is put first. Def. 5 (1) uses invocation time `t₀ = 0`.
