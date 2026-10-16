# Differences between the formalization and the paper

Paper: Abraham, Nayak, Ren, Xiang, *Good-case Latency of Byzantine Broadcast: a Complete Categorization*,
PODC 2021 (arXiv:2102.07240v3; numbering follows it).

Summary: every lower bound we formalized holds in its intended range. Several statements are false in degenerate
cases (`n ≤ 3`), one proof (Theorem 19) gives more than it claims and does not cover `f = n − 1`, and the
lower-bound executions need small changes to respect unforgeable signatures. The 2-round BRB protocol
(Theorem 5) is verified. The other upper bounds (Figures 3, 5, 6, 9, 10) are not formalized, except the timing
core of Lemma 1.

## 1. Errors and gaps in the paper

1. **Theorem 10, read literally, is false for `n = 3`** (`f = 2, 3`). *(False only in a degenerate case,
   outside the intended range.)* Table 1 and §5.4 use `n/3 < f < n/2`, which no integer `f` satisfies for
   `n = 3`; the counterexample (`f ≥ n/2`) refutes only the literal hypothesis `f > n/3`. For three parties a
   simple protocol has good-case latency `Δ + δ < Δ + 1.5δ`, for every `f`. A non-broadcaster commits the
   proposal `Δ` after first learning it if it saw no conflicting proposal. A party that saw two proposals adopts
   the commit certificate of the other non-broadcaster. The latency is proved both with synchronized start
   (`three_latency`) and, as in Definition 6, with unsynchronized start, measured from the broadcaster's start
   (`three_latency_unsync`, any skew allowed by `UValid`). Lean: `ThreeParties.theorem_10_false_three`,
   `ThreeParties.theorem_10_n4_necessary`. The paper's proof needs five groups `g, h, A, B ∋ s, C` with `A ≠ ∅`,
   i.e. `n ≥ 4`; we prove Theorem 10 for `n ≥ 4` (`Thm10.theorem_10`).
2. **Theorems 4, 8 and 9 are false for `n = 2`** (any `f ≥ 1`). *(False only in a degenerate case.)* With one
   non-broadcaster, "commit the first value received from the broadcaster" is BRB and commits after one message
   delay (one round, resp. `δ`). Lean: `theorem_4_false_two`, `theorem_8_false_two` (`SmallCases.lean`). The
   proofs need two non-empty groups besides the broadcaster; our theorems assume `n ≥ 3`.
3. **Theorems 6 and 7 fail for `n = 1`** (latency 0). *(Out of range: `n = 1` forces `f ≥ n`, outside the
   paper's implicit `f < n`.)* `theorem_7_false_one`. For `n = 2`
   and for `n = 3, f = 1` psync-BB is unsolvable, so Theorems 6 and 7 hold vacuously there (`PsyncSmall.lean`);
   the paper's own proof of Theorem 7 needs `f ≥ 2` and `n ≥ 3`.
4. **Theorem 19: the proof gives a stronger bound than stated, and it fails for `f = n − 1`.**
   *(a) Not an error, the bound is just not what the proof gives.* The executions of the proof give
   `⌊n/(n−f)⌋·Δ`, one `Δ` more than the claimed `(⌊n/(n−f)⌋ − 1)Δ`, once the good-case proposal is delayed by
   `Δ` (allowed). For `f = n/2` the paper's bound `Δ` is weaker than Theorem 9 (`Δ + δ`); ours is `2Δ`. Lean:
   `dishonestMajority_lower_bound`, and `theorem_19` for the paper's statement. *(b) Proof gap in a degenerate
   case.* For `f = n − 1` the groups `G_i` with odd `i` have size `n − f − 1 = 0`. The executions then have a
   single honest party, and agreement gives nothing. The hypothesis `n − f ≥ 2` of our stronger bound is
   necessary. For `n = 3, f = 2`, the 3-party protocol of item 1 at `δ = Δ` commits by `2Δ < 3Δ`; this
   transfer to the synchronized-start `IsBRB` formulation is argued informally. The paper's `(n − 1)Δ` holds
   for `n = 3`: it is Theorem 9 with `δ = Δ` (`theorem_19_three`). For `n ≥ 4` and `f = n − 1` we prove
   `⌊n/2⌋Δ` by monotonicity in `f` (`allButOne_lower_bound`), without showing it tight. *(c) Typo.* The broadcaster's split
   ("0 to `G_j` for `1 ≤ j ≤ (d+1)/2`, 1 to `G_j` for `(d+1)/2 ≤ j ≤ d+1`") gives both values to the middle
   group.
5. **Unforgeability in the lower-bound executions.** *(Proof gaps, all fixable; the statements are unaffected.)*
   The paper assumes ideal signatures but never checks that Byzantine parties can send what the executions make
   them send.
   - **Theorem 10, Executions 2/3.** As written they are not valid executions. In Execution 1 the Byzantine `C`
     and `h` behave honestly with value `0` and use the default delay `δ` towards the honest `B`. So `B`'s
     messages may relay `C`'s and `h`'s signatures on value-0 messages. In Execution 2, `B` must replay these
     messages to `g` until about `Δ + 0.5δ`, but `C` is honest there and holds value `1`, so it never produced
     those signatures. Execution 3 has the same problem for `h`. Fix used: in Executions 1 and 4, `C → B` and
     `h → B` messages (resp. `A → B`, `g → B`) are delayed beyond the replay horizon. `X_authValid` checks the
     repaired executions with a causal replay lemma (`tokens_replay_rel`).
   - **Theorems 7 and 9.** Byzantine replays of other executions must be truncated in time: later messages
     carry signatures that are never produced in the new execution. This is harmless for the argument.
6. **Lemma 1 (proof imprecision, statement correct).** The proof of part (1) says: if `h'` receives `v'` by
   `t − Δ` (`t` = commit time of `h`), the forwarded proposal "stops `h` from committing". Step 4a only requires
   no equivocation until `t_prop + Δ + 0.5d`, which can be earlier than `t` when the votes arrive late, so this
   step is not justified as written. Comparing with `t_prop + 0.5d` instead works for parts (1) and (2). We
   check this abstract timing core (`Lemma1.part1`, `Lemma1.part2`); the protocol itself is not formalized.
7. **Theorem 10, Execution 1, minor.** The main text says the Byzantine `C` "pretends to start `0.5δ` later";
   the appendix uses honest start with modified delays instead. We follow the appendix.
8. **Implicit size assumptions (not errors).** Theorem 7 needs a non-empty `A` and `B ∪ E ≠ ∅` (`n ≥ 3`, `f ≥ 2`).
   Theorem 9 needs `n ≥ 3`. Theorem 19 needs `n − f ≥ 2` (see 4b). All lower bounds need `|V| ≥ 2`.

## 2. Model

1. **Shared model.** CSLib `Cslib.Byzantine.PartialSync`. Discrete time; deterministic state machines that
   take one step per tick from their start; batched delivery with a delivery time chosen by the adversary;
   static Byzantine faults; ideal signatures as abstract tokens (`Auth`, `Algorithm.Unforging`,
   `Run.AuthValid`). Every lower bound is proved for authenticated protocols, which is the setting of the paper,
   and so covers the unauthenticated case. Every process has an input; only the broadcaster's input matters for
   the specifications. The lower bounds use executions in which the other inputs are fixed.
2. **Specifications** (`Basic.lean`). `IsBRB`, `IsBB`, `IsPsyncBB` follow Definitions 2–4. Agreement covers
   all pairs of correct processes including `p = q`, so a process cannot change its decision. Commits are read
   off the state (`decide`). "Terminate" is not modelled; it is irrelevant for the properties. psync-VBB
   (external validity) is not used.
3. **Synchrony, time convention.** A batch sent at `τ` and delivered at `dl` is visible in the state at time
   `dl + 1`; its *effective delay* is `dl + 1 − τ`. Thus the state at time `t` is the local history at time
   `t`, and "commits before `T`" is `CommitsBy … (T − 1)`. `SyncValid f d` means effective delays in `[1, d]`
   between correct processes. The paper also allows delay 0; forbidding it weakens the adversary, so the lower
   bounds are stronger statements. The protocol must be correct for all runs with delays `≤ Δ` (known bound).
   Good-case latency for actual bound `δ` quantifies over runs with delays `≤ δ` (Definition 6).
4. **Partial synchrony.** We use CSLib's convention verbatim (`Run.Valid f D`, delays `dl − τ ∈ [0, D]` after
   GST) and rounds of length `D`. "Commits within `r` rounds" means the state at time `rD + 1`
   (`PsyncGoodCaseRounds`), as in the formalization of Kuznetsov–Tonkikh–Zhang. The lower bounds exhibit
   lock-step executions (round-`r` messages delivered at `rD`). Theorem 6 is proved in the stronger form "not
   committed at time `2D`", i.e. before the round-2 messages are processed.
5. **Asynchrony (Theorems 4, 5).** Asynchronous executions are all runs of the model (`asyncRuns`: any GST,
   any delay bound). Every such run eventually delivers all messages, but not every fair asynchronous execution
   is such a run, so the positive Theorem 5 is proved for this class only. Asynchronous rounds (Definitions
   9–10) are not formalized. Theorem 4 is stated for lock-step executions: there a protocol with good-case
   latency of 1 asynchronous round would commit by time `D + 1`, and we show it does not commit even by `2D`.
   Theorem 5's latency is proved as "every honest party commits by `2Δ` in synchronous runs with delay bound
   `Δ`", i.e. two message delays.
6. **Unsynchronized start** (`Unsync.lean`). The protocol is an ordinary algorithm, run through the wrapper
   `lateStart A` whose input `(v, k)` gives the start time `k`. Before its start a process is silent and drops
   what it receives. `UValid f d σ` forbids correct-to-correct messages from arriving before the receiver
   starts. This weakens the adversary, so the lower bound is stronger. The constraint covers all send times,
   including time-0 batches, so every correct process starts before time `d`, the run's delay bound. Theorem 10 is stated with skew
   `σ = δ/2` in the protocol's requirements (as the paper assumes), `δ = 2e` even, and `δ < Δ`; the latter is
   needed because the execution uses delay `Δ − δ`, which must be `≥ 1` in our model. Good-case runs have
   synchronized start, which is a subset of the paper's good case. Unforgeability is assumed for the wrapped
   algorithm `lateStart A`.
7. **Byzantine parties that "behave honestly in another world".** We model each as a correct process of an
   auxiliary run (with the paper's modified delays) and make it Byzantine with `Run.enlarge`. For Theorem 10,
   Executions 2 and 3 are then the *same* auxiliary physical execution up to the start-time shift of `A` and
   `C` (`claim2`). Delays the paper calls `∞` are replaced by a finite `L` beyond every relevant horizon.
8. **Theorem 7.** In Execution 1 the Byzantine `E` also sends its round-0 messages to `A`. They equal those of
   an honest `E`, which `A` receives in Execution 2 too. This lets us reuse the executions `ρ₁…ρ₅` of the
   Kuznetsov–Tonkikh–Zhang formalization (`Papers/PODC2021/FastByzantineConsensus/Executions.lean`), which are
   exactly Figure 4 with `p` = broadcaster.
9. **Theorem 19.** The ring of groups is a time-dependent covering system with uniform delay `Δ`
   (`DelayCover.lean`). The broadcaster has two copies (left/right), each talking only to its neighbour group
   after the proposal. Locality ("information travels one group per `Δ`") replaces the paper's informal
   distance argument.
10. **Theorem 5 protocol.** Parties gossip all known signed tokens instead of "forwarding the `n − f` votes". A
    party votes for the first proposal token of `s` it knows, possibly relayed by others; simultaneous
    proposals are tie-broken by choice. The latency statement holds without `n ≥ 3f + 1`.

## 3. Not formalized

The upper-bound protocols of Figures 3 (`(5f−1)`-psync-VBB, Theorems 12–15), 5, 6, 9, 10 (Theorems 11, 16,
17, 18) and the BA primitive they use, Lemma 1 (3), Lemma 4. Asynchronous rounds (Appendix A). The `O(n/(n−f))Δ`
upper bound.
