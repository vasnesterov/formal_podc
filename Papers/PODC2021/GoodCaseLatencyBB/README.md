# Good-case Latency of Byzantine Broadcast — PODC 2021

Ittai Abraham, Kartik Nayak, Ling Ren, Zhuolun Xiang. *Good-case Latency of Byzantine Broadcast: a Complete
Categorization.* PODC 2021, pp. 331–341. DOI [10.1145/3465084.3467899](https://doi.org/10.1145/3465084.3467899).
Formalized version: arXiv:2102.07240v3 (numbering follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All the lower bounds of Table 1 hold in their intended ranges, and we
formalized every one of them: 2 rounds (asynchrony and partial synchrony), 3 rounds for `n ≤ 5f − 2`, `2δ`,
`Δ + δ`, `Δ + 1.5δ` with unsynchronized start, and `Θ(n/(n−f))Δ`. We also verified the 2-round BRB protocol.
Three kinds of fixes were needed:
- several theorems are false for very small `n`, mostly outside the paper's intended ranges;
- the proof of the dishonest-majority bound gives one `Δ` more than claimed, and does not cover `f = n − 1`;
- the paper never checks unforgeable signatures in its lower-bound executions, and the `Δ + 1.5δ` executions are
  invalid with signatures until they are slightly modified.

## Mistakes in the paper

- **Theorem 10 (`Δ + 1.5δ` with unsynchronized start, `f > n/3`), read literally, is false for `n = 3`.**
  For `n = 3` no integer `f` satisfies the paper's intended range `n/3 < f < n/2` (Table 1, §5.4). The
  counterexample has `f ≥ n/2`, so it refutes only the literal hypothesis `f > n/3`; this is a degenerate case.
  With three parties there is a simple BRB protocol (any `f`) with good-case latency `Δ + δ`, measured from
  the broadcaster's start. We prove this latency both with synchronized start and with unsynchronized start,
  for any skew allowed by our model; that model forces correct parties to start before time `δ`. A
  non-broadcaster commits the proposal `Δ` after first learning it, provided it has seen no conflicting
  proposal. A party that saw two proposals adopts the commit certificate of the other non-broadcaster. The
  paper's proof needs five groups `g, h, A, B ∋ s, C` with `A` non-empty, i.e. `n ≥ 4`. We prove Theorem 10
  for all `n ≥ 4` (`Thm10.theorem_10`, `ThreeParties.theorem_10_false_three`,
  `ThreeParties.theorem_10_n4_necessary`).
- **Theorems 4, 8 and 9 are false for `n = 2`.** With a single non-broadcaster, "commit the first value
  received from the broadcaster" is BRB and commits after one message delay. The proofs need two non-empty
  groups besides the broadcaster. For `n = 1`, Theorems 6 and 7 fail too. That case forces `f ≥ n`, outside
  the paper's implicit `f < n`, so it is out of range rather than an error. Theorems 6 and 7 hold vacuously for `n = 2`
  and for `n = 3, f = 1`, because psync-BB is unsolvable there. The paper's own construction for Theorem 7 needs
  `f ≥ 2`. All of these are degenerate cases (`theorem_4_false_two`, `theorem_8_false_two`,
  `theorem_7_false_one` (out of range), `psyncBB_impossible`).
- **Theorem 19 (`f ≥ n/2`): the proof gives `⌊n/(n−f)⌋Δ`, one `Δ` more than the stated
  `(⌊n/(n−f)⌋ − 1)Δ`.** It suffices to let the good-case proposal take `Δ` instead of `0`. For `f = n/2` the
  stated bound (`Δ`) is even weaker than Theorem 9 (`Δ + δ`). The stated bound is true; it is just not tight to
  its proof. **The proof does not work for `f = n − 1`.** There, the groups of size `n − f − 1` are empty and
  every execution has a single honest party, so agreement gives nothing. This is a proof gap in a degenerate
  case. The hypothesis `n − f ≥ 2` of our stronger bound is necessary. For `n = 3, f = 2`, the 3-party
  protocol above (at `δ = Δ`) commits by `2Δ < 3Δ = ⌊n/(n−f)⌋Δ`; we argue this transfer informally. The
  paper's claim `(n − 1)Δ` for `f = n − 1` does hold for `n = 3`, since it is Theorem 9 with `δ = Δ`
  (`theorem_19_three`). For `n ≥ 4` and `f = n − 1` we only get `⌊n/2⌋Δ`, by monotonicity in `f`; this is
  proved, but not shown tight (`dishonestMajority_lower_bound`, `theorem_19`, `allButOne_lower_bound`).
- **Signatures in the lower-bound executions of Theorem 10.** The paper assumes ideal signatures but never
  checks unforgeability; with it, Executions 2 and 3 of Theorem 10 are not valid executions as written. In
  Execution 1 the Byzantine `C` and `h` behave honestly with value `0` and reach the honest `B` within `δ`. In
  Execution 2 the Byzantine `B` must replay its Execution-1 messages to `g` until about `Δ + 0.5δ`. Those
  messages can relay `C`'s signatures on `0`-messages, which the honest `C` of Execution 2 (holding `1`) never
  produces. Delaying `C → B` and `h → B` in Execution 1 (and the mirror links in Execution 4) fixes it. This is
  a proof gap; the statement is true (`X_authValid`). The replays in Theorems 7 and 9 need truncation in time,
  which is harmless.
- **Lemma 1 (the `Δ + 1.5δ` protocol), part (1).** The proof argues that a conflicting proposal reaching `h` by
  its commit time `t` "stops `h` from committing". Step 4a only checks for equivocation until
  `t_prop + Δ + 0.5d`, which can be earlier than `t`. The lemma is still true by comparing with
  `t_prop + 0.5d`; we check this timing core abstractly (`Lemma1.part1`, `Lemma1.part2`). This is an
  imprecision in the proof.
- Minor: in Theorem 19 the broadcaster's split assigns both values to the middle group (overlapping index
  ranges). Execution 1 of Theorem 10 is described differently in Section 5.4 ("`C` pretends to start late") and
  in Appendix C.4 (modified delays).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Base model.** We use the shared Byzantine message-passing model of CSLib (`Cslib.Byzantine.PartialSync`):
  - discrete time and deterministic state machines;
  - at most `f` static Byzantine parties;
  - the adversary chooses every delivery time;
  - ideal unforgeable signatures as abstract tokens.
  Every lower bound is proved for authenticated protocols and therefore also covers unauthenticated ones.
- **Synchrony.** The protocol knows `Δ` and must be correct in all runs with delays `≤ Δ`. Good-case latency for
  an actual bound `δ` quantifies over runs with delays `≤ δ`. Time is counted with *effective delays*: a message
  received at time `t` is in the state at time `t`, and a reply can leave at `t`. So "commits before `T`" means
  "decided in the state at `T − 1`". Delays are `≥ 1`, which only weakens the adversary. (This `SyncValid f d`
  is the shared library class `Run.SyncValid f (d − 1)` of `Cslib/Computability/Distributed/Byzantine/PartialSync/RunClasses.lean` up to the GST,
  bridge `syncValid_iff`.)
- **Partial synchrony.** We use CSLib's convention: rounds of length `D`, and "within `r` rounds" means the state
  at `rD + 1`. The lower bounds use lock-step executions.
- **Asynchrony.** Asynchronous executions are all runs of the model, i.e. runs with an unknown GST and an unknown
  post-GST delay bound (`asyncRuns f` = library `Run.AsyncValidBounded f`, *bounded* asynchrony; not the
  unbounded class `Run.AsyncValid`). Asynchronous rounds (Appendix A) are not
  formalized: Theorem 4 is stated for lock-step executions, and Theorem 5's latency as "two message delays".
- **Unsynchronized start.** The wrapper `lateStart` gives each party its own start time; nothing reaches a
  correct party before it starts. This constraint also covers time-0 batches, so every correct party starts
  before time `d` (the run's delay bound). Theorem 10 assumes skew `δ/2`, `δ = 2e` even and `δ < Δ`.
- **Byzantine parties "behaving honestly with other delays"** are correct parties of an auxiliary run, made
  Byzantine with `Run.enlarge`.

**Main results in Lean** (namespace `GoodCaseLatencyBB`).

| Paper | Lean | File |
|---|---|---|
| Definitions 2–4, 6–7 | `IsBRB`, `IsBB`, `IsPsyncBB`, `LatencyWithin`, `syncRuns`, `PsyncGoodCaseRounds` | `Basic.lean` |
| Theorem 4 (async BRB: 2 rounds), `n ≥ 3` | `theorem_4` | `SplitBrain.lean` |
| Theorem 5 (2-round-BRB protocol, `n ≥ 3f+1`) | `BRB.theorem_5_brb`, `BRB.theorem_5_latency` | `BRBProtocol.lean` |
| Theorem 6 (psync-BB: 2 rounds) | `theorem_6`, `theorem_6_rounds`, `theorem_6_all` | `SplitBrain.lean`, `PsyncSmall.lean` |
| **Theorem 7** (psync-BB, `n ≤ 5f − 2`: 3 rounds) | `theorem_7`, `theorem_7_all` | `PsyncLowerBound.lean`, `PsyncSmall.lean` |
| Theorem 8 (sync BRB: `2δ`), `n ≥ 3` | `theorem_8` | `SplitBrain.lean` |
| **Theorem 9** (sync BRB, `f ≥ n/3`: `Δ + δ`), `n ≥ 3` | `theorem_9` | `SyncThird.lean` |
| **Theorem 10** (unsync start, `f > n/3`: `Δ + 1.5δ`), `n ≥ 4` | `Thm10.theorem_10` | `UnsyncLowerBound.lean` |
| Claims 1, 2 of the proof of Theorem 10 | `Thm10.claim1`, `Thm10.claim2` | `UnsyncClaim1.lean`, `UnsyncClaim2.lean` |
| Lemma 1 (1)–(2), timing core only | `Lemma1.part1`, `Lemma1.part2` | `Lemma1Core.lean` |
| **Theorem 19** (`f ≥ n/2`), stronger bound | `dishonestMajority_lower_bound`, `theorem_19`, `allButOne_lower_bound` | `DishonestMajority.lean` |
| Counterexamples (`n = 1, 2, 3`); Theorem 10 needs `n ≥ 4` | `theorem_7_false_one`, `theorem_4_false_two`, `theorem_8_false_two`, `ThreeParties.theorem_10_false_three`, `ThreeParties.theorem_10_n4_necessary`, `ThreeParties.three_latency_unsync` | `SmallCases.lean`, `ThreeParties.lean` |
| Theorem 19 for `n = 3, f = 2` | `theorem_19_three` | `DishonestMajority.lean` |

The executions of Theorem 7 are those of the Kuznetsov–Tonkikh–Zhang lower bound (same PODC, same
construction), taken from the library module `Cslib/Computability/Distributed/Byzantine/PartialSync/TwoStepLowerBound.lean` (FastByzantineConsensus still
has its own copy, to be switched to the library).

**Not formalized.** The upper-bound protocols of Figures 3, 5, 6, 9 and 10 (Theorems 11–18) and the BA
primitive they use; Lemma 1 (3); asynchronous rounds; the `O(n/(n−f))Δ` upper bound.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity of the hypotheses:
- the echo protocol solves psync-BB for `f = 0` (`echo_psyncBB_zero`);
- the verified 2-round BRB protocol satisfies the BRB hypotheses of Theorems 4 and 8 for `n ≥ 3f + 1`;
- the hypotheses of Theorems 7, 9, 10 and 19 (BRB/psync-BB with large `f`) are not instantiated here, since
  their protocols (PBFT, Dolev–Strong-based BB, Figures 5–10) are not formalized.

Shared library code used here: run classes (`Cslib/Computability/Distributed/Byzantine/PartialSync/RunClasses.lean`), quiet runs and `DecidesBy`
(`Runs.lean`), gossip of known tokens and token origin (`Gossip.lean`: `Algorithm.Gossips`,
`Run.honestTokens_origin`; the 2-round-BRB protocol and the `n = 3` protocol are instances), the two-step
executions `ρ₁…ρ₅` (`TwoStepLB.lean`), threshold certificates for commit quorums (`Cslib/Computability/Distributed/Byzantine/Certificate.lean`)
and size-bounded labellings of the processes into groups (`Cslib/Foundations/Combinatorics/Labelling.lean`).

Generic tools are in this folder and marked as CSLib candidates:
- replay lemmas `tokens_replay_dl` and `tokens_replay_rel`;
- the `lateStart` wrapper and `Run.st_shift_eq`;
- delayed covering systems `DCover`.
