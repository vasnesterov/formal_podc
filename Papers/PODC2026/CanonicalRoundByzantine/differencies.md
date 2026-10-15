# Differences between the formalization and [AFW26]

## Errors / gaps in the paper

1. **Corollary 10: the proof does not cover `3f < n ≤ 4f`.** Corollary 10 is stated for `n ≤ 5f`, but
   it is derived from Theorem 1 via Algorithm 3 (crusader agreement from `n` consistent broadcasts),
   which is only correct for `n > 4f` (Theorem 9: two sets of `n − 2f` senders must intersect).
   The statement is nevertheless **true for every `n > f ≥ 1`** by a direct argument that the paper's
   introduction hints at: the adversary lets every process hear `n − f` processes other than the
   correct sender in the first `K` rounds (or delivers the sender's messages one round late, for
   communication-closed algorithms); the other processes then have no information about the sender's
   input but validity forces them to accept it. Formalized as `corollary10`,
   `corollary10_commClosed` (`Broadcast.lean`), using only broadcast validity for a correct sender
   and no Byzantine process. Consequently the "sharp boundary at `n = 5f`" does not apply to
   reliable/consistent broadcast: no canonical-round broadcast algorithm has bounded rounds for any
   `n` once `f ≥ 1`.
2. **Theorem 14 needs gather agreement with `i = j`** (an output contains at most one pair per process
   id). With agreement only for distinct correct processes, validity (ii) of crusader agreement fails:
   `Gather.validity_fails_without_self_agreement` (`n = 4`, `f = 1`, an output with two pairs of the
   faulty process). The paper's wording ("a set of distinct (process id, value) pairs", "for any `k`,
   if `pᵢ` and `pⱼ` are correct") is ambiguous; we require it for all correct `i, j` including `i = j`.
3. **"`n ≤ 5f`" literally includes trivial cases where the theorems fail**: for `n = 1`, `f = 1` the single
   process decides its input in round 0 (`literal_theorem1_fails_n1`). The paper's setting is
   `3f < n ≤ 5f`; we prove Theorems 1/7 and Corollaries 6/8 for every `2f ≤ n ≤ 5f`, `f ≥ 1`
   (`thm1_core`, `thm7_core`), and state the paper-facing versions with `3f < n ≤ 5f`.
4. Theorem 7's proof in the paper is a sketch ("see [8]"); it is fully formalized here.

## Generalizations (the formal results are stronger)

5. **General range** `2f ≤ n ≤ 5f` instead of `n = 5f` "for simplicity": groups `|B| = |D| = f`,
   `|A|, |C|, |E| ≤ f` (`Groups`, `Groups.exists`). `|B| = |D| = f` is what makes the other four groups
   send exactly `n − f` messages per round; `A, C, E` may even be empty.
6. **Messages**: a canonical-round algorithm may send *any* function of its history (the paper sends
   the full history and the random number). Larger class of algorithms ⇒ stronger impossibility.
7. **Decisions**: `dec` is applied to every history the process goes through (not only once per
   round); the decision is the first `some` (this models irrevocability). Safety constrains only first
   decisions.
8. **Theorems 1 and 7 hold tape by tape**: the adversary of `α₂` forces round complexity `> K`
   (Theorem 1) or non-termination (Theorem 7) for **every** tape; the expectation (Lemma 5) and the
   probability-`0` statements are immediate corollaries, for every probability measure on tapes
   (not only i.i.d. choices).
9. Safety is required only at finite prefixes of *admissible* executions (the paper: in every
   execution); termination bounds only for admissible adversaries in our (smaller) class. Both make
   the hypotheses weaker, hence the theorems stronger.
10. **Communication closure**: we follow Section 3.2 (round-`r` messages arriving after round `r` are
    discarded; early messages are kept). The introduction says early *and* late messages are discarded;
    our class is larger. Formally: `msg` and `dec` factor through `ccView`.
11. Nontrivial convergence (`ncSpec`) does not require `x₀ ≠ x₁` or `d₀ ≠ d₁`.

## Modelling choices (see README "Model")

12. Processes are `Fin n`. The tape gives one random number per process and round (`ρ p r`, drawn when
    the round-`r` message is sent), matching the canonical-round message format; the paper lets every
    transition use a random number.
13. The adversary is a function of the time and the *current configuration* (histories with all random
    numbers drawn so far, messages sent by Byzantine processes, delivery counters), not of the whole
    prefix. This is non-anticipating by construction; it is a subclass of the paper's adversaries
    (stronger impossibility). Byzantine processes act only through adversary events (`Event.byz`); they
    have no state.
14. Round advancement counts round-`r` messages from `n − f` **distinct** senders (the paper: "`n − f`
    round `r` messages"), applied repeatedly in one atomic step ("cascade"). Messages received before
    wake-up are saved; a process may even "decide" before waking up (round 0) — harmless.
15. Fairness: every correct process eventually wakes up and every link into a correct process is
    served infinitely often (a `deliver` on an empty link is a no-op); this implies the paper's
    "every message sent to a correct process is eventually received". Admissibility requires fairness
    for every tape.
16. **Late processes**: in the paper's `α₀` (resp. `α₁`) the processes of `D` (resp. `B`) do not wake up
    within `K` rounds; we wake them up at time 0 but deliver their messages only after round `K`
    (Theorem 1) or always one round late (Theorem 7, exactly as in the paper). This keeps one uniform
    schedule (`schedule`) and makes fairness immediate.
17. **Random choices of `E`**: in `α₂`, `E` is Byzantine and the adversary cannot observe tape entries
    of Byzantine processes; the simulated copies of `E` use a fixed `r₀`, and `α₀`, `α₁` run on the tape
    `ρE ρ` (rows of `E` constant). The adversary of `α₂` reads the random numbers of the correct
    processes from their histories (`tapeOf`), which is exactly the non-anticipation needed in Lemma 5.
    The adversaries of `α₀`, `α₁` depend on the tape of `α₂` (e.g. `A` replays `α₂`, which involves
    future random numbers of `D`): this is legitimate because safety must hold for every adversary
    and every tape — the paper uses the same fact implicitly.
18. Indistinguishability is proved via one *cover* (`cov`: `A, B, C, D` plus two copies `E₀, E₁` of `E`)
    instead of Lemmas 3 and 4 separately; `clean₂_eq`, `clean₀_eq`, `clean₁_eq` are Lemma 3/4 and the
    corresponding statement for `α₂`.
19. Problem specifications (`Problems.lean`): consensus with strong validity; approximate agreement on
    `ℝ` with validity "between two correct inputs"; approximate agreement on graphs with the geodesic
    convex hull defined via `SimpleGraph.edist` (distance 2 between the distinguished vertices);
    connected consensus requires `R ≥ 1` (for `R = 0` the spec degenerates) and includes the range
    `D` of decisions explicitly.

## Positive side (Section 5) — `Gather.lean`

20. Gather and approximate agreement are black boxes given by their specifications; Algorithm 4 is the
    local computation between the calls (`Run`, `Phase1`, `Phase2`, `decision`). Lines 2, 5, 6 are
    relations ("some `v` appears …" allows any choice); "appears `k` times" is read as "at least `k`".
    Termination is not modelled (it follows trivially from termination of the subroutines).
21. `|Sᵢ| ≥ n − f` (used in Prop. 13) follows from the common core; Lemma 11 holds for any `SC ⊆ Sᵢ`.
    Gather agreement between *different* processes is never used.
22. The paper does not show that decisions lie in `D` (`1 ≤ g ≤ R`); this follows from AA validity
    since the AA inputs are in `{0, R}` (`ceil_y_mem`). Theorem 18 uses `|⌈a⌉ − ⌈b⌉| ≤ 1` for
    `|a − b| ≤ 1` without proof (`abs_ceil_sub_ceil_le`). Lemma 17 needs neither Lemma 16 nor `|F| ≤ f`.
23. Theorem 19 (binding) is formalized abstractly: the execution prefix `α` is represented by a fixed
    common core `SC` of the first gather; "extensions" are all runs satisfying the specs whose correct
    first-gather outputs contain `SC`; one value `v*` (depending only on `SC`) bounds all non-⊥
    branches, for every `R`.
24. Corollary 15 (`GatherLowerBound.lean`): gather is specified at every prefix (agreement, validity,
    and a common core of size `n − f` contained in all outputs returned so far); Algorithm 4 with
    `R = 1` (`caOfGather`, Line 2 made deterministic with a classical choice) has literally the same
    executions; requires two distinct values.

## Not formalized

25. Theorem 9 / Algorithm 3 (superseded by the direct proof of Corollary 10), the real-time complexity
    (Section 2.1, Section 5.3), Remark 1, the Monte-Carlo footnote of Section 6.

## Non-vacuity

26. `Sanity.lean`: for `n > 5f` a deterministic, communication-closed one-round crusader agreement
    algorithm is safe and terminates in round 1 under every admissible adversary
    (`exists_bounded_crusader`); `rrAdv_admissible` exhibits admissible adversaries for every algorithm.
    So the hypotheses of the lower bounds are not contradictory, and the `5f` threshold is sharp for
    crusader agreement. (Its counting: a sender counts for a value if *any* of its round-1 messages in
    the communication-closed view carries it.)
