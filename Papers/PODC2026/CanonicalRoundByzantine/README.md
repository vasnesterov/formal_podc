# Canonical-round algorithms and optimal Byzantine resilience — PODC 2026

Hagit Attiya, Itay Flam, Jennifer L. Welch. *Why Canonical-Round Algorithms Fail for Optimal Byzantine
Resilience.* PODC 2026. DOI [10.1145/3796701.3815948](https://doi.org/10.1145/3796701.3815948). Formalized
version: full version, arXiv [2510.04310](https://arxiv.org/abs/2510.04310).

**Verdict: ⚠️ Correct with fixes.** The lower bounds (Theorems 1 and 7, Corollaries 6 and 8, and their Section 3.3
and Corollary 15 consequences) are proved, for the whole range `2f ≤ n ≤ 5f` rather than only `n = 5f`.
Corollary 10 (broadcast) is true, but the paper's proof covers only `4f < n ≤ 5f`. Theorem 14 needs a gather
property the paper does not state. The positive results of Section 5 are proved.

## Mistakes in the paper

1. **Corollary 10: the proof covers only part of the claimed range (statement true).** Corollary 10 claims that
   reliable/consistent broadcast has unbounded round complexity for canonical-round algorithms with `n ≤ 5f`. The
   proof goes through Algorithm 3 (crusader agreement from `n` consistent broadcasts), which is correct only for
   `n > 4f` (Theorem 9 needs two sets of `n − 2f` senders to intersect). So the proof says nothing about
   `3f < n ≤ 4f`. The statement holds for every `n > f ≥ 1` by a direct argument, which the introduction hints
   at: in the first `K` rounds, let every process hear `n − f` processes other than the correct sender (for
   communication-closed algorithms, deliver the sender's messages one round late). The others then have no
   information about the sender's input, yet validity forces them to deliver it. In particular, the "sharp
   boundary at `5f`" is irrelevant for broadcast (`corollary10`, `corollary10_commClosed`).
2. **Theorem 14 needs gather agreement also for `i = j` (unstated hypothesis).** Crusader agreement from gather
   (Algorithm 4) requires that an output contains at most one pair per process id. If agreement is only
   required between distinct correct processes, validity (ii) fails. Instance: `n = 4`, `f = 1`, a correct
   output with two different pairs of the faulty process. The paper's wording ("a set of distinct (process id,
   value) pairs") is ambiguous; we require it for all correct `i, j`, including `i = j`
   (`Gather.validity_fails_without_self_agreement`).
3. **"`n ≤ 5f`" literally includes trivial cases (false in a degenerate case).** For `n = 1`, `f = 1` the single
   process decides its input in round 0, so Theorem 1 and Corollary 6 as literally stated fail. The paper's
   setting is `3f < n ≤ 5f`. Our proof needs only `2f ≤ n` (`literal_theorem1_fails_n1`).
4. **Minor.** Theorem 7's proof is only a sketch ("see [8]"); it is fully formalized here. The introduction
   defines communication closure as discarding early *and* late messages, while Section 3.2 discards only late
   ones; we follow Section 3.2. Theorem 18 uses `|⌈a⌉ − ⌈b⌉| ≤ 1` for `|a − b| ≤ 1` without proof, and the
   paper does not show that decisions lie in `{1, …, R}` (both proved).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib, `Cslib/Computability/Distributed/Byzantine/CanonicalRounds/`).
- Asynchronous message passing, `n` processes, reliable FIFO links, static Byzantine faulty set of size `≤ f`.
  Byzantine processes send arbitrary messages with arbitrary round labels.
- A canonical-round algorithm sends its round-`r` message to all and advances once it holds round-`r` messages
  from `n − f` distinct senders. Each message may be *any* function of the history; the paper sends the full
  history. A larger class of algorithms makes the impossibilities stronger. The first `some` of the decision
  function is the irrevocable decision.
- Randomness: a tape with one random number per process and round, under an arbitrary probability measure.
  Deterministic algorithms correspond to a fixed tape.
- The adversary is full-information and adaptive: a function of time and the current configuration, including
  all random numbers drawn so far. It is non-anticipating by construction, a subclass of the paper's adversaries,
  so the impossibilities are again stronger. Admissible means at most `f` faults, every correct process wakes up,
  and every link into a correct process is served infinitely often.
- Safety is required at every prefix of every admissible execution, for every tape. Round complexity is the
  smallest round by which all correct processes decide; the expected value is the integral over the tape measure.
- Communication-closed (`CommClosed`): messages and decisions factor through a view that drops late messages.
- The adversary of Theorems 1 and 7 works tape by tape: it forces round complexity `> K` (resp. non-termination)
  for every tape, not just in expectation.

**Main results in Lean** (namespace `Podc2026.CanonicalRound`; paper-facing statements assume `3f < n ≤ 5f`, cores
`thm1_core`/`thm7_core` hold for `2f ≤ n ≤ 5f`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (expected rounds `> K` for every `K`); Corollary 6 | `theorem1`, `theorem1_unbounded`; `corollary6` | `Main.lean` |
| Theorem 7 (comm.-closed: termination probability 0); Corollary 8 | `theorem7`; `corollary8` | `Main.lean` |
| Section 3.3 (consensus, approximate agreement on `ℝ`/graphs, connected consensus) | `consensus_unbounded`, `approx_unbounded`, `graphApprox_unbounded`, `connectedConsensus_unbounded` | `Main.lean` |
| Corollary 10 (every `n > f ≥ 1`) | `corollary10`, `corollary10_commClosed` | `Broadcast.lean` |
| Corollary 15 (gather) | `corollary15` | `GatherLowerBound.lean` |
| Lemma 11, Propositions 12–13, Theorem 14 | `Gather.lemma11`, `Gather.prop12`, `Gather.prop13`, `Gather.theorem14` | `Gather.lean` |
| Theorem 18, Theorem 19 (binding) | `Gather.theorem18`, `Gather.theorem19` | `Gather.lean` |

**Not formalized.** Theorem 9 / Algorithm 3 (superseded by the direct proof of Corollary 10), real-time
complexity, the comparison of Section 5.3, the Monte-Carlo footnote. In Section 5, gather and approximate agreement
are black boxes given by their specifications, and termination is not modelled.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: for `n > 5f` a deterministic, communication-closed one-round crusader agreement algorithm is verified
safe and terminating in the same model (`exists_bounded_crusader`), so the lower bounds' hypotheses are
satisfiable and the `5f` threshold is sharp for crusader agreement.
