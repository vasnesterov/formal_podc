# Why Canonical-Round Algorithms Fail for Optimal Byzantine Resilience (PODC 2026)

H. Attiya, I. Flam, J. L. Welch. *Why Canonical-Round Algorithms Fail for Optimal Byzantine
Resilience.* PODC 2026, pp. 197–207, doi:10.1145/3796701.3815948 (full version: arXiv:2510.04310).

## Status

**Complete, sorry-free and axiom-free** (only `propext`, `Classical.choice`, `Quot.sound`; checked with
`#print axioms` on every theorem in the table below). `lake build` of all modules succeeds.

Formalized: Theorem 1, Corollary 6, Theorem 7, Corollary 8 (the core lemmas `thm1_core`/`thm7_core` hold for every `2f ≤ n ≤ 5f`, `f ≥ 1`; the paper-facing statements assume
the paper's `3f < n ≤ 5f`), the Section 3.3 consequences (consensus, approximate agreement on
`ℝ` and on graphs, connected consensus / crusader agreement / gradecast), Corollary 10 (for every
`n > f ≥ 1`, with a direct proof), Corollary 15 (gather), and the positive side: Lemma 11,
Propositions 12–13, Theorem 14, Lemmas 16–17, Theorem 18 and Theorem 19 (gather and approximate
agreement as abstract specifications). Non-vacuity: for `n > 5f` a one-round communication-closed
crusader agreement algorithm is verified in the same model.

Not formalized: Theorem 9 / Algorithm 3 (not needed: Corollary 10 is proved directly), the real-time
complexity, Section 5.3 (comparison) and the Monte-Carlo footnote.

Main findings (details in `differencies.md`):
* The lower bounds are correct; the proof generalizes from `n = 5f` to `2f ≤ n ≤ 5f` with
  `|B| = |D| = f`, `|A|, |C|, |E| ≤ f`. The literal statement "`n ≤ 5f`" fails for `n = 1`.
* **Corollary 10's proof covers only `4f < n ≤ 5f`** (Algorithm 3 needs `n > 4f`, Theorem 9), although
  it is claimed for `n ≤ 5f`. The statement is true for every `n > f ≥ 1` by a direct argument (the
  correct sender is never heard), which we formalize; so the `5f` threshold is irrelevant for broadcast.
* Theorem 14 needs gather agreement also for `i = j` (at most one pair per process id in an output);
  without it validity fails (Lean counterexample `Gather.validity_fails_without_self_agreement`).
* Stronger forms: the adversary of Theorem 1 forces round complexity `> K` for **every** random tape
  (not just in expectation), and Theorem 7's adversary prevents termination for every tape.

## Model (stated explicitly; Lean: `Cslib/Computability/Distributed/Byzantine/CanonicalRounds/Model.lean`)

* Asynchronous message passing, `n` processes `Fin n`, static Byzantine faulty set of size `≤ f`
  chosen by the adversary. Reliable FIFO links. Each correct process wakes up once (adversary event);
  messages arriving before wake-up are saved.
* **Canonical-round algorithm** (`CanonAlg`): the history of a process is the sequence of received
  messages and drawn random numbers (input kept separately). The process sends its round-`r`
  message to all at wake-up (`r = 1`) and as soon as it holds round-`r'` messages from `n − f`
  distinct senders, `r'` its current round (applied repeatedly). A message is `(r, msg p v h)` with
  `h` the history ending with the fresh random number — **any** function of the history (the paper
  sends the full history; ours is a superset of algorithms, so impossibilities are stronger). The
  decision function `dec` is applied to every history; the first `some` is the decision (irrevocable).
* Randomness: tape `ρ p r` (random number of `p` at the start of its round `r`), with an arbitrary
  probability measure `μ` on tapes; deterministic algorithms = any fixed tape (e.g. `R = Unit`).
* Adversary: a static faulty set and a function of time and the **current configuration** (all
  histories, hence all random numbers drawn so far, Byzantine messages, delivery counters): full
  information, adaptive, non-anticipating by construction. Byzantine processes send arbitrary messages
  with arbitrary round labels (`Event.byz`).
* Admissible adversary: `≤ f` faults and, for every tape, every correct process wakes up and every
  link into a correct process is served infinitely often.
* Problems are `Spec`s on (inputs, faulty set, decisions so far); `Safe f S`: `S` holds at every
  prefix of every admissible execution, for every tape. Round complexity `rounds` (`ℕ∞`): smallest `r`
  such that every correct process decides at a history of round `≤ r`; `expRounds` = `∫⁻` over `μ`.
* Communication-closed (`CommClosed`): `msg` and `dec` factor through `ccView`, which drops round-`r`
  messages received in a round later than `r` (Section 3.2).

## Main theorems ↔ Lean (namespace `Podc2026.CanonicalRound`)

| Paper | Lean | File |
|---|---|---|
| Nontrivial convergence (Sec. 2.2) and its instances | `ncSpec`, `consensus_nc`, `approx_nc`, `graphApprox_nc`, `connectedConsensus_nc` | `Problems.lean` |
| Executions `α₀, α₁, α₂`, Lemmas 3, 4 | `cov`, `clean₂_eq`, `clean₀_eq`, `clean₁_eq`, `log₂`, `log₀`, `log₁` | `Cover.lean`, `LowerBound.lean` |
| Lemma 5 (+ the final contradiction) | `thm1_core` (for every tape), `key_contra` | `LowerBound.lean` |
| **Theorem 1** | `theorem1`, `theorem1_unbounded` | `Main.lean` |
| **Corollary 6** | `corollary6` | `Main.lean` |
| **Theorem 7** | `theorem7` (core: `thm7_core`) | `Main.lean`, `LowerBound.lean` |
| **Corollary 8** | `corollary8` | `Main.lean` |
| Section 3.3 | `consensus_unbounded`, `consensus_not_commClosed`, `approx_unbounded`, `graphApprox_unbounded`, `connectedConsensus_unbounded`, `connectedConsensus_not_commClosed` | `Main.lean` |
| **Corollary 10** (all `n > f ≥ 1`) | `corollary10`, `corollary10_commClosed` | `Broadcast.lean` |
| **Corollary 15** | `corollary15`, `corollary15_commClosed` (via `caOfGather`, `safe_caOfGather`) | `GatherLowerBound.lean` |
| Lemma 11, Prop. 12, Prop. 13 | `Gather.lemma11`, `Gather.prop12` (`heavy_unique`), `Gather.prop13` | `Gather.lean` |
| **Theorem 14** | `Gather.theorem14` | `Gather.lean` |
| Lemmas 16, 17, **Theorem 18** | `Gather.lemma16`, `Gather.lemma17`, `Gather.theorem18` | `Gather.lean` |
| **Theorem 19** (binding) | `Gather.theorem19`, `Gather.branch_heavy_in_core` | `Gather.lean` |
| Literal "`n ≤ 5f`" fails for `n = 1` | `literal_theorem1_fails_n1` | `Main.lean` |
| Counterexample (gather agreement with `i = j`) | `Gather.validity_fails_without_self_agreement` | `Gather.lean` |
| Non-vacuity / sharpness (`n > 5f`) | `exists_bounded_crusader`, `caAlg_safe`, `caAlg_rounds`, `caAlg_expRounds`, `caAlg_commClosed`, `rrAdv_admissible` | `Sanity.lean`, `Cslib/Computability/Distributed/Byzantine/CanonicalRounds/Liveness.lean` |

## Infrastructure (`Cslib/Computability/Distributed/Byzantine/CanonicalRounds/`, now in CSLib)

* `Model.lean`: the model above.
* `Lemmas.lean`: rounds, outboxes, cascade, monotonicity of executions, `DrawsOK` (draws come from the tape).
* `Liveness.lean` (subagent): well-formedness, FIFO invariant, eventual delivery under fairness,
  round-robin admissible adversary `rrAdv`, `rounds`/`expRounds` bounds.
* `Schedule.lean`: **clean schedules** (`schedule F hear bm lateFrom`): every correct process hears a
  fixed set of `n − f` processes per round, other messages are delayed until stage `lateFrom` and then
  delivered late; Byzantine messages computed from the configuration. `stageInv_exec`: the views
  (`id` or `ccView`) of the histories after stage `r` are the round-level histories `clean`.
  `schedule_admissible`. This turns any "processes in `X` receive the round-`r` messages of `Y`"
  indistinguishability argument into a recursion on lists.

Other CSLib candidates: the counting lemmas in `Gather.lean` (`cnt_mono`, `heavy_unique`,
`exists_not_mem_of_cnt`, `cnt_ge_of_functional`, `abs_ceil_sub_ceil_le`), `Decisions.ccView_idem`,
`Decisions.findSome_inits_ccView`, `findSome?_map_map`.

## Token spend

Roughly 0.75M tokens (paper agent ≈ 0.5M, two subagents ≈ 0.25M).
