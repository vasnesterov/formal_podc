# Revisiting Optimal Resilience of Fast Byzantine Consensus (PODC 2021)

Petr Kuznetsov, Andrei Tonkikh, Yan X Zhang. *Revisiting Optimal Resilience of Fast Byzantine Consensus.*
PODC 2021, pp. 343–353, DOI 10.1145/3465084.3467924; extended version arXiv:2102.12825v3 (the version formalized;
numbering follows it).

## Status

**Complete, no `sorry`, no axioms** (main theorems checked with `lean_verify`: only `propext`, `Classical.choice`,
`Quot.sound`). Headline result, `Impl.tight_bound` (`ImplMain.lean`): in the authenticated partially synchronous
model, for `1 ≤ t ≤ f`, `δ ≥ 2`, `n ≥ 2` and ≥ 2 values, **an `f`-resilient `t`-two-step consensus protocol exists
iff `n ≥ 3f + 2t − 1`** (so `5f − 1` for `t = f`).

- Lower bound (Section 4): Theorem 4.5 and Lemmas 4.1–4.4, for every `2 ≤ n ≤ 3f + 2t − 2` (incl. the case `t ≤ 1`
  via the classic `3f + 1` bound, proved from the PODC 2023 *Validity of Consensus* formalization). The paper's
  statement fails in the degenerate case `f = 1, t = 0` (`n = 1`, outside the paper's intended scope) — Lean counterexample.
- Protocol (Section 3 + Appendix A), two levels:
  1. abstract transition system (asynchronous, ideal signatures): consistency, Theorems 3.6 / A.4 with Lemmas
     3.1–3.5, A.1–A.2, Corollary A.3, for `n ≥ 3f + 2t − 1`;
  2. concrete algorithm in the PSync model (gossip of signed tokens, clock-driven views of length `6δ + 12`,
     rotating leader): unforgeability, refinement into level 1 (hence agreement), weak validity, **the two-step
     property claimed in Section 4.1**, and **termination** (liveness) — i.e. it is a `FastConsensus`.
  One genuine gap in the paper's safety proof (votes from "future" views; not a protocol bug) and one imprecision
  (when commit certificates are collected) are fixed by explicit protocol rules.
- Not formalized: Sections 4.3 (suspect sets) and 4.4 (disjoint proposers/acceptors); extended validity.

**Scope caveats.** (i) The lower bound `no_fastConsensus_of_le` is stated for all `δ ≥ 1`, but for `δ = 1` the Lean
two-step notion is strictly stronger than the paper's (a reply to a message received at `δ` leaves at `δ + 1 = 2δ`),
so it is the paper's notion only for `δ ≥ 2`; the headline `tight_bound` assumes `δ ≥ 2`. (ii) The Lean two-step notion
fixes one execution with batch delivery (simultaneous deliveries processed atomically), whereas the paper allows any
valid ordering of simultaneous events; so the lower bound covers a slightly smaller protocol class
(`differencies.md` §2.3). (iii) The positive side (liveness, two-step) is proved in the drift-free,
synchronized-clock PSync model, where no view synchronizer is needed — friendlier than the paper's protocol
section; the lower bound uses the same model (as does the paper's).

See `differencies.md` for all deviations.

## Model (explicit)

**Lower bound** — shared model `Cslib/Computability/Distributed/Byzantine/PartialSync/`:
- `n = Fintype.card P` processes, deterministic state machines, at most `f` Byzantine (static, arbitrary behaviour),
  authenticated point-to-point links, **ideal unforgeable signatures** (`Auth`; unauthenticated = `Auth.none`).
- **Partial synchrony**: discrete time, unknown per-run GST, correct-to-correct messages sent at `τ` delivered in
  `[τ, max τ gst + δ]`; `δ = Δ > 0` known. Correct processes step every tick from time 0 (synchronized clocks).
- Consensus with **weak validity** (`weakValidity`), termination, agreement in every valid unforgeable run.
- **`t`-two-step** (`TwoStep`): for all inputs `I` and all `T` with `|T| = t`, in the `T`-faulty two-step execution
  `tsRun A δ I T` (rounds of length `δ`, every message delivered at the next round boundary, `T` Byzantine:
  correct in round 1, silent afterwards, `gst = 0`) every correct process decides by time `2δ` (state at `2δ+1`).
  `FastConsensus A Au f t δ` = both.

**Protocol, concrete** — `Implementation.lean`: an `Algorithm` of the PSync model with `auth` (messages are signed
tokens); every process gossips its whole token set each step; view `v` = time interval `[vL, (v+1)L)` (perfectly
synchronized clocks of the model, `L = 6δ + 12`); `δ ≥ 2` for the two-step property (a reply to a message received at
`δ` leaves at `δ + 1`, which must be before `2δ`).

**Protocol, abstract** — `Protocol.lean`: asynchronous interleaving transition system; global set of emitted tokens
(signed statements), local states of correct processes, Byzantine processes emit any self-signed token; arbitrary
leader map and view changes (synchronizer abstracted). Decisions = quorums of `ack` (fast, `n − t`) or `commit`
(slow, `⌈(n+f+1)/2⌉`) tokens.

## Main results ↔ Lean (namespace `FastByzantineConsensus`)

| Paper | Lean | File |
|---|---|---|
| §2.2 weak validity; §4.1 `T`-faulty two-step execution, `t`-two-step | `weakValidity`, `tsRun`, `DecidesBy`, `TwoStep`, `FastConsensus` | `TwoStep.lean` |
| Lemma 4.1 (round-1 actions depend only on inputs) | `Cslib.Byzantine.PartialSync.templateRun_st_early`, `templateRun_out_early`, `templateRun_inbox_early`, `templateRun_st_eq_early` | `Cslib/Computability/Distributed/Byzantine/PartialSync/RoundOne.lean` |
| Lemma 4.2 (similar ⇒ same decision) | `Cslib.Byzantine.PartialSync.Run.st_eq_of_inbox_eq` (used inline) | `Cslib/Computability/Distributed/Byzantine/PartialSync/Model.lean` |
| consensus value `c(ρ)` well defined | `tsRun_agree` | `Influential.lean` |
| Lemma 4.3 | `lemma_4_3` | `Influential.lean` |
| influential process, Lemma 4.4 | `Influential`, `exists_influential` | `Influential.lean` |
| Executions `ρ₁…ρ₅` (Figs. 2–4), `ρ₄ ∼_{P₃} ρ₅`, `ρ₄ ∼_{P₁} ρ₃` (and mirror for `ρ₂`) | `rho4`, `rho3`, `rho4_st_eq_rho5_P3`, `rho4_st_eq_rho3`, `rho4_valid`, `rho4_authValid`, `decision_eq_rho4` | `Executions.lean` |
| **Theorem 4.5** | `theorem_4_5` (`n = 3f+2t−2 ≥ 2`), general `no_fastConsensus_of_le` (`2 ≤ n ≤ 3f+2t−2`), `theorem_4_5_tight` (`t = f`, `n ≤ 5f−2`), `theorem_4_5_noAuth` | `LowerBound.lean` |
| case `t ≤ 1` / classic `3f+1` bound (cited [7] in the paper) | `not_solves_of_le_three_mul` | `SmallCases.lean` |
| counterexample `f = 1, t = 0` (not in the paper) | `single_fastConsensus`, `theorem_4_5_fails_f1_t0` | `SmallCases.lean` |
| sanity: `FastConsensus` satisfiable (`f = t = 0`, leader echo) | `leaderEcho_fastConsensus` | `NonVacuity.lean` |
| §3.1–3.2, App. A.1–A.2: the protocol | `Protocol.Tok`, `Certified`, `HasCC`, `DecidedIn`, `ValidBallot`, `ValidCC`, `ValidVotes`, `Selects`, `Step`, `Reachable` | `Protocol.lean` |
| invariants of reachable states | `Protocol.TokInv`, `Protocol.Inv`, `Inv.of_reachable` | `ProtocolInvariants.lean` |
| QI1–QI3 | `exists_correct_inter`, `card_add_one_le_card_sdiff_add` | `ProtocolSafety.lean` |
| Lemma 3.1 / 3.2 / 3.3 / 3.4 / 3.5 | `not_all_nil_of_decided` / `decided_view_le` / `safe_of_single` / `safe_of_many_votes` / `not_decided_of_few_votes` | `ProtocolSafety.lean` |
| Lemma A.1 / A.2 / Corollary A.3 | `certified_of_hasCC`, `certified_of_decided` / `hasCC_decided_eq` / `decidedIn_unique` | `ProtocolSafety.lean` |
| induction "certified ⇒ safe" | `safe_of_selects`, `safe_of_certified` | `ProtocolSafety.lean` |
| **Theorem A.4** / **Theorem 3.6** | `Protocol.consistency` / `Protocol.consistency_five_f` | `ProtocolSafety.lean` |
| the protocol as a PSync algorithm (views by clock, gossip) | `Impl.algo`, `Impl.auth`, `Impl.absState` | `Implementation.lean` |
| unforgeability; refinement into the transition system; consistency (Thm A.4) in the timed model | `Impl.algo_unforging`, `Impl.reachable_absState`, `Impl.algo_agreement` | `ImplSafety.lean` |
| weak validity; "the protocol of Section 3 is `t`-two-step" (§4.1) | `Impl.algo_validity`, `Impl.algo_twoStep` | `ImplTwoStep.lean` |
| liveness ("once a correct leader is elected after GST …", §3.3, A.3) | `Impl.algo_termination` (gossip lemma, timeline lemmas in `ImplLivenessAux.lean`) | `ImplLiveness.lean` |
| **`f`-resilient `t`-two-step consensus for `n ≥ 3f+2t−1`** | `Impl.algo_fastConsensus` | `ImplMain.lean` |
| **tightness of `3f + 2t − 1`** (abstract + Thm 4.5) | `Impl.tight_bound` | `ImplMain.lean` |

## Infrastructure built

- `Cslib/Computability/Distributed/Byzantine/PartialSync/RoundOne.lean` (new, reusable for good-case-latency lower bounds): `quiet` (state without
  receptions), `nextRound` (round boundaries), `round1`, `templateRun` (Byzantine processes behave correctly in
  round 1 with a per-receiver input, arbitrarily later), `RoundSched`, the round-1 lemmas, `silentRun`,
  `quiet_tokens`/`round1_tokens` (a process that received nothing emits only its own signatures).
- Proof pattern for multi-execution indistinguishability chains in PSync with signatures (label processes by a
  function `g : P → ℕ`, prove one "side" lemma and get the mirror image by relabelling `i ↦ 6 − i`).

## CSLib candidates

- Done: the PSync model and `RoundOne.lean` moved to CSLib (`Cslib/Computability/Distributed/Byzantine/PartialSync/`,
  namespace `Cslib.Byzantine.PartialSync`, same declaration names; vasnesterov/cslib PRs #26, #30).
- Counting lemmas `card_add_card_le_card_inter_add`, `exists_correct_inter` (`ProtocolSafety.lean`): generic
  quorum-intersection facts.

## Token spend

Rough estimate: main agent ≈ 0.45M; subagents ≈ 1.0M (protocol safety ≈ 0.15M, refinement ≈ 0.25M,
Lemmas 4.3/4.4 + small cases ≈ 0.08M, two-step + validity ≈ 0.11M, termination ≈ 0.2M, plus context overhead).
Total ≈ 1.5M of the 10M budget.
