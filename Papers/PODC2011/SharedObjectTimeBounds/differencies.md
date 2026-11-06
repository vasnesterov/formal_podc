# Differences between the formalization and the thesis

Source: J. Wang, *Time Bounds for Shared Objects in Partially Synchronous Systems*, MS thesis, Texas A&M,
December 2011 (advisor J. L. Welch), the full version of the PODC 2011 brief announcement of Wang, Welch and Lee.
Numbering follows the thesis. Formalized: Theorems C.1, D.1 and E.1 of Chapter IV (lower bounds) with the
definitions of Chapter II and the model of Chapter III. Not formalized: Chapter V (Algorithm 1, Theorems C.18,
D.1, D.2 of Chapter V) and the tables of Chapter VI, except the claims checked in `Examples.lean`.

## Model

1. **Algorithms.** The thesis models a process as a state machine with timers and a run as a set of timed views
   (§III.B). We model the local behaviour of a process as a *causal function* from its timed input events
   (invocations, receipts) to its timed output events (responses, sends), in local clock time
   (`Cslib.TimedMP.Algorithm`): outputs up to clock time `τ` depend only on inputs up to `τ`, and there is no
   output without input (views start quiescent). Every deterministic automaton of the thesis whose runs are not
   Zeno induces such a function (messages can be tagged with sequence numbers, since we treat outputs as sets),
   so the lower bounds apply to all such automata. Zeno automata (timers accumulating at a finite time) have no
   complete run with an invocation at all; for them the thesis's correctness condition is vacuous and its
   Claim B.2 ("every finite admissible run has a complete admissible extension") is false. We exclude them by the
   choice of the model (✏️: the thesis evidently intends non-Zeno algorithms).
2. **Runs.** A run of a scenario (offsets, invocation times, delays as a function of sender, receiver and real
   send time) is the fixpoint of "invocations ∪ receipts of sent messages" (`IsRun`). It exists and is unique
   when delays are bounded below by some `γ > 0` (`exists_run`, `IsRun.unique`). Delays depending only on the send
   time (not on the message) restrict the adversary; all runs of the proofs are of this kind, and correctness is
   only *assumed* for admissible scenarios, so this makes our hypotheses weaker and the theorems stronger.
3. **Simultaneous events.** The thesis requires strictly increasing clock times in a view, which makes the run
   `R₁` of Theorem C.1 impossible (two messages arrive at `p_k` at the same time `t + d`). Our histories are sets of
   timed events, so simultaneous events are allowed.
4. **Shift, chop, extend, append** (Claims B.1–B.4, Lemma B.1, Corollary B.4): shifting is `Scenario.shift`
   with the same local histories (`IsRun.shift`); chopping and extending is replaced by running another scenario
   that agrees with the shifted one before a causally closed cut (`agree_of_cut`, `agree_window`); appending to an
   initialized run is `restart` (Setup.lean), which uses history-obliviousness.
5. **Assumptions of §III.B.4.** Bounded-time operations: `TimeBound A d u ε (fun _ => True) Bop`. Bounded
   quiescence: only its consequence "every admissible well-formed run is finite" (`FiniteRuns`), weaker than the
   thesis's. History-obliviousness: `HistoryOblivious`: after two runs in which the same process alone executes the
   same operations (arguments and return values), every process has the same residual behaviour
   (`SameResidual`) — for a state machine this is "same final state".
6. **The application.** Invocation times are fixed in the scenario; "invoked immediately after the previous
   response" is realized by computing the response time in an auxiliary run. `WF` requires each operation to
   respond strictly before the next invocation of its process; correctness, time bounds etc. are assumed only for
   well-formed admissible runs. The `ρ`-phase invokes the operations of `ρ` at times `0, g, 2g, …` with `g > Bop`
   instead of "immediately after the previous response".
7. **Linearizability** uses the strict real-time order "response < invocation" (an operation invoked at the very
   instant another responds may be ordered either way). This weakens the correctness hypothesis. Consequently the
   proofs insert a small gap `η > 0` where the thesis invokes "immediately after" a response (Theorem E.1).
8. **Sequential specification**: a predicate `legal` on finite sequences of `(argument, return value)`;
   deterministic (Definition A.1) and prefix closed (implicit in the thesis, standard).
9. **Time bounds.** `|OP| ≥ X` is formalized as: if every operation of type `OP` responds within `B` in every
   admissible well-formed run, then `B ≥ X` (the thesis's `|OP|` is the supremum of these times).

## Definitions (Chapter II)

10. **Definitions D.1, D.4 (mutator, pure accessor).** Literally no operation type is a pure accessor
    (`not_pureAccessor`), so Theorem E.1 would be vacuous. We use the intended notion `NonMutator` (for every
    legal `ρ ∘ op`, `ρ ∘ op` is equivalent to `ρ`). ✏️ (evident intent). Only the non-mutator part is used
    in Theorem E.1; the accessor part is dropped (the theorem is stated for every non-mutator `AOP`).
11. "Immediately self-commuting" is the negation of Definition B.2 (as stated in the thesis's note).

## Theorem C.1

12. Statement as in the thesis, for `n ≥ 2` instead of `n ≥ 3` (the proof never needs a third process), with
    hypotheses `0 < d`, `0 ≤ u`, `0 ≤ ε`. `u ≤ d` is not needed.
13. Proof as in the thesis. The `ρ`-phase of every run is a fresh admissible run glued by `restart`
    (history-obliviousness), as in §IV.B.2; when `2m > u` this is necessary, since the cumulative relative shift
    of `p_i` and `p_j` is `2m`. The cuts are `C_i = t + d - m`, `C_j = t + 2d - 2m`, others `t + 2d - m` in Step 2,
    and `C_j = t + d - m`, `C_i = C_k = t + 2d - m` in Step 3; all window and cut conditions were checked channel
    by channel (`step2_agree`, `step3_agree`). Every shifted delay is admissible except the one the proof
    removes.
14. Slip: Step 2 says "letting messages from `p_j` to `p_k` cost `δ = d - m`"; it should be `p_j` to `p_i`.

## Theorem D.1 (Chapter IV)

15. **Missing hypothesis `ε ≥ (1 - 1/k) u`.** The shifted run `R₂` has clock skew `(1 - 1/k) u`; the proof
    justifies admissibility by "the optimal `ε` is `(1 - 1/n) u`", i.e. it assumes clocks synchronized no better
    than optimally. The statement only says "`ε`-bounded clocks". Without the hypothesis the bound is not
    established, and it is contradicted by the thesis's own Algorithm 1, whose pure mutators respond after
    `ε + X` with `X = 0` allowed (Chapter V, not formalized; its correctness proof does not seem to need the optimal
    `ε`). ✏️: the assumption holds wherever the thesis uses the theorem and is stated in its proof. The thesis
    treats `ε` as a free parameter in Theorems C.1 and E.1, but its Chapters IV–V consistently
    take `ε` to be the optimal achievable skew (`ε ≥ (1 - 1/n) u` by Lundelius–Lynch), so a reader of the thesis
    would assume it; the refutation for smaller `ε` (Algorithm 1) is not formalized.
16. **Proof gap, Step 1.1.** "There exists a legal permutation `π` of the `k` operations in `R₁` such that for
    any `ρ*` with `ρ ∘ π ∘ ρ*` legal, the operations of `ρ*` invoked later return as in `ρ*`" does not follow from
    correctness and determinism: correctness gives a linearization per extension of the run, and an algorithm may
    fix the order of concurrent mutators lazily, depending on later operations. Without it, the runs of the proof
    only show that, for every later query sequence, the answers are compatible with some permutation whose last
    element is not `z`, for every `z` — which is no contradiction: for the test-and-reset register (`TR`,
    `Examples.lean`), whose writes satisfy the theorem's hypothesis (`tr_nonEquiv`), every query sequence has such
    answers (`tr_answers`). We prove the theorem under the stronger hypothesis `LastRevealing` (one fixed query
    sequence whose answers determine the last operation), which holds for writes
    (`write_lastRevealing`) and, by the same argument (not formalized), for push and enqueue, and for `k = 2` under the thesis's own hypothesis (`theorem_D1_two`). Whether
    Theorem D.1 holds in its stated generality is open (we have neither a proof nor a counterexample algorithm).
    Precision: in `R₂^z` the real-time order puts `op_z` before `op_{z+1 mod k}`, and only that pair when
    `|OP| > (1 - 2/k) u`; for smaller `|OP|` the order of `R₂^z` is stricter and the runs do give a contradiction for
    `TR` (all writes ordered, last `= z + 1` for every `z`). So the gap concerns `|OP| ∈ ((1 - 2/k) u, (1 - 1/k) u)`;
    `tr_answers` only records "last ≠ z", which suffices because `TR`'s state after the writes depends only on the
    last write. ⚠️: Theorem D.1 is one of the three results the abstract presents as main contributions; it holds
    only with the new hypothesis, and it is not refuted in general.
17. Slip: the shift is written `x_i = [-(k-1)/2 + ((z-i) mod k)/k] u`; it must be `-(k-1)/(2k)` (Step 2.2 and the
    skew computation use `(k-1)/(2k)`).
18. The thesis requires the `k` instances to be distinct; not needed. `ρ` executed by `p_0`, the queries `α` by
    `p_0` after all `op_i` responded; the shift is normalised so that `p_0` does not move.
19. Statement of `theorem_D1` additionally assumes `u ≤ d` (delays `d - u ≥ 0`) and `0 < d`.

## Theorem E.1

20. "One of the below is legal while the other one is illegal" is `¬ (_ ↔ _)`. `AOP` is assumed to be a
    non-mutator (item 10), `OP` immediately self-commuting; `n ≥ 3`.
21. Proof as in the thesis (runs `R₁`, `R₂` = shift of `p_j` by `+m`, chopped at `C_i = t + d - m`,
    `C_j = t + 2d - 2m`, others `t + 2d - m`, extended with delay `d` on `j → i`; `R₂⁻` without `p_j`'s operations),
    with these changes: (a) **gap**: the proof gets "both `ρ ∘ op₁ ∘ op₂` and `ρ ∘ op₂ ∘ op₁` legal" from immediate
    self-commutativity, which needs `ρ ∘ op₁` and `ρ ∘ op₂` legal, while hypothesis C gives only one of them; repaired
    by running each operation alone after `ρ` (correctness yields a legal return, determinism identifies it), 🔧;
    (b) the accessors are invoked at fixed times `τ = t + B₁ + η`, `τ + m` (`η = (d + m - B₁ - B₂)/4`) instead of
    "at `t_max`" and the adaptive time `max{min{t_max, t+d-m}, t+|op''₁|}`; then the case analysis of Step 2.2a is
    unnecessary, and the strict real-time order holds; (c) `B₁, B₂ ≥ 0` are derived from runs. The second case of
    Step 1 (Remark 2) is the same core lemma with `i ↔ j`, `op₁ ↔ op₂`, A ↔ B (`E1.core`).
22. Slip: "Since `aop'_1` and `aop'_2` are pure mutators" — pure accessors.

## Claims about specific objects (Chapters II, IV.E, VI)

23. Read-modify-write is strongly immediately non-self-commuting (`rmw_strongly`); the writes of a register
    satisfy the hypotheses of Theorem D.1 including `LastRevealing` (`write_lastRevealing`); enqueue/peek satisfy
    A, B, C of Theorem E.1 (`queue_E1_hyps`, with `put_selfCommuting`, `peek_nonMutator`).
24. **§IV.E: "The theorem can be applied to push and peek on a stack"** is false: with `peek` returning the top,
    hypotheses A and C of Theorem E.1 cannot hold together (`stack_push_peek_not_E1`), since `ρ ∘ op_1 ∘ aop_1` and
    `ρ ∘ op_2 ∘ op_1 ∘ aop_1` leave the same top. Hence the lower bound `d + min {ε, u, d/3}` for `|push| + |peek|`
    in Table III (and "(|push| or |enqueue|) + |peek|" in Chapter VI) is not supported by Theorem E.1. ❌: a
    concrete claim that an object is in a class is false, and nothing we proved gives the bound. Checked against the
    rendered thesis pages 47 and 76 (PDF pages 56, 85). The claim is in the thesis; the 2-page PODC brief
    announcement is not openly available, so whether it repeats the claim is unknown. The `|push| + |peek|` bound
    itself is neither proved nor refuted here (for the purposes of E.1 a peek after pushes behaves like a read after
    writes, which the thesis itself excludes).
