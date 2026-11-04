# Time Bounds for Shared Objects in Partially Synchronous Systems — PODC 2011

Jiaqi Wang, Jennifer L. Welch, Hyunyoung Lee. *Brief Announcement: Time Bounds for Shared Objects in Partially
Synchronous Systems.* PODC 2011. DOI [10.1145/1993806.1993877](https://doi.org/10.1145/1993806.1993877).
Formalized version: the full version, J. Wang's MS thesis of the same title (Texas A&M, December 2011, advisor
J. L. Welch); numbering follows the thesis (Chapter IV for the lower bounds).

**Verdict: ❌ False claim.** The `d + min {ε, u, d/3}` lower bounds hold: for every strongly immediately
non-self-commuting operation (read-modify-write, dequeue, pop; Theorem C.1) and for `|OP| + |AOP|` under the
hypotheses of Theorem E.1. The `(1 - 1/k) u` bound of Theorem D.1, one of the three main results, is not established:
its proof has an unrepaired gap; we prove it only under a stronger hypothesis, which covers writes and every `k = 2`,
and for skew `ε ≥ (1 - 1/k) u`. The claim that Theorem E.1 covers push/peek on a stack is false.

## Mistakes in the paper

### ❌ Theorem D.1 of Chapter IV (Step 1.1 of the proof)
Step 1.1 asserts a single legal permutation `π` of the `k` concurrent operations that fixes the results of *every*
later sequence of operations; correctness does not give this, and without it the runs of the proof yield no
contradiction (`tr_answers`).

**Impact.** Theorem D.1, a main result of the thesis (abstract), is unestablished in its stated generality (rule
R5: an unestablished headline is ❌); we have neither a proof nor a counterexample. We prove it under a stronger
hypothesis, `LastRevealing` (one fixed query sequence whose results determine the last of the `k` operations). This
covers writes with `k = n` (`write_lastRevealing`), every case `k = 2` (`theorem_D1_two`), and, by the same argument
(not formalized), push (one pop) and enqueue (`k` dequeues).

**Details.** Correctness gives a linearization for each complete run; an algorithm may decide the order of
concurrent operations lazily, depending on later operations. The proof's runs `R₁` and its shifts `R₂^z` only
imply: the answers of later queries are compatible, for every `z`, with some permutation that respects the real-time
order of `R₂^z`. If `|OP|` is close to `(1 - 1/k) u` (above `(1 - 2/k) u`), that order only puts `op_z` before
`op_{z+1 mod k}`, so `op_z` is not last. For the "test-and-reset" register (writes `W a`; `T a` answers whether the
value is `a` and resets it), the writes satisfy the theorem's hypothesis (`tr_nonEquiv`), yet for `k = 3` every
query sequence has answers compatible, for every `z`, with a permutation whose last write is not `z` (`tr_answers`;
only the last write matters, so one with `op_z` before `op_{z+1}` exists). So the hypothesis does not imply
`LastRevealing` (`tr_not_lastRevealing`). We do not know whether Theorem D.1 itself fails for this object.

**Repair.** `theorem_D1`: with `ε ≥ (1 - 1/k) u` and `LastRevealing`, `|OP| ≥ (1 - 1/k) u`. The thesis's shifts
and its six-case delay check are correct (after the typo below).

### ❌ §IV.E and Table III (push and peek on a stack)
The thesis says that Theorem E.1 "can be applied to push and peek on a stack" and lists `d + min {ε, u, d/3}` as a
lower bound for `|push| + |peek|`, but push/peek never satisfy the hypotheses of Theorem E.1
(`stack_push_peek_not_E1`).

**Impact.** The push+peek entry of Table III (and the same claim in Chapter VI) is unproved; the theorem itself and
its application to enqueue/peek on a queue are fine (`queue_E1_hyps`). For E.1's hypotheses, a peek after pushes
behaves like a read after writes, a case the thesis itself excludes from Theorem E.1 (overwriting).

**Details.** Hypothesis A asks that exactly one of `ρ ∘ op₁ ∘ aop₁` and `ρ ∘ op₂ ∘ op₁ ∘ aop₁` be legal. With
`op₁`, `op₂` pushes and `aop₁` a peek, both sequences leave the element of `op₁` on top, so they are legal
together or illegal together (as soon as hypothesis C makes `op₁`, `op₂` legal instances). A peek of a queue sees
the first element, which is why enqueue/peek works.

### ⚠️ Theorem D.1 of Chapter IV (missing assumption on the clock skew)
The run `R₂` of the proof has clock skew `(1 - 1/k) u`, but the theorem allows any `ε`; the bound is established
only for `ε ≥ (1 - 1/k) u` (`theorem_D1`).

**Impact.** Local fix: the proof states that it assumes the optimal skew `ε = (1 - 1/n) u ≥ (1 - 1/k) u`, and
Chapter V makes the same assumption. For smaller `ε` the bound appears to fail: Algorithm 1 of Chapter V answers
pure mutators (writes) after `ε` (not formalized).

### ⚠️ Definitions D.1 and D.4 (mutator, pure accessor)
Read literally, no operation type is a pure accessor (`not_pureAccessor`), so Theorem E.1 is vacuous.

**Impact.** Typo-level: the intended definition (Kosa) compares only legal sequences; with it (`NonMutator`)
Theorem E.1 is proved (`theorem_E1`).

**Details.** An accessor has a legal `ρ` with `ρ ∘ op` illegal; then `ρ ∘ op` is not equivalent to `ρ`, so `op` is a
"mutator" by Definition D.1.

### Typos and slips
- Proof of Theorem D.1, Step 2: the shift `x_i = [-(k-1)/2 + ((z-i) mod k)/k] u` should read `-(k-1)/(2k)` (as in
  Step 2.2 and in the skew computation).
- Proof of Theorem C.1, Step 2: "messages from `p_j` to `p_k` cost `δ = d - m`" should be `p_j` to `p_i`.
- Proof of Theorem E.1, Step 1: "since `aop'₁` and `aop'₂` are pure mutators" should be pure accessors.
- §III.B.2: views require strictly increasing clock times, which rules out simultaneous receipts such as those at
  `p_k` in the run `R₁` of Theorem C.1; non-decreasing times are meant.

## Proof gaps (statements true)

### 🛠️ Theorem E.1 (both orders of `op₁`, `op₂` are legal)
The proof infers that `ρ ∘ op₁ ∘ op₂` and `ρ ∘ op₂ ∘ op₁` are both legal from immediate self-commutativity, which
needs `ρ ∘ op₁` and `ρ ∘ op₂` legal; hypothesis C gives only one of them.

**Impact.** Statement true; repaired by running each operation alone after `ρ`: a correct implementation returns a
legal value, and determinism does the rest (`theorem_E1`).

**Details.** We also invoke the accessors at fixed times (`t + B₁ + η` and `m` later) instead of the thesis's
adaptive times; this makes the case analysis of Step 2.2a unnecessary.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Partially synchronous message passing, `n` processes (`Fintype P`), no failures, reliable channels, message delays
  in `[d - u, d]` chosen by the adversary as a function of sender, receiver and send time, drift-free clocks with
  offsets of pairwise difference at most `ε` (`Cslib.TimedMP.Scenario.Admissible`). Deterministic algorithms, no
  randomness. The adversary also chooses the clock offsets and the invocation times (one pending operation per
  process, `WF`).
- An algorithm is given by causal local behaviours in local clock time (`Cslib.TimedMP.Algorithm`): every non-Zeno
  timed automaton of the thesis is one. Runs exist and are unique (`exists_run`, `IsRun.unique`); shifting a run is
  `IsRun.shift`; chopping and extending is running another scenario that agrees before a causally closed cut
  (`agree_of_cut`, `agree_window`).
- Hypotheses on the algorithm, all from §III.B.4: correctness (`Correct`: unique responses, linearizability with the
  real-time order "response < invocation"), bounded operation time (`TimeBound … Bop`), finite runs (consequence of
  bounded quiescence, `FiniteRuns`), history-obliviousness (`HistoryOblivious`, same residual behaviour after two
  runs executing the same operations). Theorem D.1 needs only correctness and `Bop`.
- `|OP| ≥ X` is stated as: if every `OP` operation responds within `B` in all admissible runs, then `B ≥ X`.
- Proof remarks: Theorem C.1 holds for `n ≥ 2` (the thesis assumes `n ≥ 3`); the `ρ`-prefix of every run is a fresh
  admissible run glued by history-obliviousness (`restart`), which is necessary when `2 min {ε, u, d/3} > u`; where
  the thesis invokes an operation "immediately after" a response, we leave a small gap, since precedence is strict.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem C.1 (Ch. IV) | `theorem_C1` | `TheoremC1.lean` |
| Theorem D.1 (Ch. IV), repaired | `theorem_D1` | `TheoremD1.lean` |
| Theorem D.1 (Ch. IV), `k = 2`, thesis hypothesis | `theorem_D1_two` | `TheoremD1.lean` |
| Theorem E.1 (Ch. IV) | `theorem_E1` | `TheoremE1.lean` |
| Step 1.1 of Theorem D.1 unsupported | `tr_answers`, `tr_not_lastRevealing` | `Examples.lean` |
| E.1 does not apply to push/peek | `stack_push_peek_not_E1` | `Examples.lean` |
| Definitions D.1/D.4 literal | `not_pureAccessor` | `Spec.lean` |
| Examples (RMW, write, enqueue/peek) | `rmw_strongly`, `write_lastRevealing`, `queue_E1_hyps` | `Examples.lean` |
| Claims B.1–B.4, Lemma B.1 | `IsRun.shift`, `agree_of_cut`, `agree_window`, `restart` | `Podc/…/Timed/Basic.lean`, `Setup.lean` |

**Not formalized.** Chapter V (Algorithm 1 and its correctness and time bounds, Theorems C.18, D.1, D.2 of
Chapter V) and the remaining entries of the tables of Chapter VI.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
hypotheses of the theorems on specifications are shown satisfiable by concrete objects (`Examples.lean`); the
hypotheses on the algorithm (`Correct`, `TimeBound`, `FiniteRuns`, `HistoryOblivious`) are those of the thesis;
their joint satisfiability is not machine-checked (for `u < d` a centralized implementation, which forwards every
operation to one process that applies them in arrival order and keeps only the object state and message counters, satisfies them with
`|OP| ≤ 2d`). The timed model is staged in `Podc/Computability/Distributed/MessagePassing/Timed/`
(CSLib candidate).
