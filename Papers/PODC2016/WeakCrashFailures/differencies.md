# Differences between the formalization and the paper

Paper: G. Taubenfeld, *Computing in the presence of weak crash failures* (PODC 2016, brief announcement); formalized
from the full version *Weak Failures: Definitions, Algorithms and Impossibility Results* (2018).

## Mistakes (labels per `mistakes-labeling.md`)

1. ✏️ **Theorem 1, `n = 1`.** "For every `n ≥ 1`": the algorithm of Fig. 1 violates validity for `n = 1` (decides
   `0`, the initial value of `max`; `Fig1.fig1_invalid_n1`). Degenerate case; §1.3 says `n > 1`; the existence
   claim itself is trivial for `n = 1`. We prove Theorem 1 for `n ≥ 2` (`Fig1.theorem1`).
2. ✏️ **Corollary 2, `n = 1`.** False for `n = 1`, `ℓ = 0` (`corollary2_false_n1`). Proved for `n ≥ 2`
   (`corollary2_paper`).
3. ✏️ **After Corollary 2.** "there is no consensus algorithm that can tolerate two crash (n−1)-failures" needs
   `n > 2` (stated in §1.3); for `n = 2` it is false (`weakAdmissible_iff_of_card_two` + Theorem 1).
4. ✏️ **Appendix A, k-deadlock-freedom.** Literally unsatisfiable when the only trying process then crashes; we use
   "if fewer than `cap` processes are delayed forever, and some non-delayed process is trying, then some process
   eventually enters" (`Fig2.DF`). Delayed forever = participates but takes finitely many entry-code steps (crashed,
   abandoned after seeing `decision`, or entered the CS — in Fig. 2 nobody ever exits).

## Statements stronger than the paper's (hypotheses not needed)

- Theorem 3 (termination of Fig. 1) holds for every `n` (`Fig1.theorem3` has no assumption on `n`); agreement and
  validity need `n ≥ 2`.
- Theorem 4/5: `n ≥ 2ℓ + k − 2` and `ℓ ≥ 1` are not needed; termination needs `ℓ + k ≥ 2`, k-agreement `k ≥ 1`
  (`Fig2.theorem4'`, `Fig2.theorem5`). Lemma 8 is proved (`Fig2.lemma8`) but not used.
- Lemma 5 holds for every `m` (`Fig2.lemma5`).
- Theorem 7 does not need `k ≥ 1`; Corollary 1 holds for `n > ℓ + k` (paper: `n > 2ℓ + k`); Corollary 2 holds for
  `n > ℓ + 1` (`corollary2`).
- Corollary 2 is derived in the paper as an "immediate corollary" of Corollary 1 with `k = 1`, which needs
  `n > 2ℓ + 1`; the stated range `ℓ < n/2` also contains `n = 2ℓ + 1`. For `ℓ ≥ 1` that case follows from Theorem 7
  directly (`corollary2`); for `ℓ = 0`, `n = 1` it is the false degenerate case (mistake 2).

## Proof details filled in

- Fig. 1, Lemmas 3–4: proved through one inductive invariant (`Fig1.Inv`): every decided or written value is
  `val x t` for a *tag* `t` (`ex y` = max of the inputs of all processes but `y`; `all` = max of all inputs) with
  justification `TagFact`; two justified tags coincide (`TagFact.unique`, `n ≥ 2`). The paper's "process j will never
  be able to set state[j] to 3" (Lemma 3.3) is the invariant `DoomedR C 3 j`, established when a process reads
  `state[j] < 2` in line 18 (all others are already `3` by the round-3 wait).
- Line 21 comment "at this point it must be that counter = n" is proved (the round-3 wait set is contained in the
  line-18 count).
- Fig. 1, Theorem 3: the paper's sketch is turned into a level/rank argument (`Fig1Ranks.lean`, `Fig1Live.lean`);
  Lemma 1 is used in the form: a weakly failing process with `state ≥ 2` stops while some `q` has not started, and
  then `q` is doomed in round 1 (`DoomedR 1 q`), contradicting that `q` is correct and progresses (`Fig1.lemma2`).
- Fig. 2, Theorem 5: deadlock-freedom of `EX[2]` gives "some process enters", not "some correct process enters";
  crashed entrants are delayed forever, there are `≤ k − 2 < k − 1` delayed processes, and repeated application of
  deadlock-freedom would give infinitely many entries — impossible. The paper states the conclusion directly.

## Modelling choices

- Executions are infinite schedules `ℕ → P`; correct = infinitely many steps; decided processes take no-op steps
  (so participation is required, as the paper assumes). Faulty processes that never step are initial failures.
- Point contention at time `t` = number of processes that took a step before `t` (participation never ends). An
  m-failure (type 1) stops at a time with contention `≤ m`. For Fig. 1 the alternative reading (terminated processes
  stop participating) gives the same result, since a terminated process has written `decision` and then every
  correct process decides (`Fig1.eventually_done_of_dec`).
- Type-2 failures are only defined in the paper, never used; not modelled.
- Fig. 1: one shared-memory access per step; consecutive reads of `decision` in lines 13–14 and 22–23 are merged
  (removes stuttering only); `decide` is folded into the preceding write of `decision`; inputs are natural numbers
  ("non-negative"); initial values of `input[]` are an arbitrary parameter `inr₀` ("immaterial"). Validity is "the
  input of a process that has taken a step" (`started`).
- Fig. 2: atomic snapshot and `decision` are single atomic objects; the exclusion objects are given by their
  specification (safety in the step, deadlock-freedom `DF` as hypothesis on executions), not by a register
  implementation; line 7's two threads are interleaved by the scheduler, with a fairness hypothesis `Fair`. The
  local `counter` is kept after the loop (used by Lemmas 5–7). The threshold `n − ℓ − k + 2` is `n + 2 − (ℓ + k)`
  (truncated subtraction; equal whenever it is nonnegative).
- Section 5: model `Cslib.SWMR` (single-writer registers, deterministic algorithms) instead of multi-writer
  registers; the k-set consensus task uses validity "input of some process" (weaker than "of a participating
  process", so the impossibility is stronger). The k-set impossibility (BG/HS/SZ) is a hypothesis
  `KSetImpossible K Vr V k` (for the same register types and value type; classically true iff `V` has more than `k`
  values — for `|V| ≤ k` "decide your own input" solves k-set consensus, so Theorem 7 is meant for larger `V`); for `k = 1` it is proved from FLP for any
  `V` with two distinct values.
- Theorem 1 is stated for the concrete algorithm of Fig. 1 (agreement, validity, termination), not as an abstract
  "there exists an algorithm"; Theorem 4 for Fig. 2 with any exclusion objects meeting the spec.
