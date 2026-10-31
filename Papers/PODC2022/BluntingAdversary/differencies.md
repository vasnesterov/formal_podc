# Differences between the formalization and the paper

Attiya, Enea, Welch, *Blunting an Adversary Against Randomized Concurrent Programs with Linearizable
Implementations*, PODC 2022 (arXiv 2106.15554v2). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Errors in the paper

1. **Lemma 4.3 is false (R1: numbered lemma → ❌).** The paper claims, for every adversary `A` against
   `P(O^k)`, `Prob[(P(O^k)||A → B) | X] ≤ Prob[P(O^a) → B]`. Conditioning on `X` (all object random steps
   pick randomization-free iterations) biases the *program* coins: whether the iteration chosen later is
   overlapped by the second program random step can be arranged by the adversary depending on the first coin.
   Counterexample (`Counterexample.lean`): two processes, a register `R` and a dummy object `S` whose read has
   a one-access preamble; `p: c1 := coin; R.write(c1); c2 := coin`, `q: S.read(); y := R.read()`, `B = {y = 1}`;
   `Prob[P(O^a) → B] ≤ 1/2`; for `k = 2` the adversary that overlaps `q`'s first preamble iteration with `c2`
   only when `c1 = 0` gets `Pr[B ∧ X] = 1/2`, `Pr[X] = 3/4`, so `Pr[B | X] = 2/3` (`lemma_4_3_false`,
   `lemma_4_3_numbers`). All hypotheses of Theorem 4.2 hold (the object is even strongly
   linearizable; at most two random steps).
2. **Lemma 4.4 is false (R1 → ❌).** Same instance, adversary overlapping only when `c1 = 1`:
   `Pr[B | ¬X] = 1 > 1/2 ≥ Prob[P(O) → B]` (`lemma_4_4_false`; numbers in `lemma_4_4_numbers`).
3. **Proof gap in Lemmas 4.3/4.4 beyond the conditioning: the simulating adversary `A_O` is not an adversary.**
   `A_O(v) = remRedundant(A(u))` picks the "best" object random value *after* seeing later program coins, and
   removing the unused iterations moves preamble steps relative to earlier program random steps, so the
   executions of `A_O` for two coin sequences with a common prefix need not agree up to the next random step
   (the paper's own condition on adversaries). Such a retroactive choice can beat every real adversary
   (e.g. a read whose preamble is iterated once before and once after a write, with the choice made after
   seeing a later coin). Repair used here: the object random choices are independent of everything the
   adversary sees before they are made, so they can be sampled *in advance* (`Removal.opt_le_avg`); the
   simulating adversary against `P(O)` then knows them causally.
4. **Theorem 4.2 (headline) is unestablished for `r ≥ 2`.** Its proof is the chain (1)–(2) built on Lemmas
   4.3 and 4.4, both false. We prove (a) the theorem exactly as stated for `r = 1` (`theorem_4_2_r1`; this is
   the case used in Appendix A.3.1), and (b) for every `r` the weaker bound
   `Prob[O^k] ≤ Prob[O^a] + (1 − q)` together with `Prob[O^k] ≤ Prob[O]`, `q = (max{0,k−r}/k)^{n−1}`
   (`theorem_4_2_weak`, `prob_iter_le_prob_impl`). We neither proved nor refuted the stated bound
   `Prob[O^a] + (1 − q)(Prob[O] − Prob[O^a])` for `r ≥ 2`. The natural repair of the paper's argument
   (induction over the random steps, mixing over the advance-sampled choices) breaks exactly where the
   adversary correlates which choices get spoiled at a later random step with the gap `Prob_O − Prob_{O^a}`
   of the resulting configurations. Per R5 an unestablished headline is ❌.
5. **Lemma 4.5 is true; its proof is imprecise.** "`Prob[X] = ∏ Prob[X_i]` since the random choices are
   independent" ignores that which iterations are spoiled depends adaptively on earlier object choices and
   coins; the bound still holds (path-wise product argument). We prove it by a potential function
   (`Clean.optNX_le`). 🛠️-level.
6. **Theorem 3.1 is ill-typed as stated** (tail strong linearizability is defined for objects/sets of
   executions with control points, the theorem speaks of sets of *histories*). Not formalized; we model a set
   of objects as one combined object, so locality is not needed (see Modelling).

## Modelling choices

- **Programs and outcomes.** One deterministic client per process (`Program`): local step, `random(V)` with
  `|V| = m+1` uniform, call of an operation with continuation, done. An *outcome* is the vector of final client
  states; the paper's outcomes (return values of invocations, identified by process/line/count) are a function
  of it for a client that records its responses, so quantifying over all `B` on client states is at least as
  general.
- **Set of objects `O`.** Modelled as one object whose operations are tagged by the component object
  (the paper uses locality, Theorem 3.1, for the same purpose). Tail strong linearizability is assumed for the
  combined object.
- **Objects.** Deterministic shared-memory implementations (CSLib `Impl`: base objects with sequential
  specifications accessed atomically, deterministic per-process code with persistent local state). All
  operations are allowed (`hall : ∀ p o, I.allowed p o`). Message-passing implementations (ABD) are **not**
  covered; Section 5 is not formalized.
- **Preamble mapping.** Given as a predicate `Π p l` = "local state `l` is still inside the preamble of the
  current operation" instead of a control point; `PreambleWF` encodes "every path passes through `Π(M)`
  before returning, and `Π(M)` is not inside a loop". **Effect-free** = every preamble step applies a
  read-only primitive (the paper also allows message sends that do not change other processes' local states,
  i.e. ABD; not covered).
- **Complete executions / tail strong linearizability.** `Complete Π C`: every pending invocation is past its
  preamble. `TailStronglyLinearizable I Π`: `I` linearizable and a linearization function on complete
  executions, prefix-preserving between complete executions (CSLib `IsLinearization`).
- **`O^k` (Algorithm 2).** `iterSem I Π k`: the invocation re-runs the preamble from the local state right
  after the call, stores the `k` results, then one step `random([1..k])`. Bookkeeping (restart/record) is a
  separate local step (it changes no shared state). Ghost fields record which iterations overlapped a program
  random step ("randomization-free" = no program random step strictly between the first and last step of the
  iteration).
- **Adversaries and `Prob`.** Strong adversary = picks the next process with full knowledge of the
  configuration (which determines all past random values). `Prob[P(O) → B]` is the optimal value of this
  finite-horizon game (`MDP.opt`, supremum over horizons; runs that do not terminate count as not reaching `B`).
  This equals the supremum over the paper's adversaries (maps from coin sequences to schedules); the paper
  assumes every schedule terminates, which we do not need. For the counterexamples, a fixed adversary is a
  positional strategy on configurations and probabilities are its values.
- **Atomic object `O^a`.** The atomic object of the sequential specification `A` (`atomSem A`): the paper's
  "atomic object equivalent to `O`"; equal to it when `O` can complete every operation in isolation.
- **"At most `r` random steps"** is assumed for `P(O)` (`AtMostRandom`), as in the paper; we derive it for
  `P(O^k)`.
- **`n`** = number of processes (`Fintype.card P`), `k ≥ 1`.

## Not formalized

Propositions 2.1, 2.2; the converse direction of Theorem 2.3 (we prove `Prob[O] ≤ Prob[O^a]` for strongly
linearizable `O`); Theorem 3.1; the history-equivalence statement of Theorem 4.1 (we prove its consequence
`Prob[O^k] ≤ Prob[O]`); Section 5 (Theorem 5.1 and the snapshot / Vitányi–Awerbuch / Israeli–Li claims);
Appendix A (ABD case study).

## Verdict calibration

- Worst label: ❌ (R1: Lemmas 4.3 and 4.4 are numbered lemmas and false; R5: the headline Theorem 4.2 is
  only unestablished for `r ≥ 2`, not refuted, so not 🚨).
- Borderline check (R2): the formalized counterexample uses `k = 2 = r`, where the bound of Theorem 4.2 is
  trivial. The lemmas are stated for every `k` and every adversary, and the instance is not degenerate
  (two processes, two coins). The same adversary works for every `k ≥ 1`: `Pr[X] = 1/2 + (k−1)/(2k)`,
  `Pr[B ∧ X] = 1/2`, so `Pr[B | X] = k/(2k−1) > 1/2` (computed by hand, only `k = 2` is in Lean).
- Scope of the counterexample (checked in review). The adversary `σ b` reads only the client states and
  the busy flags (no ghost fields) and depends only on the past coin `c₁`, so it is an adversary in the
  paper's sense (§2.4). The overlap is with `q`'s first preamble iteration, which starts at the call step;
  the paper counts the call transition as part of the preamble (§3, "empty" preamble = call transition
  only). The counterexample does not depend on this convention: with an `S`-read whose preamble makes two
  read-only accesses the same adversary works. The instance does not refute Theorem 4.2 itself: there
  `Prob[O] = Prob[O^a] = 1/2` and `Prob[O^k] ≤ 1/2` (B forces `c₁ = 1`), so the bound holds. Biasing the
  coins only helps the adversary *within* `X` or `¬X`, not overall, which is why the headline is
  unestablished rather than refuted.
