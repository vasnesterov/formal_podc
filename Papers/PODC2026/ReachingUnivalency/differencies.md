# Differences between the formalization and the paper

Paper: A. Lewis-Pye, *Reaching Univalency with Subquadratic Communication*, PODC 2026 (arXiv 2602.05356v1).

## Errors in the paper

1. **Lemma 6 is false (false statement).**
   - Lean: `RPK.Lemma6Claim`, refuted by `Counterexample.lemma6_false`.
   - Instance: `n = 38`, `ε = 1/5`, `f = 5`, `k = 37`.
   - The sampling is accurate to within `≤ 1/19 < ε/2` on *every* set for every processor (`sampling_accurate`).
     So no processor is bad, under §4's definition or §5's "any configuration" definition.
   - The committees behave as an ideal BA functionality: every member outputs the majority of the correct members'
     inputs. This is a valid ε-BA outcome within the fault bound (`majorityOracle_epsBA`).
   - Result: 14 correct processors output 1 and 19 output 0, against `nε = 7.6`.
   - Root causes:
     - (a) With step-1 threshold `k(2/3 − ε/2)`, two accurately sampling correct processors can respond `0` and `1`
       as soon as `f` is close to `n(1/3 − ε)`. "Time-slot-1 agreement" fails.
     - (b) "Bad" only looks at the fractions of correct processors with value `b`. The proof's step from "a non-bad
       `p` sees `≥ 2k/3` copies of `b`" to "`α_{2,b} > 2/3 − ε/2`" ignores Byzantine samples.
     - (c) The case split "at least `nε/4` correct processors have grade 2" should be "some non-bad processor has
       grade 2". This one is presentation only.
2. **The protocol of §5 (Fig. 3) is incorrect for admissible sampling choices (false statement about the protocol;
   Theorem 1 is still true).**
   - Lean: `PaperFails.paper_protocol_fails`.
   - The recursive protocol uses the paper's threshold, `Smp₃₈ = σ38` and `Smp₁₉ = σ19`. Both are accurate to within
     `ε/2` on every set (`σ38_accurate`, `σ19_accurate`). The sampling choices at all other sizes are arbitrary.
   - The protocol has an execution on 38 processors with 5 Byzantine ones that violates ε-Agreement.
   - Inside the committees the paper's own protocol runs. All correct members reach grade 2 in both rounds, so their
     sub-committees are irrelevant.
   - Lean proves the failure for `k = 37` only. For every `k = 37m` the same execution works: each step-1/2 sample
     is repeated `m` times, step 3 samples the committee cyclically (`j mod |C_r|`), and all counts and thresholds
     scale with the stated slack. This is argued by hand, not in Lean, but it suggests "sufficiently large `k`"
     does not help.
3. **§5's union bound proves accuracy on all configurations, but Lemma 6 is stated for the actual one (proof gap).**
   The corrected lemma needs accuracy on sets containing Byzantine processors, and these sets are among the
   configurations. `exists_sampler` proves the needed form: for every set `S`, at most `γ n` processors are
   `δ`-inaccurate on `S`, with `k` depending only on `δ` and `γ`. Chebyshev plus independence across processors
   suffices; KL-Chernoff is not needed.
4. **Proposition 4 (proof gap).**
   - The claim "Consistency ⇒ `F(M) = F(M_c)` for `M_c ⊆ M ⊆ M_a`" does not follow, because `F(M)` may be empty
     (`consistency_not_monotone`, an abstract counterexample to the inference).
   - Faulty processors may disseminate messages outside `M_a`.
   - Fix: require monotone Consistency. Proposition 5's `F` satisfies it (`prop5_extract`), so Theorem 2 is
     unaffected.
   - We did not decide whether Proposition 4 as stated is false for some protocol.

## Repairs and corrected statements

- **Corrected protocol.** The step-1 threshold is `k(2/3 − ε/4)` (`T1c`); everything else is as in Fig. 3.
- **Corrected Lemma 6** (`lemma6_corrected`, `lemma6_corrected_sampling`).
  - Sampling accuracy is `δ ≤ ε/8`. It is required on the sets "correct with value `b`", with and without the
    Byzantine processors (step 1); "correct with response `b`", with and without (step 2); and "committee members
    with output `b`" (step 3).
  - The exceptional set `B` must satisfy `|B| < |C_r| ε` for both committees and `|B| ≤ n(ε − δ)`.
  - The exceptional processors play the role of `X` in ε-Agreement.
- **Sampler existence** (`exists_sampler`): for all `δ, γ > 0` there is `k` such that for all `n` and every response
  set `R`, some sampler has `≤ γ n` inaccurate processors on every set `S`.
- **Theorem 1** (`theorem1_corrected`).
  - Parameters: `δ = ε/8`, `γ = ε/80`, committees `⌈n/2⌉ / ⌊n/2⌋`.
  - Every execution of the recursive corrected protocol with `f < n(1/3 − ε)` solves ε-BA.
  - Messages: `≤ 6kn⌈log₂ n⌉ + n`.

## Modelling choices

- **Synchrony / time.** Lock-step rounds via CSLib `OmExec`: a batch sent at time `τ` is processed into the state at
  `τ + 1`. The appendix theorems quantify over arbitrary deterministic algorithms with arbitrary state spaces, as the
  paper's state-transition diagrams do.
- **Omission faults (Theorem 7).**
  - Whole batches (per sender, receiver, time) are delivered or omitted. The paper allows dropping arbitrary
    subsets. Fewer executions make the hypothesis weaker, so the theorem is at least as strong.
  - Self-messages never count and are never omitted. "Receives at least one message" means from another process.
    With self-messages the statement would be false.
  - Authentication plays no role: omission-faulty processes run the protocol.
- **Message complexity.** Messages from correct processes to others, at times `< N`. Results say "some admissible
  execution has `≥ …` messages within finite time". The paper's "maximum over executions" follows.
- **Bound in Theorem 7.** `⌈f/2⌉²`, exactly what the proof gives. The case split is on the number of distinct
  senders rather than messages, with the same bound.
- **Crash faults (Appendix B).**
  - `CrashAdm E F`: every omitted batch is sent by a process of `F` to another process, and after its first omitted
    batch the process delivers nothing.
  - Crashed processes keep computing states in `OmExec`, but nobody hears from them.
- **`P₁ ; P₂` (Appendix B).** One algorithm; `P₁` is the time interval `< t*`.
  - `t*` is fixed. The paper's footnote 6 allows input-dependent `t*`.
  - "`E'` extends the prefix" means same inputs and same delivery pattern at times `< t*`. This is slightly stronger
    than "same messages sent", so the univalency hypothesis is weaker and the theorem stronger.
  - Agreement of BA is not used.
- **Appendix B conclusion.**
  - Processor count: `f ≤ |A₀ ∪ A₁|`, where `A_b` are the processes that send or receive before `t*` in the
    fault-free all-`b` execution.
  - Hence `f ≤ 2|A_b|` for some `b`, as stated in the paper.
  - Hence `f ≤ 4·#messages` before `t*` in that execution.
  - Hypothesis `0 ≤ f < n`.
- **ε-BA** (`EpsBAOn`, `EpsBA`). As in §2.3, relative to a committee `C`: `|X| < |C|ε`, and validity "fewer than
  `|C|ε` correct members have an input `≠ x` ⇒ `v = x`". For `n = 0` the definition is unsatisfiable, so the
  theorems assume `n ≥ 1`.
- **One level of ε-RPK** (`RPK.lean`).
  - Byzantine answers are per (step, Byzantine processor, sampler).
  - Step-1 tie order: `1` is checked first. This is harmless because at most one value can reach the threshold.
  - Step-3 majority ties are adversarial.
  - Committee instances are functions from input vectors to output vectors, constrained by ε-BA only within the fault
    bound (`CommOK`). For the counterexample this is the paper's "it does not matter how committees carry out
    ε-BA".
- **Recursion** (`Outcome`).
  - The committee instance may be a different execution for each value vector. This lets the Byzantine processors
    inside a committee react to values outside it.
  - Committees are re-indexed by any bijection.
  - Base protocol for `n ≤ 2`: everybody adopts processor 0's input. With `f < n(1/3 − ε) < 1` there are no faults,
    and the paper leaves `P` unspecified.
- **Complexity.** `msgs k n = 6kn + msgs(⌈n/2⌉) + msgs(⌊n/2⌋)` (`n > 2`), `msgs k n = n` (`n ≤ 2`). This is the
  paper's count (one constant-size message per sample, six sampling steps per level), stated as a recurrence rather
  than measured on an operational message-passing semantics.
- **Samples with repetitions** are counted with multiplicity, as in Fig. 2.

## Not formalized

- **Theorem 2.** The end-to-end Extractable BA protocol with signatures and its `O(f log f)` bound. Its combinatorial
  core, Proposition 5, is proved.
- **Proposition 4** in repaired form.
- **Probabilistic ε-RPK** with random sampling: only deterministic samplers.
- **The §6 remarks** on adaptive adversaries and `Δ`-delays.
- **Non-vacuity of Appendix B's hypotheses**: no concrete crash-tolerant BA protocol with univalent first phase is
  verified here.
