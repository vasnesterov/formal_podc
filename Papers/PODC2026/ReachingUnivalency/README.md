# Reaching Univalency with Subquadratic Communication — PODC 2026

Andrew Lewis-Pye. *Reaching Univalency with Subquadratic Communication.* PODC 2026. DOI
[10.1145/3796701.3815918](https://doi.org/10.1145/3796701.3815918). Formalized version: arXiv
[2602.05356](https://arxiv.org/abs/2602.05356) v1 (the same text as the proceedings version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Lemma 6 and the claim that the §5 protocol (Fig. 3) solves ε-BA are false. In a Lean
counterexample (`n = 38`, `ε = 1/5`, `f = 5`, `k = 37`), correct processors output different values although every
sample is accurate to within `ε/2` on every set and the committees act as an ideal BA functionality. Theorem 1 itself
holds: we prove it for a corrected protocol (step-1 threshold `k(2/3 − ε/4)`, samplers accurate also on sets that
contain Byzantine processors). The appendix lower bounds and Propositions 3 and 5 are proved.

## Mistakes in the paper

- **Lemma 6 is false, and the §5 protocol is incorrect as specified (false statement; Theorem 1 itself is true).**
  - *What breaks.* The proof needs "time-slot-1 agreement": two correct, accurately sampling processors never get
    different response values in step 1. With the threshold `k(2/3 − ε/2)` this needs perfectly representative
    samples. Write `f/n = 1/3 − ε − η`. Any sample deviation larger than about `η` lets the Byzantine processors push
    one sampler to `0` and another to `1`. Here `η` can be arbitrarily small, while samples may deviate by up to
    `ε/2`.
  - *A second gap.* The proof never bounds the Byzantine processors in a sample. "Bad" only compares the fractions of
    *correct* processors with value `b`. The step "a non-bad `p` sees `≥ 2k/3` copies of `b`, hence
    `α_{2,b} > 2/3 − ε/2`" ignores that these copies may come from Byzantine processors.
  - *Counterexample.* `n = 38`, `ε = 1/5`, `f = 5 < 38(1/3 − ε)`, `k = 37`. The 5 Byzantine processors lie in
    `C₁ = {0..18}`; `C₂ = {19..37}` is fault-free. In steps 1 and 2 every processor samples the 37 processors other
    than `13`. In step 3 it samples the round's committee `C_r` cyclically. For every step, every processor and every set of
    processors, the sample deviates by at most `1/19 < ε/2`. So no processor is ever bad, under §4's definition or
    §5's stronger "every configuration" definition.
  - *The run.* Before round 2, 16 correct processors have value 0 and 16 have value 1 among those sampled, so in
    step 4 the Byzantine processors can steer each correct processor to response 0 or 1. They make 20 respond 1 and
    12 respond 0. In step 5 the 14 correct members of `C₁` see `20 + 5 = 25 ≥ 2k/3` copies of `1` and keep `1` with
    grade 2. All members of `C₂` see both values at least `k/3` times, so they get grade 0 and keep their values: 16
    zeros and 3 ones. `C₂` then outputs `0`, which ε-Validity forces since only `3 < 19ε` inputs differ, and everyone
    but `C₁` adopts `0`. Final outputs: 14 correct processors output `1` and 19 output `0`, while `nε = 7.6`.
  - *Recursive version.* The committees may behave as an ideal BA functionality (`Counterexample.lean`). They may
    also run the paper's own recursive protocol with a sampler at size 19 that is accurate on every set
    (`PaperProtocolFails.lean`). Either way ε-Agreement fails, whatever the sampling choices at the other sizes.
  - *Larger `k`.* Lean proves this for `k = 37` only. For every `k = 37m` the same execution works: repeat each
    step-1/2 sample `m` times and sample the committee cyclically (`j mod |C_r|`). This is argued by hand, not
    checked in Lean.
  - *Fix.* With the step-1 threshold `k(2/3 − ε/4)`, and samples `ε/8`-accurate also on sets that contain Byzantine
    processors, the paper's argument goes through. We prove the corrected one-level lemma, the existence of such
    samplers with `k = k(ε)`, the recursion and the message bound. (`lemma6_false`, `paper_protocol_fails`,
    `lemma6_corrected`, `theorem1_corrected`)
- **§5's derandomisation proves a property that the proof of Lemma 6 does not use (proof gap).** The counting
  argument gives samplers that are good on every configuration, which also bounds the Byzantine processors in a
  sample. Lemma 6, however, is stated and proved only for the actual configuration. Our `exists_sampler` proves the
  needed form: for every set `S`, at most `γn` processors deviate by `≥ δ` on `S`. This needs only Chebyshev plus
  the product structure, not KL-Chernoff.
- **Proposition 4 (Extractable BA ⇒ BA): proof gap.** The text after the definition claims that Consistency
  together with `F(M_c) ∈ {0,1}` implies `F(M) = F(M_c)` for all `M_c ⊆ M ⊆ M_a`. This does not follow, since
  `F(M)` may be the empty string. Also, during dissemination faulty processors may forward messages that are not in
  `M_a`. Requiring `F` to be monotone (`M ⊆ M' ⊆ M_a ⇒ F(M) ⪯ F(M')`) fixes this. The extraction function of
  Proposition 5 is monotone, so Theorem 2 is unaffected. (`consistency_not_monotone`, `prop5_extract`)
- **Minor.**
  - Appendix B argues about processors: "fewer than `f/2` correct processors send or receive". The step to
    `Ω(f)` *messages* is implicit. The proof uses only the two fault-free executions with uniform inputs, in which
    every message has two correct endpoints, so we get `≥ f/4` messages (`appendixB_messages`).
  - Theorem 7 assumes `f < n − 1`. The implication holds for `f ≤ n`; for `f ≥ n − 1` its hypothesis cannot be
    satisfied.
  - Footnote 6 lets `t*` depend on the inputs; we fix `t*`.
  - With samples drawn "with replacement", the deterministic protocol must count a processor sampled twice twice.
    Fig. 3 ("send your value to every processor that samples you") leaves this implicit.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Lower bounds.* CSLib's synchronous lock-step executions `OmExec` (`Cslib.Byzantine.PartialSync`):
  - an execution is the inputs plus the set of delivered batches;
  - processes are arbitrary deterministic state machines;
  - message complexity counts messages from correct processes to others.
- *Theorem 7.* Omission faults (`Admits`). Faulty processes run the protocol, so signatures are irrelevant and the
  authenticated case is covered.
- *Appendix B.* Crash faults (`CrashAdm`): a crashing process delivers an arbitrary subset of its batches at its
  crash time and nothing afterwards. `P₁; P₂` is one algorithm whose first phase is the time interval `< t*`.
  Univalency is the paper's: every admissible execution extending the prefix before `t*` decides the same value.
- *ε-RPK.*
  - Lock-step, Byzantine faults, static adversary, deterministic. The two committees are `C₁`, `C₂`.
  - A sampling choice lists, for each round, step and processor, `k` sampled processors (repetitions counted).
  - Byzantine processors answer each sampler arbitrarily (`Option Bool`, where `none` is `⊥` or silence). Step-3
    ties are broken adversarially.
  - One level (`RPK.lean`) treats committee instances as black boxes that must satisfy ε-BA only within their fault
    bound, as §4 does.
  - The recursion (`Recursive.lean`) runs the protocol itself on the committees, re-indexed. The Byzantine behaviour
    inside a committee may depend on all values. On `n ≤ 2` processors a trivial base protocol runs; there are no
    faults there.
- *Complexity.* Each sample is one message carrying a value in `{0,1,⊥}`. The count `6kn` per level plus the
  recursive calls is a recurrence that follows the protocol's structure; it is not derived from an operational
  message semantics.

**Main results in Lean.** Namespace `ReachingUnivalency`.

| Paper | Lean | File |
|---|---|---|
| Theorem 7 (`Ω(n + f²)`, with `⌈f/2⌉²`) | `theorem7`, non-vacuity `helloAlg_alwaysReceives` | `Dissemination.lean` |
| Appendix B (`Ω(f)` to reach univalency) | `appendixB`, `appendixB_half`, `appendixB_messages` | `UnivalencyLowerBound.lean` |
| Proposition 3 (ε-BA + majority ⇒ BA) | `prop3` | `EpsBA.lean` |
| Proposition 5 (committee size, extraction function) | `prop5_committee`, `prop5_extract` | `EpsBA.lean` |
| §2.4 remark (Consistency ⇒ monotonicity): **does not follow** | `consistency_not_monotone` | `EpsBA.lean` |
| Lemma 6: **false** | `RPK.Lemma6Claim`, `Counterexample.lemma6_false` | `RPK.lean`, `Counterexample.lean` |
| Fig. 3 protocol with admissible `Smp₃₈`, `Smp₁₉`: **fails** | `PaperFails.paper_protocol_fails` | `PaperProtocolFails.lean` |
| Lemma 6, corrected (threshold `2/3 − ε/4`) | `RPK.lemma6_corrected`, `RPK.lemma6_corrected_sampling` | `Corrected.lean` |
| §5 existence of samplers (corrected form) | `RPK.exists_sampler` | `Sampler.lean` |
| Theorem 1 (corrected protocol; correctness and `O(n log n)`) | `RPK.theorem1_corrected` (`outcome_epsBA`, `msgs_le`) | `Theorem1.lean`, `Recursive.lean` |

**Not formalized.**
- Theorem 2 end to end: Extractable BA with signatures and `O(f log f)` communication. It is Proposition 5 (proved
  combinatorial core) plus Theorem 1 (proved).
- Proposition 4 with a repaired (monotone) Consistency.
- The randomised protocol's probability statements: we work directly with deterministic samplers.
- The extension to adaptive adversaries and to `Δ`-bounded delays.

**Trust.** No `sorry`; all listed theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- *Kernel computation.* The counterexample executions are evaluated by `decide +kernel`; there is no
  `native_decide`.
- *Non-vacuity.*
  - Theorem 7: an algorithm satisfying its hypothesis.
  - Corrected Lemma 6: `NonVacuity.nonvacuous` (`n = 8`, one Byzantine processor, every Byzantine behaviour).
  - Recursion: `outcome_exists`, every size has executions.
  - The counterexample's hypotheses are checked in full (accuracy on all `2^38` sets via an ℓ¹/TV bound).
- *Not checked.* There is no non-vacuity instance for Appendix B's hypotheses, i.e. a crash-tolerant BA protocol
  with a univalent first phase in this model (FloodSet would be one).
- *Dependencies.* The lower bounds reuse CSLib `Cslib/Computability/Distributed/Byzantine/PartialSync/Omission.lean`.
  The sampler existence (§5) uses the shared finite probability library `Podc/Probability/Finite/Uniform.lean`
  (Chebyshev for sampling with replacement `card_freq_dev_ge_le`, many rare events `card_many_le`, union bound
  `card_filter_exists_le`).
