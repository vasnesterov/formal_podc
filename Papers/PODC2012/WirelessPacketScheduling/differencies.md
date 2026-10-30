# Differences between the formalization and the paper

Paper: Kesselheim, *Dynamic Packet Scheduling in Wireless Networks*, PODC 2012, arXiv 1203.1226v1.
Formalized: Theorem 1 (Section 3) and Theorem 20 (Section 8). Verdict rules: `verdicts.md` (R1–R6).

## Theorem 1 (Algorithm 1)

1. **Theorem 1 is false (statement-level, ❌).** `theorem1_false`, `theorem1_false_ln`.
   * *Instance.* `W = I` on 200 links, 5100 packets per link (`n = 1 020 000`, `I = 5100`),
     `φ = 1`. The static algorithm is all-or-nothing: if `‖W R_S‖∞ ≤ I'`, it delivers `S` in `I'`
     steps (`f ≡ 1`); otherwise it delivers nothing.
   * *Result.* Algorithm 1 fails with probability `≥ 1 − 60·(24/25)^200 > 0.98 > 1/n`.
   * *Hypotheses.* All of the paper's hypotheses hold. `𝒜(I', n')` succeeds with probability 1
     whenever `‖W R_S‖∞ ≤ I'`; the hypothesis says nothing about inputs beyond that bound (an
     algorithm that delivers most of an overloaded input would not give a counterexample; the
     falsity uses exactly this freedom, which the proof's `Y_j` also assumes away). `φ = 1`
     is a constant. The single-hop instance is exactly the setting of Section 3, with
     `m = max(|E|, D) = |E| = 200`.
   * *Why not excused.* R2: not degenerate, since `n` is large and `φ = 1` is the standard choice.
     R3: the repair changes the algorithm (`ψ` doubled) or the leading constant (`2 f(mχ)` →
     `4 f(mχ)`), and that constant is part of the claim (it is the throughput in Section 4). R4:
     no implied assumption rescues it, because the paper's own proof treats overloaded classes
     as total failures.
   * *Headline?* Borderline ❌ vs 🚨. Theorem 1 is about the paper's specific Algorithm 1. But the
     title and abstract headline is the dynamic stable protocol built from static algorithms with
     their throughput. Section 4 is stated for algorithms with `f(m) I + g(m,n)` schedules and is
     not refuted. The applications that go through Algorithm 1 (Cor. 13, 14; Sec. 7.2) are only
     *unestablished*, and probably hold with a constant factor 2 worse. Hence ❌ (R5).
   * *Which log.* The paper writes "log" without a base. The counterexample holds for base 2 and
     base `e`; the claim is parametrized by the base `b` (`Theorem1Claim b`).
   * *Our reading of "success".* "Algorithm 1 uses at most X steps" requires all packets to be
     delivered when Algorithm 1 ends. Algorithm 1 has a fixed schedule, so its length is
     deterministic (treated separately in `Time.lean`). The probabilistic content is that every
     packet is delivered, and that is what fails.
2. **Root cause (proof, Claim 2).**
   * *The error.* `E[(W R_j^{(i-1)})(e)] ≤ ‖W R^{(i-1)}‖∞/ψ ≤ χ/2` is false. With
     `ψ = ⌈2^{-i+1} I/χ⌉` and `‖W R^{(i-1)}‖ ≤ 2^{-(i-1)} I`, one only gets `≤ χ`.
   * *The repair.* `ψ = ⌈2^{-i+2} I/χ⌉` would fix this step and change the time bound to
     `4 f(mχ) I + …`. We did not formalize the repaired theorem; it needs multiplicative Chernoff
     bounds for weighted sums and negative association of balls-into-bins loads.
3. **Further gaps in the proof of Claim 2** (not formalized, documented only).
   * `ψ ≥ 4(ξ − i + 2φ log n)` is false for `i` close to `ξ`. The definition of `ξ` gives only
     `2^{-i+1} I/χ > 2^{ξ-i+1} φ log n`, i.e. `ψ > 2φ log n` at `i = ξ`. Fix: define `ξ` with a
     larger constant (e.g. `16φχ log n`) and run the clean-up with that parameter.
   * `‖W R^{(i)}‖ ≤ χ(∑Y_j + ∑Z_j) < χψ/2` only gives `≤ 2^{-i} I + χ/2`, because of the ceiling.
   * `E[∏ e^{4Y_j}] ≤ ∏ E[e^{4Y_j}]`: the FKG sketch is not a proof. Negative association
     (Dubhashi–Ranjan) gives it.
   * `E[Z_j] ≤ 1/(8e)` uses that `𝒜(χ, mχ)` fails with probability `≤ 1/(mχ)` and that
     `mχ ≥ 8e`. That is fine, since `χ ≥ 54`.
   * The Chernoff estimate for `Z` needs the form `(eμ/R)^R`. The `R ≥ 6μ` form does not apply
     (`ψ/4 < 6ψ/(8e)`). Fine.
4. **Step bound.** `alg1Time_le` proves the displayed estimate exactly, for `I ≥ 0`, `f(mχ) ≥ 0` and
   `m ≥ 1`. The paper's `= 2 f(mχ) I + O(log n · f(mχ) + …)` drops a factor `χ = Θ(log m)` in the
   middle term. The correct form `O(log n · log m · f(mχ))` matches the introduction's
   `O(I log m + log n log² m + log² n log m)`. This is a typo (R3) and is not formalized as an
   asymptotic statement.
5. **Typos.**
   * `2^{-ψ/4} ≤ 2^{ξ-i+2φ log n}` (sign).
   * `2^ξ/2^i` should be `2^i/2^ξ` in Claim 2 and in the sum after it.
   * "one of the last `φ log n` executions" vs. `⌈φ⌉ + 1` in Algorithm 1.
   * "`(W · R_j^{(i+1)})(e)`" should be `R_j^{(i-1)}`.
   * "for each constant `φ ≥ 0`": `φ = 0` makes `ξ` undefined. We require `φ > 0`.
6. **Modelling choices.**
   * *Algorithm 1.* We use `max ψ 1` delay values so that the delay type is never empty; this is
     irrelevant whenever the loop runs.
   * *Black box.* `𝒜` is any `PMF`-valued function returning a subset of its input.
   * *Delays.* All packets get delays, but only those of remaining packets matter. This is
     equivalent to drawing delays for the remaining packets only.

## Theorem 20 (local clocks)

7. **The paper's chain at `λ = ln m/m` is wrong (proof).** It claims
   `(1 − (1−1/m)λ)^{m−1} < 1/e^{ln m} ≤ λ`.
   * The first inequality is false for every `m`: the left side is
     `≈ m^{-(1-1/m)²} > 1/m`.
   * For `m = 4` the left side even exceeds `λ` (`paper_step_fails_four`). For `m ≥ 5` it is
     `< λ`, which is all the proof needs.
   * *Repair.* Our proof removes the factor `1 − 1/m`: the window length `k` can be taken
     arbitrarily large. The criterion becomes `(1 − λ)^{m−1} < λ`, which holds at `λ = ln m/m`
     for all `m ≥ 4` (`key_ineq`).
8. **Strictness (proof gap).** "`γ`-competitive" with `γ = m/(2 ln m)` and OPT rate `1/2` asks
   for stability at all `λ < ln m/m`. The paper shows instability only for `λ ≥ ln m/m`, which
   is not a contradiction. We repair this by continuity: for `m ≥ 4` there is `λ < ln m/m` with
   `(1−λ)^{m−1} < λ` (`exists_rate_below`, `theorem_20`).
9. **`m = 2, 3` (claim inside the proof false; statement unestablished).** The proof claims that
   for `λ ≥ ln m/m` no acknowledgement-based local-clock protocol is stable on the network of
   Figure 1. This is false for `m = 2, 3`. The protocol "send each packet in its arrival slot" needs
   no clock, and makes the long link's opportunities i.i.d. with probability `(1−λ)^{m−1}`. That is
   `> λ` at `λ = ln m/m` (`rate_lt_opp_two/three`), so the long link's queue is stable
   (`immediate_stable_two/three`). Short links have empty queues.
   * Theorem 20 quantifies over all networks of size `m`. So for `m ≤ 3` it is not refuted, only
     unestablished by this proof.
   * By R1 a false claim inside a proof of a statement that may still be true counts as a proof
     issue. Our `theorem_20` covers `m ≥ 4`.
   * `m ≤ 3` (two or three links, competitive ratio `≈ 1.37–1.44`) is a corner of the
     asymptotic statement. We do not count it towards the verdict (R2-like), and record it here.
10. **Model of "acknowledgement-based with only a local clock" (modelling choice).** The paper argues
    informally. We model the *consequence* of this restriction on the network of Figure 1:
    * *Short links.* Each runs as an independent process in its own local time, because its
      feedback is always "success". We take an arbitrary `LinkExec` on its own probability space,
      combined by `Measure.pi`.
    * *Clocks.* The clocks differ by adversarial switch-on times `d_i`. Before switch-on a link is
      silent, and its arrivals start at switch-on. This is the paper's "delaying the start of the
      protocol at a link does not change this behavior".
    * *Long link.* It is arbitrary: any process on a probability space mapping measure-preservingly
      to the short links' randomness. Successful transmissions are only allowed in silent slots.
      This is *more* general than the paper (which needs only ack-based).
    * *Not formalized.* We do not formalize general protocols as functions of histories, nor the
      reduction from them to this model.
11. **Stability ⇒ window throughput.** The paper asserts that stability yields `k` with at least
    `(1−1/m)λk` expected transmissions in every window of length `k` (with a typo: `(1−1/m)λ`). We
    prove `λk − B` for expected queue length `≤ B` (`window_tx`), via queue conservation. This
    needs a uniform bound on the expected queue, which is the stability notion of Section 4.1
    ("expected queue lengths bounded at any time").
12. **Randomized offsets → deterministic offsets.** The paper picks random delays. We average over
    all offset vectors in `[k]^{m−1}` and conclude that some deterministic vector makes every
    long-link execution unstable (contradiction with a uniform bound over the finitely many
    vectors).
13. **Positive side (global clock, immediate protocol).** These are modelled directly as the
    long link's queue Markov chain (`Queue.slot`; TDMA frame = a slot without plus a slot with an
    opportunity), not derived from the general model:
    * *Slot order.* Arrival first, then a possible transmission.
    * *TDMA.* `Queue.tdma_stable` covers the long link. A short link under TDMA is the same queue
      with the slots swapped (not separately formalized).
14. **Not formalized.**
    * The competitive-ratio definition itself; the statement is phrased via rates.
    * The SINR realization of Figure 1 (short links never interfere with each other or get
      interfered with; the long link is blocked by any short transmission). We take these
      interference rules as the network's definition.

## Not formalized at all

* Section 4 (Theorem 3, Lemma 4–7, Theorem 8).
  * Lemma 7 has visible typos: `Pr[Δ = −1] = 1` should be `q`, and `Pr[Δ = iH+1] = a/(1−b)·b^i`
    does not give a probability distribution. These were not checked further.
* Theorem 11; Section 6 corollaries; Section 7 (Lemma 15, 17, Theorem 19).
