# Dynamic Packet Scheduling in Wireless Networks — PODC 2012

Thomas Kesselheim. *Dynamic Packet Scheduling in Wireless Networks.* PODC 2012. DOI
[10.1145/2332432.2332487](https://doi.org/10.1145/2332432.2332487). Formalized version: arXiv
[1203.1226](https://arxiv.org/abs/1203.1226) v1; numbering follows it.

**Verdict: ❌ False claim.** **Theorem 1 is false.** Theorem 1 is the transformation (Algorithm 1)
that makes static `O(I log n)`-type algorithms scale linearly in `I`. There are instances that satisfy
its hypothesis on which Algorithm 1 fails with probability `> 0.98`, while the theorem claims
failure probability `≤ 1/n^φ`. The proof's halving step is off by a factor 2. Doubling the number of
delay classes probably repairs it, with leading constant `4 f(mχ)` instead of `2 f(mχ)`; we did not
formalize that repair. Theorem 20 (local clocks cost a factor `m/(2 ln m)`) holds for `m ≥ 4`
after a repair of its proof. For `m ≤ 3` the proof's network cannot give the bound, and the
statement is open there.

## Mistakes in the paper

* **Theorem 1 is false: Algorithm 1 does not halve the interference.** Iteration `i` gives every
  packet a uniform delay in `[ψ]`, `ψ = ⌈2^{-i+1} I/χ⌉`. The proof of Claim 2 asserts that a delay class
  has expected load `E[(W R_j)(e)] ≤ ‖W R^{(i-1)}‖/ψ ≤ χ/2`. In fact the bound is only `χ`. So a
  constant fraction of the classes exceeds `χ`, and `𝒜(χ, mχ)` gives no guarantee for them.
  Counterexample (in Lean):
  * Packet routing (`W = I`) on `m = 200` links, with `5100` packets per link. So `n = 1 020 000`
    and `I = 5100`.
  * `φ = 1`.
  * The static algorithm is "all or nothing". If `‖W·R_S‖∞ ≤ I'`, it sends all packets, one per
    link and step, in `I'` steps (`f ≡ 1`). Otherwise it sends nothing. It meets the hypothesis with
    success probability 1. The paper's own proof treats overloaded classes in exactly this way
    (`Y_j`).

  Then `85 < χ < 86`, `ξ = 1` and `ψ = 60`. On each link, a delay class gets `Bin(5100, 1/60)`
  packets, with mean `85`. With probability `≥ 1/25` this is exactly `86 > χ`, independently over
  the 200 links. So all 60 classes fail with probability `≥ 1 − 60·(24/25)^200 > 0.98`, and nothing
  is delivered. The clean-up runs `𝒜(2φχ log n, n)` then face interference `5100 > 2φχ log n` and
  deliver nothing either. The statement fails for `log = log₂` and for `log = ln`. This is a false
  numbered theorem about the paper's own algorithm. Section 4 is not touched when it starts from an
  `f(m)·I + g(m,n)` algorithm. But all corollaries that go through Algorithm 1 (Cor. 13, 14,
  Thm 19 + Sec. 7.2) are unestablished as written. They very likely hold up to constants
  (`theorem1_false`, `theorem1_false_ln`).
  The counterexample uses the freedom the hypothesis leaves on overloaded inputs: a static algorithm
  that still delivers most packets of an overloaded class would not fail here. But the theorem is
  claimed for every algorithm meeting the hypothesis, and the proof itself counts overloaded classes
  as lost. A Monte Carlo run on a single link with the all-or-nothing algorithm
  (`simulation/sim.py`, `φ = 1`) shows the failure is the typical behaviour, not an artefact of the
  chosen sizes. The failure probability is ≈ 0.57 for
  `n = 2376`, ≈ 0.78 for `n = 20000` and ≈ 0.99 for `n = 10⁵`. Once a round leaves more than half
  of the load, the next round's classes are overloaded on average, and the process stalls.
* **Other errors in the proof of Claim 2 / Theorem 1** (not formalized):
  * The claimed `ψ ≥ 4(ξ − i + 2φ log n)` is false for the last iterations. For `i = ξ`, the
    definition of `ξ` only gives `ψ > 2φ log n`.
  * `‖W R^{(i)}‖ ≤ χ ∑(Y_j + Z_j) < χψ/2` gives `2^{-i} I + χ/2`, not `2^{-i} I`, because of the
    ceiling in `ψ`.
  * The bound `E[∏ e^{4Y_j}] ≤ ∏ E[e^{4Y_j}]` needs negative association of the balls-into-bins
    loads; the FKG sketch does not show it.
* **Theorem 1's step bound drops a factor `log m`.** The displayed estimate
  `≤ 2 f(mχ) I + ξ f(mχ) χ + (⌈φ⌉+1) f(n) 2φχ log n` is correct (`alg1Time_le`). But
  `ξ f(mχ) χ = O(log n · log m · f(mχ))`, not `O(log n · f(mχ))`, since `χ = Θ(log m)`. The
  introduction states the correct `O(I log m + log n log² m + log² n log m)`, so this is a typo.
* **Theorem 20: the proof needs repairs, and for `m ≤ 3` it does not work.**
  * *Wrong bound.* The final chain `(1 − (1−1/m)λ)^{m−1} < 1/e^{ln m} ≤ λ` at `λ = ln m/m` is false.
    The left side is about `m^{-(1-1/m)²} > 1/m`. For `m = 4` it is even `> λ`
    (`paper_step_fails_four`).
  * *Endpoint not excluded.* The argument shows instability only for `λ ≥ ln m/m`. But
    `m/(2 ln m)`-competitiveness asks for stability only at `λ < ln m/m`, so the conclusion does not
    follow as written.
  * *Repair.* Let the window length `k` grow, so that the factor `1 − 1/m` disappears, and use
    continuity. We prove that for every `m ≥ 4` there is `λ < ln m/m` at which no protocol with local
    clocks is stable (`theorem_20`). The protocol may be arbitrary, and the long link even
    omniscient.
  * *`m = 2, 3`.* The intermediate claim "no local-clock protocol is stable for `λ ≥ ln m/m`" is
    false. Short links can send each packet in its arrival slot. Then the long link gets i.i.d.
    opportunities of probability `(1−λ)^{m−1} > λ`, so its queue is stable at `λ = ln m/m`
    (`immediate_stable_two`, `immediate_stable_three`). So the network of Figure 1 cannot prove
    Theorem 20 for `m ≤ 3`. There the theorem is unestablished, not refuted.
* **Typos.**
  * Proof of Theorem 20: the expected number of transmissions in a window of length `k` should
    be `≥ (1−1/m)λk`, not `(1−1/m)λ`.
  * Proof of Theorem 1: "`2^{-ψ/4} ≤ 2^{ξ−i+2φ log n}`" should have a minus sign. The factor
    `2^ξ/2^i` in Claim 2 should be `2^i/2^ξ`. "one of the last `φ log n` executions" should be
    `⌈φ⌉ + 1`. "for each constant `φ ≥ 0`" needs `φ > 0`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Theorem 1 (static, single hop).* An instance has links `E`, packets `P` (each on one link) and
  `W ∈ [0,1]^{E×E}` with `W_ee = 1`. A static algorithm is a black box
  `𝒜(I', n') : Finset P → PMF (Finset P)` that returns the undelivered packets. Its hypothesis is:
  it delivers everything with probability `≥ 1 − 1/n'` when `‖W R_S‖∞ ≤ I'` and `|S| ≤ n'`.
  Algorithm 1 is written verbatim as a `PMF`, with independent uniform delays and independent runs
  per class; `m = |E|` (`D = 1`). The base of `log` is a parameter; the counterexample covers 2
  and `e`. The step bound is the deterministic schedule length.
* *Theorem 20.* Discrete time; network of Figure 1 (`m − 1` short links, one long link); Bernoulli
  arrivals with expected rate `λ`.
  * Acknowledgement-based with only a local clock means: a short link's execution
    (transmissions, arrivals, deliveries, queue) is a process of its own randomness in local time.
    Its feedback is always "success". The links are independent (product measure). Link `i` is
    switched on at an adversarial global time `d_i` and is silent before. This is the paper's
    "delaying the start does not change the behaviour".
  * The long link is an arbitrary process on any probability space extending the short links'
    randomness. Its successes need all short links silent.
  * Stability = bounded expected queue length (Section 4.1).
  * The positive results (TDMA with a global clock, the immediate protocol) are stated for the
    long link's queue as a Markov chain. Its slot model: arrival, then possibly a transmission in
    the same slot.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (success probability): **false** (`log₂`, `ln`) | `theorem1_false`, `theorem1_false_ln` | `Counterexample.lean` |
| Theorem 1, hypothesis satisfiable / exact interference | `A0_good`, `X0_intfEq` | `Counterexample.lean` |
| Theorem 1, displayed step bound | `alg1Time_le` | `Time.lean` |
| Theorem 20 (repaired, `m ≥ 4`, strict) | `Theorem20.theorem_20` | `Theorem20.lean` |
| Theorem 20, core (any `K`, `(1−λ)^K < λ`) | `LocalClock.no_stable_long_link` | `LocalClock.lean` |
| Theorem 20, "stability ⇒ throughput in every window" | `LocalClock.LinkExec.window_tx` | `LocalClock.lean` |
| Theorem 20, paper's inequality fails at `m = 4` | `Theorem20.paper_step_fails_four` | `Theorem20.lean` |
| Theorem 20, `m = 2, 3`: local protocol stable at `λ = ln m/m` | `Theorem20.immediate_stable_two`, `immediate_stable_three` | `Theorem20.lean` |
| Theorem 20, global clock (TDMA) stable for `λ < 1/2` | `Queue.tdma_stable` | `Queue.lean` |

**Not formalized.**
* The repaired Theorem 1 (needs Chernoff bounds and negative association).
* Section 4 (Theorems 3, 8, Lemma 7), Theorem 11.
* The SINR applications (Section 6) and Section 7.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The large binomial estimate is checked by the kernel (`decide +kernel`, no
`native_decide`).
Non-vacuity:
* `A0_good` and `X0_intfEq`: the counterexample satisfies the hypotheses of Theorem 1.
* `immediateExec_rate` and `immediateExec_stable`: stable short-link executions of every rate
  exist (on CSLib's `coinMeasure`), so the hypotheses of `theorem_20` are satisfiable.

CSLib candidates (`-- CSLib candidate`):
* `card_filter_count_eq` (binomial counting).
* `Queue.stable_of_drift`.
* The `LocalClock` link-execution model.
