# Differences between the formalization and the paper

Paper: R. Vacus, I. Ziccardi, *Minimalist Leader Election Under Weak Communication*, PODC 2025,
DOI 10.1145/3732772.3733559; formalized version arXiv 2502.12697v2 (numbering follows it).

## Modelling choices

1. **Randomness as a coin field.** The only random transition of BFW is `W• → B•`. The execution
   `exec G init c` is a deterministic function of a coin field `c : ℕ → V → Bool` (`c t v` is used
   only if `v ∈ W•` hears nothing in round `t`). All results of Section 3 are proved **for every coin
   field**, i.e. for every rule deciding when `W•` goes to `B•`, as the paper remarks.
   For the probabilistic results the coins are i.i.d. `Bernoulli(p)` indexed by `ℕ × V`
   (`coinMeasure p = Measure.infinitePi …`). Faithful.
2. **Initial configuration.** Section 3 and all theorems assume Eq. (2) (`GoodInit`: every node is
   waiting and some node is a leader), which is more general than the paper's "all nodes in `W•`"
   (`initAll`, `goodInit_initAll`).
3. **Graph and diameter.** `G` is a finite connected `SimpleGraph`. Wherever the paper uses the
   diameter `D`, the theorems take any `D` with `dist(a, b) ≤ D` for all `a, b` (so `D = diam G` is a
   special case). For Theorem 3 this covers `p = 1/(D'+1)` for any upper bound `D' ≥ diam`
   (part of the paper's remark on constant-factor approximations; approximations from below are
   not covered).
4. **Paths** (Definition 4) are `SimpleGraph.Walk`s; the flow along a path (Definition 5) is
   `walkFlow`. `N_t^beep(v)` counts beeps in rounds `0..t`, as in the paper.
5. **"With high probability"** is instantiated as probability `≥ 1 − 1/n²`, with explicit
   constants; the paper writes `1 − n^{−Ω(1)}`.

## Changed constants / proofs

6. **Theorem 2, time bound — different proof, explicit constants.** The paper derives the
   `O(D² log n)` bound from an anti-concentration estimate (Theorem 13 via a Berry–Esseen theorem for
   mixing sequences, Lemmas 14, 15, 17). We do not formalize those lemmas. Instead, for two leaders
   `u, v` the triple `(phase u, phase v, N(u) − N(v))` follows a pair chain. For that chain we use
   `M = Δ + h(x_u) − h(x_v)`, which is a martingale, plus a bounded corrector. Together they give a
   Lyapunov function with drift exactly `−1` (`lyap_drift`). Hence the chain leaves the strip
   `|Δ| ≤ D` within `T₂ = ⌈(D+2)²(1+2p)³/(p(1−p)) + 4⌉` steps with probability `≥ 1/2`
   (`alive_half`). Result: `P(no single leader from round k·T₂ on) ≤ n²·2^{−k}` (`theorem2_time`).
   With `k = ⌈6 ln n⌉` this is `≤ 1/n²` (`theorem2_whp`). Same order `O(D² log n)` as the paper.
7. **Theorem 2, almost-sure part — separate argument.** Proved via windows of `2D+3` rounds with
   an explicit good event of probability `Q = (1−(1−p)^{D+1})(1−p)^{2D+3} > 0`
   (`theorem2_tail`, `theorem2_ae`). See also item 11.
8. **Theorem 3 — window `2D+3` instead of `2D+1`, explicit constants.** With `p = 1/(D+1)`,
   `D ≥ 1`: `P(no single leader from round k(2D+3) on) ≤ n²(127/128)^k` (`theorem3`). The leader
   is unique from round `(2D+3)·⌈512 ln n⌉` on with probability `≥ 1 − 1/n²` (`theorem3_whp`).
   The longer window repairs the gap in item 10.
9. **Lemma 7** is proved for one edge and summed along the walk (`flow_succ`, `lemma7`). The
   paper's regular-expression case analysis is not needed. Lemma 9 is proved in the paper's
   strong form (`lemma9_strong`: some leader has the maximal beep count), Lemma 12 in a stronger
   form (item 10).

## Issues in the paper

10. **Lemma 12 is stated too weakly for Lemma 19, and Lemma 19's case analysis has gaps (proof gap;
    Lemma 19 as stated fails for `D ≤ 2`; Theorem 3 is true).** Lemma 12 says only "`v` beeps in some round `s ≤ t + dis(u,v)`".
    Lemma 19 needs `t < s`, which the proof of Lemma 12 does give. We prove
    `t < s ≤ t + dis(u,v)` (`lemma12`). In Lemma 19:
    * `P(A) = (1−p)^{2(D+1)}` ignores the state of `v`'s chain in round `t`: if `v ∈ B•_t`, then
      `P(A) = 0`.
    * In the case `N_t(u) = N_t(v)`, a beep of `u` "between `t` and `t+D+1`" may be the beep in
      round `t` itself. That beep is already counted in `N_t(u)`, so `N_s(u) > N_s(v)` does not
      follow.
    * Typo: "`N_s^beep(u) ≥ 1`" should read `N_s(u) > N_s(v)`.
    * The window `2D+1` is too short for small `D` when the lemma is read per configuration in
      round `t` (as its proof does). On `K₂` (`D = 1`), with both nodes in `B•` in round `t = 1`
      (both coins `true` in round 0), both stay leaders up to round `t + 3 = t + 2D + 2` for every coin
      field, so the probability of an elimination before round `t + 2D + 1` is 0. On the path `u–w–v`
      (`D = 2`, `w` eliminated in round 2), the earliest elimination is in round `t + 2D + 1`, not
      before it. Both are formalized for every coin field (`lemma19_fails_K2`: both nodes are leaders
      up to round 4; `lemma19_fails_P3`: both endpoints are leaders up to round 5). The averaged form
      `P(A_{t+2D+1} | A_t) ≤ c` used in the proof of Theorem 3 is not refuted by this, but it is
      not proved either.

    Our repair takes the coins of `u` in rounds `t+2..t+D+2` and those of `v` in rounds
    `t..t+2D+2`, with window `2D+3` (`elim_window`).
11. **Theorem 2's "almost surely" is not proved in the paper (proof gap; the statement is true).**
    The proof shows only `P(two leaders in round AD² log n) ≤ n^{−2}`, and a w.h.p. bound for each
    `n` does not give probability 1. One needs, e.g., Lemma 17 for every `A`, plus the monotonicity
    of the leader set. We prove the a.s. statement (`theorem2_ae`).
12. **Lemma 14 is stated for the wrong chain (imprecise statement).** It is stated for
    `N_t^{(u)}`, i.e. the chain started in `W`. The proof uses `E N_t = π_B t` and Theorem 13, which
    both need the stationary start. The lemma is applied (in Lemma 15) only to the stationary copy
    `Ñ`.
13. **Proof of Lemma 14: a false intermediate inequality (proof gap; the conclusion is true).** It
    claims `P(Z ≥ E(Z) + k(2p+1)) ≥ 1/2` for `Z` binomial and `1 ≤ k ≤ δ√t`. A binomial's median is
    within 1 of its mean, so this probability is `< 1/2`. Numerically, for `p = 1/2` and `k = 1` it
    is `0.333` at `t = 100` and `0.447` at `t = 1000`. The argument works with any constant
    `c ∈ (0, 1/2)` in place of `1/2`.
14. **Lemma 17's use of Lemma 15 does not match (proof gap; the statement is true).**
    * Conditioning on the past fixes `δ = N^u − N^v ∈ [−D, D]`. The event `E_k` then needs a bound
      on `P(|Δ + δ| ≤ D)` for a shifted interval, but Lemma 15 bounds only `P(|Δ| < d)`.
    * The chain rule needs conditioning on `E_1 ∩ … ∩ E_{k−1}`, not on `E_{k−1}` alone.
    * Lemma 15 holds only for "`d` large enough", while `D` may be small (`D = 1` on cliques).

    All three are routine to fix: use Theorem 13 with a constant `c`, condition on the whole past,
    and use windows of length `max(D, d₀)²`. We avoid these lemmas entirely (item 6).
15. **Lemma 21 is off by one (typo).** It states `P(Σ_{i≤n} W_i ≥ k) = P(Bin(k,p) ≤ n)`. For
    geometric `W_i` counting trials, the right side should be `P(Bin(k−1,p) ≤ n−1)`. Example:
    `n = 1`, `k = 2`, `p = 1/2` gives `1/2` vs `3/4`. The proof's sentence ("in `k` trials, fewer than
    `n` successes") is also off by one (it describes `ΣW_i > k`). The form used in Lemma 14 is correct (`P(ΣW_i ≤ x) = P(Bin(x,p) ≥ m)`).
16. **Claim 16** (the coupled copies differ by at most one beep before they meet): checked by
    exhaustive search over the pair states; no issue. Not needed for our proof.

16a. **Typo in the Discussion (§5).** It speaks of "the upper bound in Theorem 1". There is no
    Theorem 1; Theorem 2 is meant.

## Remarks of the paper made precise

17. "No deterministic algorithm can break symmetry on certain graphs" (§1.3). We prove it for
    **every** graph with two distinct nodes and no isolated node (`deterministic_impossible`): all
    nodes stay in the same state forever.
18. The assumption `V ⊆ W_0` in Eq. (2) is necessary for Lemma 9 (§5 Discussion; it is not stated
    as a lemma in the paper). On a triangle where all three nodes are leaders, one in `B•` and one
    in `F•`, every leader is eliminated by round 3 for every coin field (`triangle_no_leader`).

## Not formalized

19. Theorem 13, Theorem 20 (Berry–Esseen for mixing sequences), Lemmas 14, 15, 17 and 21. Our
    proof of the Theorem 2 time bound does not need them (item 6).
20. Table 1 and the related-work comparisons, and the Discussion's conjecture that the
    `O(D² log n)` bound is tight up to `log n`.
