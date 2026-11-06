# Minimalist Leader Election — PODC 2025

Robin Vacus, Isabella Ziccardi. *Minimalist Leader Election Under Weak Communication.* PODC 2025.
DOI [10.1145/3732772.3733559](https://doi.org/10.1145/3732772.3733559). Formalized version: arXiv
[2502.12697](https://arxiv.org/abs/2502.12697) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** All main results hold: Theorem 2 (for every fixed `p ∈ (0,1)`, BFW elects a unique leader
almost surely, and w.h.p. within `O(D² log n)` rounds), Theorem 3 (`O(D log n)` rounds for `p = 1/(D+1)`) and Section 3
(flow conservation, Ohm's law, and "there is always a leader"). The paper's anti-concentration proof of the
`O(D² log n)` bound fails at Lemmas 14 and 17, and we replace it by a new martingale/Lyapunov proof. Lemma 19 (used for
Theorem 3) is false as stated for small `D` (`K₂`, `P₃`), Theorem 3 still holds with a window of `2D+3` rounds, the
"almost surely" claim needed a separate argument, and knowing `D` only up to a constant factor was checked only for
upper bounds on `D`.

## Mistakes in the paper

### 🔧 Lemma 19 (elimination within `2D+1` rounds, used for Theorem 3)
Lemma 19, read per configuration in round `t` as its proof does, is false for small `D`: on `K₂` (`D = 1`) with both
nodes in `B•` in round `t = 1`, neither node loses leadership before round `t + 4 > t + 2D + 1`, whatever the coins
(`lemma19_fails_K2`, `lemma19_fails_P3`).

**Impact.** Theorem 3 is true: with windows of `2D+3` rounds it holds with explicit constants
(`elim_window`, `theorem3`, `theorem3_whp`).

**Details.** On the path `u–w–v` (`D = 2`) the earliest elimination is in round `t + 2D + 1`, not before it. Both
counterexamples hold for every coin field and are proved in Lean. The proof of Lemma 19 has two further gaps:
* `P(v does not beep by itself in [t, t+2D+2]) = (1−p)^{2(D+1)}` is wrong if `v` is in `B•` in
  round `t` (the probability is then 0).
* In the case `N_t(u) = N_t(v)`, the "self-beep of `u` between `t` and `t+D+1`" may be the beep
  in round `t` itself. That beep is already counted, so `u` does not get ahead of `v`.

**Repair.** We shift the coin windows (coins of `u` in rounds `t+2..t+D+2`, all coins of `v` in rounds `t..t+2D+2`)
and use windows of length `2D+3`. Theorem 3 then holds with explicit constants:
`P(no single leader from round k(2D+3) on) ≤ n²(127/128)^k` (`elim_window`, `theorem3`, `theorem3_whp`).

### ✏️ Slips
- Lemma 12 as stated only gives a beep of `v` in some round `s ≤ t + dis(u,v)`, but Lemma 19 needs it to happen *after*
  round `t`. Its proof does give `s > t`, and we prove that version (`lemma12`).
- Lemma 14 is stated for the chain started in `W`, but its proof needs the stationary start. The lemma is applied (in
  Lemma 15) only to the stationary copy. Not formalized; our proof of Theorem 2 does not use it.
- Lemma 21 should read `P(Σ_{i≤n} W_i ≥ k) = P(Bin(k−1,p) ≤ n−1)`, not `P(Bin(k,p) ≤ n)`: for `n = 1`, `k = 2`,
  `p = 1/2` the two sides are `1/2` and `3/4`. The form used in Lemma 14 is correct. Not formalized.

### Typos
- Proof of Lemma 19, case `N_t(u) = N_t(v)`: "`N_s^beep(u) ≥ 1`" should read `N_s(u) > N_s(v)`.
- Proof of Lemma 17, last bound: the display ends with `≤ 1/n²`, while the lemma states `n^{−4}`, which is what the
  chosen `A` gives and what the union bound in Theorem 2 uses.
- The Discussion (§5) cites "Theorem 1", which does not exist; Theorem 2 is meant.

## Proof gaps (statements true)

### 🛠️ Lemma 14 (proof of the anti-concentration bound)
The proof of Lemma 14 claims `P(Z ≥ EZ + k(2p+1)) ≥ 1/2` for a binomial `Z`, which is false.

**Impact.** This is the first step of the chain (Lemmas 14, 15, 17) behind Theorem 2's `O(D² log n)` bound. The
statements are true. We prove that bound by a different route (see "The formalization") (`theorem2_time`,
`theorem2_whp`).

**Details.** A binomial's median is within 1 of its mean, so the probability in Lemma 14's proof is `< 1/2` (for
`p = 1/2`, `k = 1`, `t = 100` it is 0.333). Any smaller constant works instead; this repair is not in Lean.

### 🛠️ Lemma 17 (proof of `P(σ_{u,v} > AD² log n) ≤ n^{−4}`)
The proof applies Lemma 15, which bounds `P(|Δ| < d)`, where it needs a shifted interval `|Δ + δ| ≤ D`.

**Impact.** The gap is fixable and the statement is true, but that repair is not in Lean; the `O(D² log n)` bound is
saved by the same different route (`theorem2_time`, `theorem2_whp`).

**Details.** The proof also conditions only on `E_{k−1}` instead of the whole past, and it uses Lemma 15's
"`d` large enough" although `D` may be 1.

### 🔧 Theorem 2 ("almost surely")
The proof only bounds the probability of two leaders in round `AD² log n` by `n^{−2}`, and that does not give
probability 1.

**Impact.** Statement true; proved by a separate argument (`theorem2_ae`, `theorem2_tail`).

**Repair.** Each window of `2D+3` rounds has a good event of positive probability `(1−(1−p)^{D+1})(1−p)^{2D+3}`, and
that event eliminates one of any two given leaders. (`theorem2_ae`, `theorem2_tail`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous beeping model on a finite connected `SimpleGraph`; anonymous, uniform nodes. A
  listening node hears a beep iff some neighbour beeps.
* BFW has 6 states: a phase `W/B/F` and a leader bit (Figure 1).
* No failures, no adversary. The only randomness is the `W• → B•` coin. The execution is a
  deterministic function of a coin field `c : ℕ → V → Bool`.
* Section 3 is proved **for every coin field**, i.e. for every rule deciding `W• → B•`, as the
  paper remarks.
* Probabilistic results use i.i.d. `Bernoulli(p)` coins on `ℕ × V` (`Measure.infinitePi`).
  Events are tracked by the finite set of coins they depend on (`Determined`); events on
  disjoint coin sets are independent.
* Initial configuration: Eq. (2), i.e. all nodes waiting and at least one leader. This is more
  general than the paper's all-`W•` start.
* `D` is any upper bound on all distances (the diameter, or more).
* Definition 1 is `UniqueFrom T`: a fixed node is the only leader in every round `t ≥ T`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Claim 6 (Eqs. 3–11) | `claim6_3` … `claim6_11` | `Flow.lean` |
| Lemma 7 (conservation of flow) | `lemma7` (`flow_succ` for one edge) | `Flow.lean` |
| Corollary 8 (Ohm's law) | `corollary8`, `ohm_edge` | `Flow.lean` |
| Lemma 9 (always a leader) + Claim 10 | `lemma9`, `lemma9_strong` (`M⋆_t ≠ ∅`), `claim10` | `Flow.lean` |
| Lemma 11 | `lemma11` | `Flow.lean` |
| Lemma 12 (strengthened: `t < s`) | `lemma12` | `Flow.lean` |
| Lemma 19 (deterministic core) | `elim_window` | `Convergence.lean` |
| Theorem 2, almost surely | `theorem2_ae` | `Main.lean` |
| Theorem 2, `O(D² log n)` w.h.p. | `theorem2_time` (`≤ n²2^{−k}` at round `k·T₂`), `theorem2_whp` | `Theorem2.lean` |
| Theorem 3 (`p = 1/(D+1)`, `O(D log n)` w.h.p.) | `theorem3`, `theorem3_whp` | `Main.lean` |
| Lemma 19 per configuration: false for `D = 1, 2` | `lemma19_fails_K2`, `lemma19_fails_P3` | `Remarks.lean` |
| §1.3: randomness is necessary | `deterministic_impossible` | `Remarks.lean` |
| §5: Eq. (2) is needed (cycling waves, no leader) | `triangle_no_leader` | `Remarks.lean` |

Our proof of the `O(D² log n)` bound is new. While `u` and `v` are both leaders, the triple
`(phase u, phase v, N(u) − N(v))` follows a 9-phase pair chain (`pchain_couple`). Write
`a = 1 + 2p`. The quantity `M = N(u) − N(v) + h(x_u) − h(x_v)`, with `h(W) = 0`, `h(B) = −2p/a`,
`h(F) = −p/a`, is a martingale. Add a corrector `k(x_u) + k(x_v)` and put

  `g = ((D+2)² − M² + k(x_u) + k(x_v))·a³ / (2p(1−p))`.

Then `g` has drift exactly `−1` (`lyap_drift`), so `T·P(|N(u) − N(v)| ≤ D for T steps) ≤ g ≤ G_max`
(`alive_bound`). By Lemma 11 the leaders `u`, `v` can coexist only while
`|N(u) − N(v)| ≤ D`. Hence one of them is eliminated within
`T₂ = ⌈(D+2)²(1+2p)³/(p(1−p)) + 4⌉` rounds with probability `≥ 1/2`. A union bound gives a unique
leader from round `⌈6 ln n⌉·T₂` on with probability `≥ 1 − 1/n²`.

**Not formalized.** The anti-concentration machinery: Theorem 13, Theorem 20 (Berry–Esseen for
mixing sequences) and Lemmas 14, 15, 17, 21. Our Theorem 2 proof does not need it. Also not
formalized: the Discussion's tightness conjecture. The remark after Theorem 3 that the proof "can be easily
generalized" to a constant-factor approximation of `D` is open: Lean covers upper bounds on `D` only, and
approximations from below were not examined.

**Trust.** No `sorry`. All theorems in the table use only the axioms `propext`, `Classical.choice`
and `Quot.sound`.
* Non-vacuity: `theorem2_ae_example` instantiates Theorem 2 on the triangle with `p = 1/2` from
  the paper's initial configuration.
* `goodInit_initAll` shows that the paper's start satisfies Eq. (2).
* `lyap_drift` is an exact identity, checked case by case over the 9 phase pairs.
* The probability space is Mathlib's `Measure.infinitePi` of `Ber(true, false, p)`.

The model is self-contained in this folder. CSLib's stone-age model (`Cslib.StoneAge`) has
deterministic transitions, so the randomized BFW protocol does not fit it; the deterministic
protocols of the remark on randomness (`DetProtocol`) are stone-age algorithms run under the
synchronous schedule (`DetProtocol.toStoneAge`, `DetProtocol.run_succ`).

The i.i.d. coin fields (`coinMeasure`), `Determined` events, independence of events on disjoint coin
sets, and partition along fibres are shared code in CSLib, `Cslib/Probability/CoinField.lean`
(namespace `Cslib.Probability`).
