# Round-Efficient BA via Proxcensus — PODC 2021

Matthias Fitzi, Chen-Da Liu-Zhang, Julian Loss. *A New Way to Achieve Round-Efficient Byzantine
Agreement.* PODC 2021. DOI [10.1145/3465084.3467907](https://doi.org/10.1145/3465084.3467907).
Formalized version: the 8-page proceedings version (no arXiv version; the IACR ePrint full version 2021/814 was not accessible to us); numbering follows the proceedings.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Both headline protocols fail as stated, though the `t < n/3` one is
fixed by a one-line change.
* **`t < n/3`.** The Proxcensus expansion (Lemma 3.2, Cor. 3.3), and hence the `(κ+1)`-round BA
  (Cor. 3.8), is wrong for every `n ≥ 3t + 2` with `t ≥ 1`. With the threshold `t + 1` instead of `n - 2t` (the
  same thing when `n = 3t + 1`) everything is proved, including error `≤ 2^{-κ}`.
* **`t < n/2`.** The Proxcensus protocol (Lemmas 3.4–3.6) and Theorem 3.7 are correct. The `3κ/2`-round
  BA (Cor. 3.8) runs the coin in parallel to the last Proxcensus round. Against the paper's adaptive
  strongly rushing adversary this fails: one iteration errs with probability at least `1/2`, not `1/4`. Against
  coin-independent corruptions the claimed `1/4` holds.

## Mistakes in the paper

* **The `t < n/3` expansion is wrong for `n ≥ 3t + 2` (Lemma 3.2, Cor. 3.3, Cor. 3.8).** A party
  outputs the slot "between" or "on" two adjacent old slots. The choice depends on which slot has
  `≥ n - 2t` echoes. If `n ≥ 3t + 2`, the `≥ n - t` honest echoes may split so that neither slot
  reaches `n - 2t` without Byzantine help. Then one Byzantine echo moves a receiver by several grades.
  Example: `n = 5`, `t = 1`, honest `Prox_5` outputs `(0,1),(0,1),(0,2),(0,2)`. A receiver getting the
  extra echo `(0,2)` outputs grade 3. A receiver getting nothing from the Byzantine party outputs
  grade 0. The protocol then breaks down from honest inputs `0,0,0,1`. After 3 rounds the honest
  `Prox_9` outputs are `(0,2),(0,2),(0,3),(0,0)`, and the BA of Cor. 3.8 (`κ = 3`) fails for 3 of the
  8 coin values (error `3/8`, not `1/8`). Using the largest admissible `t` does not help:
  `n = 5, t = 1` already is that case. This is a false statement, easily repaired: with threshold
  `t + 1` we prove Lemmas 3.1–3.2, Cor. 3.3 and Cor. 3.8 (`t < n/3`) for all `n > 3t`. For
  `n = 3t + 1` that is the paper's protocol verbatim. (`lemma32_counterexample`,
  `paper_cor33_counterexample`, `paper_cor38_counterexample`; repaired: `expand_isProx`,
  `proxProtocol_spec`, `ba_third`)
* **"The slot pair is fixed after round 2" is false against the paper's adversary (Cor. 3.8,
  `t < n/2`).** To get 3 rounds per iteration, the coin is tossed in parallel to round 3 of `Prox_5`.
  The coin is revealed during that round (§2.2), so a strongly rushing adaptive adversary can corrupt
  a party in round 3 depending on the coin, and drop its round-3 forwarding. Example: `n = 5`, `t = 2`,
  inputs `1,1,0,0`, party 4 Byzantine. Party 4 makes everybody hold `Σ` on 1, and lets only party 0
  form `Ω` on 1.
  * Coin 4: nothing more happens. Party 0 outputs `(1,2)` and the others `(1,1)`, split by coin 4.
  * Coin 3: the adversary corrupts party 0 in round 3 and forwards `Ω` only to party 1. Party 1
    outputs `(1,1)` and parties 2, 3 output `(⊥,0)`, split by coin 3.

  One iteration fails with probability `≥ 1/2`. For `κ = 2` this contradicts Cor. 3.8's `2^{-κ}`.
  This is a proof gap whose statement is false in the paper's model. We prove the claim for
  coin-independent corruption (e.g. a static adversary), even when the adversary picks its round-3
  messages after seeing the coin. Tossing the coin after round 3 also works, but costs 4 rounds per
  iteration, i.e. `2κ` rounds and no gain over prior work. (`coin_parallel_adaptive_attack`;
  repaired: `coin_parallel_static`)
* **Proof gap, statement true (Lemma 3.2 for `n = 3t + 1`, case `b = 0`, `gᵢ = gⱼ = 1`).** The
  proof claims `n - 2t` *honest* parties in `S_{yᵢ,0}`, where only `n - 3t` are guaranteed. It then
  adds counts from two receivers' views, which differ in their Byzantine echoes. The correct
  argument compares honest counts. Our proof is organized differently. (`expand_isProx`)
* **Typos.**
  * The pseudocode of `Prox_{2r-1}` (§3.3.2) writes `s` for the number of rounds `r`.
  * In the proof of Theorem 3.7, `2G + 1 - j` should be `2G + 1 - r`, and this `r = s mod 2` clashes
    with `r` = rounds.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Proxcensus** (Def. 2.2) is a property `IsProx s x H out` of the honest outputs: grades in
  `[0, ⌊(s-1)/2⌋]`, validity, consistency for every ordered pair.
* **Theorem 3.7.** The binary slots and the extraction function `f` are the paper's. The coin is ideal
  and uniform on `[1, s-1]` (`PMF.uniformOfFintype`). It is independent of the Proxcensus outputs, and
  the adversary may corrupt more parties after seeing it.
* **`t < n/3`.** CSLib's synchronous lock-step model on the complete network: deterministic protocol,
  static Byzantine adversary sending arbitrary messages per round, sender and receiver (this covers
  rushing). Adaptive corruption reduces to static corruption of the finally corrupted parties, since
  the phase is deterministic. Values come from any finite linearly ordered domain.
* **`t < n/2`.** Our own model with ideal unique `(n-t)`-out-of-`n` threshold signatures:
  * Certificates are represented by certified values. The adversary can send exactly the
    certificates it can form, from shares of parties honest in that round plus the keys of the
    corrupted parties.
  * Corruption is adaptive, at round granularity: a party corrupted in round `k` has its round-`k`
    messages replaced.
  * For the coin-in-parallel analysis, an adversary strategy is a family of adversaries indexed by
    the coin that agree before the last round.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.2 (Proxcensus), §3.4 extraction | `IsProx`, `extract`, `extract_iff` | `Proxcensus.lean` |
| Theorem 3.7 (validity; error `≤ 1/(s-1)`) | `iter_validity`, `iter_error_le` | `Proxcensus.lean` |
| Lemmas 3.1–3.2, threshold `t+1` (any `n > 3t`) | `expand_isProx` | `Expansion.lean` |
| Lemmas 3.1–3.2 as stated, `n = 3t+1` | `expand_isProx_paper` | `Expansion.lean` |
| Lemma 3.2 for `n ≥ 3t+2`: **false** | `lemma32_counterexample` | `Expansion.lean` |
| Cor. 3.3 (`Prox_{2^r+1}` in `r` rounds), corrected / `n = 3t+1` | `proxProtocol_spec`, `proxProtocol_spec_paper` | `Protocol.lean` |
| Cor. 3.8, `t < n/3` (`κ+1` rounds, error `≤ 2^{-κ}`), corrected / `n = 3t+1` | `ba_third`, `ba_third_paper` | `Protocol.lean` |
| Cor. 3.3 / 3.8 (`t < n/3`) for `n = 5, t = 1`: **false** | `paper_cor33_counterexample`, `paper_cor38_counterexample` | `Counterexample.lean` |
| Lemma 3.4 (`Prox_{2r-1}`, `t < n/2`, `r ≥ 3`) | `Half.half_isProx` | `Half.lean` |
| Lemma 3.5 / Lemma 3.6 | `Half.half_validity` / `Half.two_run_cons` | `Half.lean` |
| Cor. 3.8, `t < n/2`, one iteration, coin-independent corruption (bound tight) | `Half.coin_parallel_static`, `Half.coin_parallel_validity`, `Half.coin_parallel_static_tight` | `HalfIter.lean` |
| Cor. 3.8, `t < n/2`, adaptive adversary: **false** | `Half.coin_parallel_adaptive_attack` | `HalfIter.lean` |

**Not formalized.**
* Communication complexity.
* The Turpin–Coan multivalued extension.
* The composition of the `κ/2` iterations for `t < n/2`.
* Implementations of the coin and of threshold signatures (idealized, as in the paper).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. All counterexample runs are checked by `decide` on the actual protocol definitions,
and their scenarios satisfy all hypotheses (corruption bound, validity of the adversary,
`PrefixAgree`). The non-vacuity of `coin_parallel_static` is shown by an explicit strategy for which
the bound `1/4` is attained (`coin_parallel_static_tight`). The `t < n/3` model is CSLib's `Cslib.Byzantine.LockStep`.
CSLib candidates: the Proxcensus specification and extraction (`Proxcensus.lean`) and the
echo-counting interface `hcnt`/`viewCnt` (`Expansion.lean`).
