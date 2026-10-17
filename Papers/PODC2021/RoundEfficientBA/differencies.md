# Differences between the formalization and the paper

Fitzi, Liu-Zhang, Loss. *A New Way to Achieve Round-Efficient Byzantine Agreement.* PODC 2021,
DOI 10.1145/3465084.3467907 (proceedings version, 8 pages; no arXiv version).

## Errors in the paper

1. **False statement (for `n ≥ 3t + 2`, `t ≥ 1`): Lemma 3.2, Corollary 3.3, and Corollary 3.8 for `t < n/3`.**
   The expansion step `Prox_s → Prox_{2s-1}` uses the "dominant slot" threshold `n - 2t`. When
   `n ≥ 3t + 2`, the `≥ n - t` honest echoes can be split between two adjacent slots with fewer than
   `n - 2t` honest echoes on each. Then one Byzantine echo decides whether a receiver satisfies a
   condition, and grades can differ by more than one.
   * One step (Lemma 3.2): `n = 5`, `t = 1`, honest `Prox_5` outputs `(0,1),(0,1),(0,2),(0,2)`. A
     receiver that also gets the Byzantine echo `(0,2)` outputs grade 3. A receiver that gets nothing
     from the Byzantine party outputs grade 0 (`lemma32_counterexample`).
   * Whole protocol (Cor. 3.3): `n = 5`, `t = 1`, honest inputs `0,0,0,1`, 3 rounds. The honest
     `Prox_9` outputs are `(0,2),(0,2),(0,3),(0,0)`, which is not a Proxcensus
     (`paper_cor33_counterexample`).
   * BA (Cor. 3.8, `κ = 3`): in the same run the coins `2, 3, 4` out of `[1, 8]` split the honest
     parties. The error is `3/8` instead of `2^{-3}` (`paper_cor38_counterexample`).
   Using the largest admissible `t = ⌊(n-1)/3⌋` does not help: the counterexample already uses it
   (`n = 5`, `t = 1`). **Fix:** threshold `t + 1`, which equals `n - 2t` iff `n = 3t + 1`. With this
   threshold we prove Lemmas 3.1–3.2 (`expand_isProx`), Corollary 3.3 (`proxProtocol_spec`) and
   Corollary 3.8 for `t < n/3` (`ba_third`) for every `n > 3t`. For `n = 3t + 1` this is the paper's
   protocol verbatim (`expand_isProx_paper`, `proxProtocol_spec_paper`, `ba_third_paper`).

2. **Proof gap whose statement is false in the paper's adversary model: Corollary 3.8 for `t < n/2`.**
   The proof runs the coin flip in parallel to round 3 of `Prox_5`. It justifies this with "after
   round 2 of `Prox_5`, the slot-pair where the honest parties lie is already fixed", and claims a
   failure probability of `1/4` per iteration. The coin is revealed during round 3: its shares are sent
   in that round, and the paper's coin is uniform only "until the first honest party has queried
   CoinFlip". A strongly rushing adaptive adversary (§2.1) can therefore pick its round-3 corruptions
   after seeing the coin.
   Counterexample (`coin_parallel_adaptive_attack`): `n = 5`, `t = 2`, inputs `1,1,0,0` for parties
   `0..3`, party `4` corrupted from the start.
   * Round 1: party 4 sends a share on `1` to everybody, so everybody has `S¹ = {1}`.
   * Round 2: party 4 sends its `ω` share to party 0 only. So only party 0 forms `Ω` on `1`.
   * Round 3, coin `4`: no further corruption. Party 0 outputs `(1,2)` and the others `(1,1)`, which
     the coin `4` separates.
   * Round 3, coin `3`: the adversary corrupts party 0 when it sends its round-3 message, and forwards
     `Ω` to party 1 only. Then party 1 outputs `(1,1)` and parties 2, 3 output `(⊥,0)`, which the coin
     `3` separates.
   The failure probability is `≥ 1/2`. For `κ = 2` (one iteration, 3 rounds) this contradicts the
   claimed `2^{-κ} = 1/4`.
   **What holds** (`coin_parallel_static`): if the corruptions do not depend on the coin (e.g. a static
   adversary), the per-iteration failure probability is `≤ 1/(2r-2)` for `Prox_{2r-1}`, any `r ≥ 3`
   (`1/4` for `Prox_5`). This holds even when the adversary picks its last-round *messages* after
   seeing the coin. The proof is a two-run version of Lemma 3.6 (`two_run_cons`).
   *Not formalized:* the composition of `κ/2` iterations. Informally, the attack repeats in every
   iteration (mirrored on value 0 when needed) as long as one unused corruption is left per
   iteration. So for `t ≳ κ/2` we expect the error to be about `2^{-κ/2}` instead of `2^{-κ}`. We did
   not check this.

3. **Proof gap, statement true (`n = 3t + 1`): proof of Lemma 3.2, case `b = 0`, `gᵢ = gⱼ = 1`.**
   The proof says that "there are `n - 2t` honest parties in `S_{yᵢ,0}`". A count `≥ n - 2t` gives
   only `n - 3t` honest parties. The proof then adds counts taken from the views of two different
   receivers, which see different Byzantine echoes. The correct argument compares the honest parts:
   each receiver's pair condition gives `≥ n - t - f` honest echoes of its value, and
   `2(n - t - f) > n - f`. Our proof (`expand_isProx`, case `zero_receiver`) is organized differently:
   honest outputs lie on one "ray" at two adjacent levels, and every receiver's grade lies in an
   interval of length one determined by the honest outputs alone (`ray_receiver`).

4. **Imprecision (harmless) in the proof of Lemma 3.2, first bullet.** "Any honest `Pⱼ` has
   `gⱼ = gᵢ`" holds only with maximality of `gᵢ` plus the fact that some slot has `≥ n - 2t` honest
   echoes, which again needs `n = 3t + 1`.

5. **Typos / notation.**
   * The pseudocode of `Prox_{2r-1}` (§3.3.2) writes `s` for the number of rounds `r`
     ("Rounds j = 3 to s", "for j = 1 to s - 1", `S^{s-j}`, `Ω^{s-j+1}`).
   * Proof of Theorem 3.7 (validity): "`c ≤ 2G + 1 - j = s - 1`" should be `2G + 1 - r`. Here
     `r = s mod 2`, which clashes with `r` = rounds elsewhere.
   * Corollary 3.8, `t < n/3`: one should use `Prox_{2^κ+1}` (Cor. 3.3), i.e. `s = 2^κ + 1`.

## Modelling choices

* **`t < n/3` protocol.** CSLib's synchronous lock-step model (`Cslib.Byzantine.LockStep`) on the
  complete network, with a static deterministic adversary: arbitrary messages per round, sender and
  receiver, so rushing is covered. Corruption in the paper is adaptive and strongly rushing. For the
  deterministic Proxcensus phase this is equivalent to statically corrupting the parties that are
  corrupted by the end, since they may behave honestly until then. The coin of Cor. 3.8 is drawn after
  the `κ` rounds. The adversary may corrupt further parties after seeing it (`Hc` in `ba_third`),
  which only shrinks the honest set.
* **Expansion step.** We state it abstractly (`expand_isProx`): an honest receiver's counting
  function sees every honest echo and at most `f` further echoes.
* **Output rule.** The paper's loop, with later conditions overwriting earlier ones, is formalized as
  "the satisfied condition of largest grade" (`topLevel` / `outGrade`). This is equivalent because the
  grades increase along the loop. When several values satisfy the top condition, the least is taken.
  The paper leaves this open: "∃z". All proofs use only that the chosen value satisfies the condition,
  so they hold for every choice. In `Expansion.lean` the value is in fact unique (`ray_upper`).
* **Default value at grade 0.** The paper uses `0`. The expansion uses the party's own old value
  (needed for validity of `Prox_1 → Prox_1`, irrelevant otherwise). The `t < n/2` protocol takes a
  parameter `d₀`. For an odd number of slots the value of a grade-0 output carries no information.
* **Domain.** `D` is a finite type with a linear order (for the tie-break). Theorem 3.7 and the BA
  results are binary (`Bool`), as in the paper.
* **`t < n/2` protocol.** Our own model, since CSLib's `Auth` tokens are single signatures:
  * Unique threshold signatures are ideal. A set of valid certificates `{(v, Σ)}` is represented by
    the set of certified values. Invalid certificates are dropped by the receiver (`I_k`), so the
    adversary sends only certificates it can form (`consSig`, `consOm`). It can form one from the shares
    sent by parties honest in the relevant round plus the keys of everyone corrupted so far.
  * In round 1 a corrupted party may give shares on a *set* of values to a receiver. This is more
    power than the paper's single `(v, σ)`, so the positive results are only stronger. The attack uses
    singletons.
  * Corruption is adaptive at round granularity (`A.cr q` = first corrupted round). In that round the
    party's messages are replaced, which is the strongly rushing replacement. "Honest" means honest at
    the end.
  * Parties send to themselves, so their own sets grow. `ω` is sent iff `S¹ = {own input}` (line 5).
    `Ω` is formed only on the own input (lines 11–12).
* **Coin.** An ideal uniform coin in `[1, s-1]` (`PMF.uniformOfFintype`). For Cor. 3.8 `t < n/2` the
  adversary strategy is a family of adversaries indexed by the coin that agree before round `r`
  (`PrefixAgree`).
* **Termination.** Decisions are made exactly in round `r` (`decides_proxProtocol_iff`,
  `TerminatesBy`).

## Not formalized

* Communication complexities (`O(rn²)`, `O(κn²)`); they follow by inspection.
* The multivalued extension (Turpin–Coan, `+2` / `+3` rounds).
* The composition of `κ/2` iterations in Cor. 3.8 for `t < n/2`, and the implementations of the coin
  and of threshold signatures (random oracle, unforgeability). These are idealized, as in the paper.
* Protocols mentioned only for the full version (proxcast for `t < n`, `√s`-round Proxcensus).
