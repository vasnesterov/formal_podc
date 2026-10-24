# Differences between the formalization and the paper

Paper: R. Ostrovsky, W. Rosenbaum, *Fast Distributed Almost Stable Matchings*, PODC 2015,
arXiv 1408.2782v2. Scope: the deterministic algorithm ASM (Sections 2–4). The randomized variants
(Section 5, Appendix A) are not formalized.

## Model and definitions

1. **Preferences** (`Prefs`): duplicate-free preference lists, symmetric acceptability (`w ∈ P^m ↔ m ∈ P^w`), as in
   §2.1. We do not assume `|X| = |Y|`. Men and women are any finite types.
2. **Quantiles.** The paper says only that `Q_1` holds the `deg v / k` favourites, `Q_2` the next `deg v / k`, and
   so on; it does not say how to round. We use `q^v(u) = ⌈k · P^v(u) / deg v⌉ ∈ {1, …, k}` (`quant`). Then two
   items in the same quantile have ranks less than `deg v / k` apart (`lt_of_quant_le`). This is the only property
   of the rounding the proofs use.
3. **Blocking pairs / Definition 2.3.** `IsBlocking` follows §2.1: an unmatched player prefers every acceptable
   partner to being alone. `IsEpsBlocking` follows Definition 2.3. For an unmatched player it uses the convention
   `P^v(∅) = deg v + 1`, which the paper introduces only in the proof of Lemma 4.3.
4. **The woman's list `Q^w` is not stored.** In Step 4 a woman sends `REJECT` to *all* acceptable men in a lesser
   or equal quantile than her new partner. The paper sends it only to those still in `Q^w`. A man outside `Q^w`
   has already removed her, so the extra messages change no state. She never reads `Q^w` anyway: proposals come
   only from men in `Q^w`.
5. **Who runs the outer-loop test.** Algorithm 3 has every processor test `|Q| ≥ 2^i`. We let only the men test it,
   once at the start of iteration `i`. Women always take part, and so does every man as a receiver of `REJECT`
   messages: an inactive man still drops rejecting women and loses his partner if she rejects him. This is the
   only reading under which the algorithm makes sense, and §3.4 says so ("we only allow men … to participate").
   An inactive man does not set `A` and does not propose.
6. **MaximalMatching** (Theorem 2.7) is a black box `MMOracle`. It is an arbitrary function from bipartite graphs
   `G₀` to maximal matchings of `G₀` (Definition 2.6 in its "every edge has a matched endpoint" form), plus a
   round count. All theorems hold for *every* such oracle. This covers any deterministic subroutine, in particular
   [HKP]'s. The oracle sees only `G₀`; an adversary that also depends on the history is not covered. The analysis
   never uses this restriction.
7. **Parameters.** `k = ⌈8/ε⌉` (`kOf`; Algorithm 3 writes `8ε⁻¹`, the proof of Theorem 4.1 `⌈8/ε⌉`). `δ = ε/8`.
   The inner loop runs `ℓ = ⌈2δ⁻¹k⌉ = ⌈16k/ε⌉` times (`ellOf`). The outer loop runs `i = 0, …, ⌊log₂ n⌋`, where
   `n` is any bound on the degrees (the paper assumes `log n` is an integer). The general theorem `blocking_le`
   allows any `k ≥ 1`, any `ℓ` and any `L` with all degrees `< 2^{L+1}`.
8. **Granularity.** The state is updated once per `ProposalRound`, through local rules: `proposers` (step 1),
   `accepts` (step 2), the oracle (step 3), `rejects`/`womanUpdate`/`manUpdate` (steps 4–5). Each node's new state
   is a function of its own state, the one-bit messages from its neighbours and its own partner in `M₀`. There is
   no formal CONGEST semantics with message passing. In particular, the composition with a CONGEST
   implementation of the subroutine is not formalized.
9. **Running time (Theorem 4.7)** is proved for the explicit round count `asmRounds = (L+1) · ℓ · k · (3 + T)`:
   one round each for `PROPOSE`, `ACCEPT` and `REJECT`, plus `T` for the subroutine. Local steps cost 0 rounds.
   `ASM` run with a round counter (`stageC`: each `ProposalRound` adds `3 + mm.rounds`) computes the output of
   `asm` and ends with counter `asmRounds k ℓ L mm.rounds`, i.e. `ASM` makes exactly `(L+1) ℓ k` `ProposalRound`
   calls (`stageC_asm`); `theorem_4_7_run` bounds this counter for `ASM(P, ε, n)`. The asymptotic bound is
   explicit: `≤ 2610 (3 + c) ε⁻³ log⁵ n` for `0 < ε ≤ 1`, `n ≥ 2`, `T ≤ c log⁴ n`, with `log = ⌊log₂⌋`.

## Statements

10. **Theorem 4.1** is proved as stated, with the paper's constants (`theorem_4_1`). We also prove that the output
    is a matching in `E` (implicit in the paper). The general form is `k ℓ · #blocking ≤ 4ℓ|E| + 8k²|E|`
    (`blocking_le`).
11. **Lemma 4.4.** The paper assumes `δ ≤ 1/2` and gets `2δ/(1-δ) |E| ≤ 4δ|E|`. We prove `4δ|E|` directly for
    every `δ > 0` with `ℓ ≥ 2k/δ` (`lemma_4_4`); the core form is `ℓ · ∑_{m bad} |Q^m| ≤ 8k|E|`
    (`sum_bad_card_le`).
12. **Lemma 4.5** is stated as `ℓ · #(bad active men) ≤ 2k · #(active men)` (`lemma_4_5`), i.e. at most a
    `2k/ℓ ≤ δ` fraction. It holds for every iteration started in a reachable state with all `A` empty, as every
    iteration of ASM is.
13. **Lemma 4.6** is proved in the form used by the proof of Lemma 4.4: every `(2/k)`-blocking pair `(m, w)` has
    `m` bad and `w ∈ Q^m` (`lemma_4_2_4_6`). Hence the `(2/k)`-blocking pairs number at most `∑_{m bad} |Q^m|`
    (`card_strongBlocking_le`). The paper's "fewer than `2^i` for `m ∈ B_i`" depends on its definition of `B_i`
    (see item 16) and is not formalized separately.
14. **Lemma 3.1** is proved for one `ProposalRound`: a matched woman stays matched, and a change of partner is a
    strict improvement in quantile (`lemma_3_1`). **Lemma 3.2** says `k` `ProposalRound`s empty every `A`, from any
    reachable state (`lemma_3_2`).
15. **Lemma 4.3** holds for arbitrary partner functions (`lemma_4_3`). The paper's display (1) has the
    differences reversed: it should read `P^m(p(m)) − P^m(w) < 2 deg m / k` or `P^w(p(w)) − P^w(m) < 2 deg w / k`.

## Proofs

16. **Proof of Lemma 4.4 (gap; we use a different argument).** The paper charges every man who is bad at the end to
    the set `B_i` of men that "became bad during the `i`-th iteration and `|Q^m| < 2^i`". It then bounds
    `|B_i ∪ … ∪ B_log n|` with Lemma 4.5, which concerns only the men *active* in iteration `i`. A man can,
    however, become bad while inactive. He is matched when he leaves the active set, and later an active man
    displaces him (`Example.bad_while_inactive`: `k = 2`, `ℓ = 1`, 5 men, 5 women). Such men are not covered by
    the application of Lemma 4.5. The construction of the disjoint sets `H_i` and inequality (2) are also not
    justified as written. Our proof (`BadMen.lean`) charges a displaced inactive man to the *previous* iteration:
    - the number of unmatched men never increases;
    - so the inactive men displaced in iteration `j` number at most the bad active men at the start of
      iteration `j` (`matched_inactive_le`);
    - each such man has `|Q| < 2^j`;
    - the per-man potential "`2^j` if matched, `|Q|` otherwise" of an inactive man never increases
      (`reach_Fpot`, `inactive_mass`).
    This gives `∑_{m bad} |Q^m| ≤ ∑_i 2^{i+1} b_i` (`accounting`), where `b_i` is the number of bad active men at
    the end of iteration `i`. Lemma 4.5 and `∑_i 2^i |act_i| ≤ 2|E|` (`sum_pow_card_ac_le`) finish the proof. The
    constant matches the paper's final `4δ|E|`.
    In random searches with the paper's parameters (`k = 2`, `ℓ = 8`, up to 30 × 30 players) we found no run with
    such a displaced man. These parameters leave very few bad active men at the end of an iteration. The paper's
    argument does not rule such men out, though, and our proof does not need to.
17. **Proof of Lemma 4.5.** "The number of matched players (and hence matched men) can only increase … therefore
    the number of good players can only increase" is used for the *active* men. That step also needs: inactive men
    are never newly matched, and matched men = matched women in number. Then the number of matched active men
    cannot decrease, although individual active men may lose their partners (`card_matched_act_le`,
    `card_bad_act_le`). The counting of quantile rejections is formalized as the potential
    `∑_{m ∈ act} #(quantiles of Q^m) + ∑_w ψ_w` (`Pot`, `pot_prStep`, `pot_le`).
18. **Proof of Lemma 3.2** is formalized as an invariant: after `t` rounds every proposal `(m, w)` has
    `q^w(m) > t` (`prStep_quantile_gt`).
19. **Proof of Lemma 4.2** uses only two invariants of reachable states: a woman who rejected `m` is matched in the
    same or a better quantile, and a matched man's partner is in his best remaining quantile (`Inv.witness`,
    `Inv.p_best`). With our quantile rounding, `(1/k)`-blocking would already suffice.
20. **Typos.** In the proof of Lemma 4.2, "contradicts that `(m, w)` is `ε`-blocking" should say `(2/k)`-blocking.
    §3.1 says `Q_1` holds "`v`'s `deg v / k` favorite men" for every player `v`; for a man these are women.
    Theorem 2.7 states `log⁴ n` rounds; [HKP] give `O(log⁴ n)`.
