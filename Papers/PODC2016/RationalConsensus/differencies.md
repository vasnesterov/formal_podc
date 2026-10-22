# Differences between the formalization and the paper

Paper: Halpern, Vilaça, *Rational Consensus*, PODC 2016; arXiv 2005.10141 v1.

## Errors found in the paper

1. **Under-specified forwarding step in round `f + 1` (Theorem 2).** Line 20 of Algorithm 1 sends
   `(y_li)_{l ≠ j}`; the index set includes `l = i` (the pseudocode writes `l ≠ j, i` when it excludes `i`,
   lines 6 and 28), i.e. the agent's own share `y_ii = q_i(i)`, which line 14 never defines (it sets `y_ij`
   only for `j ≠ i`). The prose instead says the agent forwards the shares "it received in round 1", which
   excludes the own share. The proof ("at least `n − f ≥ 2` nonfaulty agents" suffice to interpolate `q_l`)
   and the hypothesis `f + 1 < n` need the own share. We model line 20 as written (`selfShare = true`,
   `y_ii := q_i(i)`) and prove Theorem 2 for every `f + 1 < n` (`Cons.theorem_2`). Under the received-only
   reading (`selfShare = false`) Theorem 2 is false when `n = f + 2` or `f = 0`: with exactly two nonfaulty
   agents and the others crashing silently in round 1, or with `f = 0` (a single round, so nothing has been
   received when shares are forwarded), some nonfaulty agent holds one point of a degree-1 polynomial and
   decides `⊥` (`Cons.theorem_2_receivedOnly_false`, `Cons.sigmaCons_receivedOnly_not_fair_3_1`); it holds
   for `f ≥ 1`, `n ≥ f + 3` (`Cons.theorem_2_receivedOnly`).
2. **Proof gap in Theorem 2.** The claim "the first round `m*` in which no agent crashes seems clean to every
   nonfaulty agent" is false (`not_clean_example`, `n = 4`, `f = 2`). Agreement on the decision data is proved
   by a different counting argument (`crash_chain_of_disagree`, `ghost_agree`).
3. **Theorem 1 needs `n ≥ 2`** (`theorem_1_false_of_card_eq_one`); the paper does not state it.
4. Secret sharing evaluates at identifiers `0, …, n − 1`, so agent `0` receives the secret `q(0)` itself. No
   field is specified. We use `ZMod p` with a prime `p > n` and evaluation points `j + 1`.
5. Status-report update (lines 29–30) is order-dependent, as it compares with the start-of-round record; we take
   the minimum of all reports. Check 8 says both "more than `f`" and "`f` or more".

## Modelling choices

* **Execution model.** CSLib `SyncCrash` (`LockStep` on the complete graph): a history-based protocol, with
  history = list of inboxes. Sent messages and own decisions are recomputable from (input, history), so they are
  not stored. A failure `(i, m, A)` is `crash i = some m`, `reach i = A`. The paper's convention "if `m > 1` then
  `A ≠ ∅`" is not imposed. `(i, m+1, ∅)` and `(i, m, N)` give the same messages; Theorem 1's proof handles both
  (its chain of failure patterns wraps around through `(i, m+1, ∅)`). A crashed agent's state is `⊥` from its
  crash round on. It does not decide then (`status` uses `SyncCrash.state`).
* **Decision time.** Decisions are read at the beginning of each round from the history so far. The paper's
  decision in the update phase of round `m` is our decision at time `m`.
* **Randomization.** Each agent has a private seed from a common space `Ω`; the seed vector is drawn from an
  arbitrary probability measure `μ` on `P → Ω`. Theorem 1 is proved for every `Ω`, `μ`, so it covers behavioural
  strategies and even correlated seeds. A deviation must use the same seed space. This restricts the deviations
  and only strengthens "not a Nash equilibrium".
* **Measurability.** Bochner integrals are junk on non-measurable functions. `IsEpsNash` therefore requires the
  profile's outcome to be AE-measurable in every admissible context, and compares only deviations with an
  AE-measurable outcome. In Theorem 1 the profitable deviation has the same outcome function as `σ` in another
  context, so it is measurable.
* **Outcome / utilities.** Outcome = consensus on `b` iff all nonfaulty agents decide `b`; otherwise no
  consensus (also when every agent is faulty). Decisions of faulty agents do not affect the outcome. The
  paper's "deciding ⊥ guarantees no consensus" holds for nonfaulty agents. Utilities: `β₀ i > β₁ i > β₂ i`,
  per agent, independent of the context. The paper's "agents care only about consensus" is exactly this
  assumption.
* **Fair consensus.** Agreement, termination and validity are required almost surely (the paper does not say
  "surely" or "a.s." for randomized protocols; a.s. is the weaker hypothesis, so Theorem 1 is stronger).
  Validity applies to every agent that decides while alive; `⊥` is not a value. Integrity holds by
  construction (first decision). All conditions are required only in contexts with at most `f` crashes.
* **`f`-Nash** is ex post: expectation over the seeds, for every fixed admissible context. `ε`–`f`-Nash is
  defined (`IsEpsNash`); `IsNash = IsEpsNash 0`.

## `σ_cons` (Theorem 2)

* Seeds: uniform over `Fin n → Seed n f p`, i.e. independent uniform per agent. Per `t ≤ f`: the secret
  `x[t] ∈ Fin (n − t)` and the slope in `ZMod p` of the line `q^t`. (The paper's `zᵐ_ij` and `z` are not
  modelled.)
* Messages: `sr` (for each agent, the earliest known crash round; `⊤` = believed alive), `pref` (round 1),
  `share` (round 1: the receiver's shares), `fwd` (round `f + 1`: forwarded shares). The reporter identity in
  status reports is not modelled.
* Decision (lines 46–56) as in the paper: `NC_m = {l | m < SR[l]}`, first `m ∈ [1, f+1]` with
  `NC_m = NC_{m−1}`, `t = n − |NC_m|`, `S = Σ x_l[t] mod (n − t)`, the `(S+1)`-st highest identifier. When
  something is missing (no seemingly clean round, `t > f`, a value or a second share missing) the agent decides
  `⊥`. Interpolation uses the own round-1 share and the share forwarded by the least agent that forwarded
  one. Consistency of further shares is not checked.
* Consistency checks 1, 2, 3, 5, 6, 7 are not modelled; check 4 survives only as "a second share point
  exists", and check 8 as `t ≤ f`. When nobody deviates the checks never fire in the paper's protocol, and
  Theorem 2 is only about such runs. Our protocol decides only at the end of round `f + 1`; the paper decides
  `⊥` as soon as an inconsistency is detected, which matters only for deviations.
* `selfShare` flag: `true` = line 20 as written (own share included, `y_ii := q_i(i)`); `false` = the
  received-only reading of the prose.
* Theorem 2 needs the extra parameter `p` (a prime `> n`) and the instance `Fact (f < n)` (implied by
  `f + 1 < n`; needed to state the seed measure).

## Not formalized

Lemma 1, Theorem 3 (π-Nash equilibrium: "supports reachability", uniformity, the deviation case analysis) and
Theorem 4 (sequential equilibrium); the naive protocol of §3.2.1 and its gain estimate.
