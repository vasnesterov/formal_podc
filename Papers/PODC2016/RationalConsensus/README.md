# Rational Consensus — PODC 2016

Joseph Y. Halpern, Xavier Vilaça. *Rational Consensus.* PODC 2016. DOI
[10.1145/2933057.2933088](https://doi.org/10.1145/2933057.2933088). Formalized version: arXiv
[2005.10141](https://arxiv.org/abs/2005.10141) v1 (full version with proofs and Algorithm 1); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 1 (no fair consensus protocol is an `f`-Nash equilibrium,
`f ≥ 1`) is correct for `n ≥ 2` and fully verified. Theorem 2 (`σ_cons` solves fair consensus whenever
`f + 1 < n`) is verified for Algorithm 1 as written, but its proof has a gap (the first crash-free round
need not seem clean), and the forwarding step of round `f + 1` is under-specified: under the prose reading
("forward the shares *received*") the theorem fails for `n = f + 2` and for `f = 0`. Theorems 3 and 4
(π-Nash and sequential equilibrium) were not formalized.

## Mistakes in the paper

* **The forwarding step of round `f + 1` is under-specified, and one reading breaks Theorem 2.** Line 20
  of Algorithm 1 has agent `i` send `j` the tuple `(y_li)_{l ≠ j}`. The index set includes `l = i`, so `i`
  also sends its own share `y_ii = q_i(i)`. Elsewhere the pseudocode writes `l ≠ j, i` when it wants to
  exclude `i` (lines 6, 28). But line 14 defines `y_ij` only for `j ≠ i`, and the prose says `i` forwards
  "the secret shares `y_li` it received in round 1 from each agent `l`", which excludes the own share
  (though the next sentence, "this enables `j` to compute the polynomials `q_i^t`", again needs it).
  The proof needs the own share: "since there are at least `n − f ≥ 2` nonfaulty agents, `i` and `j` will
  be able to interpolate `q_l`" counts `l` itself as a forwarder when `l` is nonfaulty. So does the
  hypothesis `f + 1 < n`. We formalize line 20 as written, with `y_ii = q_i(i)`, and prove Theorem 2 for
  every `f + 1 < n`. Under the received-only reading, Theorem 2 is false. Take `n = f + 2`, let agents `0`
  and `1` be nonfaulty, and let the other `f` agents crash at the start of round 1 without sending
  anything. Agent `0` then holds a single point of agent `1`'s degree-1 polynomial, cannot interpolate
  `x_1[t]` and decides `⊥`. The same holds for `f = 0` and any `n ≥ 2`: round `f + 1 = 1` comes before
  any share is received. Under that reading Theorem 2 holds only for `f ≥ 1`, `n ≥ f + 3`. This is an
  under-specified algorithm; the intended protocol is correct. (`Cons.theorem_2`; received-only reading:
  `Cons.theorem_2_receivedOnly_false`, `Cons.sigmaCons_receivedOnly_not_fair_3_1`,
  `Cons.theorem_2_receivedOnly`)
* **Proof of Theorem 2: the first crash-free round need not "seem clean".** The proof claims that if `m*` is the
  first round in which no agent crashes, then `NC_{m*} = NC_{m*−1}` for every nonfaulty agent, so `m*` seems
  clean. This is false. Take `n = 4`, `f = 2`: agent 1 crashes in round 1 sending nothing, and agent 0 crashes
  in round 1 sending only to agents 2 and 3. Round 2 is crash-free, but agent 0's crash is detected only in
  round 2, so `NC_2 ≠ NC_1` (`not_clean_example`). The first seemingly clean round can therefore come *after*
  `m*`, where the paper's agreement argument does not apply. Agreement still holds, by a different argument.
  Suppose two nonfaulty agents disagree about agent `l` at threshold `m`. Then `l` crashed in round `m`, and
  there is a chain of agents crashing in rounds `m+1, …, f+1` that carried the information to one of them only.
  Add the `m − 1` agents that make rounds `1, …, m−1` look unclean, and there are `f + 1` crashes. This is a
  proof gap; the statement is true. (`crash_chain_of_disagree`, `ghost_agree`)
* **Theorem 1 needs `n ≥ 2`.** With a single agent, "decide your own preference" is fair consensus and an
  `f`-Nash equilibrium for every `f`. This is degenerate. (`theorem_1_false_of_card_eq_one`)
* **Minor slips.**
  * The secret sharing is under-specified: no field is given, and shares are evaluated at agent identifiers
    `0, …, n−1`, so agent `0` receives `q_i^t(0) = x_i[t]`, the secret itself. We use `𝔽_p` with a prime
    `p > n` and evaluation points `j + 1`.
  * The pseudocode's status-report update (lines 29–30) compares against the record from the *start* of the
    round, so the result depends on the order in which messages are processed: a later, larger report can
    overwrite a smaller one. We take the minimum, which is what the proof assumes.
  * Check 8 says "more than `f` crashes", then "(i.e., `f` or more agents …)".
  * In Theorem 1's proof, the step "there is a failure pattern `F²` where `i` fails after the decision"
    silently uses countable additivity: decisions happen at unbounded times, but with positive probability by a
    fixed time `T`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous rounds, complete network, reliable channels, crash failures. This is CSLib's `SyncCrash`/`LockStep`
  model. A context is the preferences plus a failure pattern: crash round, and the agents reached in the
  crashing round. At most `f` agents crash.
* Strategies: a profile is a history-based protocol whose input is *(preference, private seed)*. The seed
  vector `ω : P → Ω` is drawn from an arbitrary probability measure `μ`; Theorem 1 holds for every `Ω` and `μ`.
  This covers behavioural strategies: the paper's per-information-set randomization is drawn from the seed.
  A deviation `deviate σ τ i` replaces only agent `i`'s protocol and uses `i`'s own seed.
* Decisions are `Option Bool` (`none` = `⊥`). An agent's decision is its first one, so Integrity holds by
  construction. Outcome: consensus on `b` iff every nonfaulty agent decides `b`.
* Utilities ("care only about consensus"): `β₀ i > β₁ i > β₂ i`. Expected utility is taken over the seeds,
  for each fixed context (ex post). An `ε`–`f`-Nash equilibrium requires a measurable outcome, and only
  deviations with a measurable outcome are compared. This only makes "not an equilibrium" harder to prove.
* Fair consensus: agreement, termination and validity hold almost surely in every context with `≤ f` crashes.
  Fairness: `P(consensus on b) ≥ #{nonfaulty agents preferring b} / n`.
* `σ_cons` (Theorem 2), with seeds drawn uniformly: per `t ≤ f`, a secret `x[t] ∈ {0..n−t−1}` and the slope of
  a line over `𝔽_p`. It sends status reports (earliest known crash round of every agent), round-1 values and
  shares, and forwards shares in round `f+1` (flag `selfShare`: `true` = line 20 as written, own
  share included; `false` = the received-only reading). The decision is the paper's: first seemingly clean round,
  `NC`, `t`, `S = Σ x_l[t] mod (n−t)`, then the `(S+1)`-st highest identifier. We do not model the random
  "signatures" `z`, reporter identities, and consistency checks 1–3, 5–7: they never fire when nobody
  deviates, and Theorem 2 is only about such runs.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (`n ≥ 2`) | `theorem_1` | `Theorem1.lean` |
| Theorem 1 fails for `n = 1` | `theorem_1_false_of_card_eq_one` | `Theorem1.lean` |
| Theorem 2 (Algorithm 1 as written), all `f + 1 < n` | `Cons.theorem_2` | `Theorem2.lean` |
| Theorem 2, received-only reading of line 20: **false** for `n = f + 2` and `f = 0` | `Cons.theorem_2_receivedOnly_false` | `Theorem2.lean` |
| Theorem 2, received-only reading, `f ≥ 1`, `n ≥ f + 3` | `Cons.theorem_2_receivedOnly` | `Theorem2.lean` |
| Proof of Thm 2: nonfaulty agents agree on `NC` and the first clean round | `ghost_agree`, `crash_chain_of_disagree` | `Records.lean` |
| Proof of Thm 2: "`m*` seems clean" is false | `not_clean_example` | `Records.lean` |
| Proof of Thm 2: fairness of the random dictator | `Cons.seedMeasure_dictator` | `Fairness.lean` |
| Instances (`n = 3, f = 1`); Thm 1 applied to `σ_cons` | `Cons.sigmaCons_fair_3_1`, `Cons.sigmaCons_receivedOnly_not_fair_3_1`, `Cons.sigmaCons_not_nash` | `Examples.lean` |

**Not formalized.** Lemma 1, Theorem 3 (π-Nash equilibrium under "supports reachability" and uniformity) and
Theorem 4 (sequential equilibrium). They need conditional expectations over information sets, the full
consistency-check machinery of `σ_cons`, and a case analysis over all deviations.

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Cons.sigmaCons_fair_3_1` shows the hypotheses of Theorem 1 are satisfiable, and the `n = 1`
profile satisfies `SolvesFairConsensus`. The model comes from CSLib `Cslib.Computability.Distributed.SyncCrash.Model`.
CSLib candidate: the game layer in `Model.lean` (profiles, contexts, outcome, `IsEpsNash`, and the simulation
lemmas `hist_ignore`/`status_congr_silent`).
