# Optimal EBA with Omission Failures — PODC 2023

Kaya Alpturer, Joseph Y. Halpern, Ron van der Meyden. *Optimal Eventual Byzantine Agreement Protocols
with Omission Failures.* PODC 2023. DOI [10.1145/3583668.3594573](https://doi.org/10.1145/3583668.3594573).
Formalized version: arXiv [2305.06271](https://arxiv.org/abs/2305.06271) v1 (full version with
appendix); numbering follows it. Targets: §6 (Prop. 6.1, Thm. 6.3, Prop. 6.4, Thms. 6.5–6.6, Cor. 6.7).

**Verdict: ⚠️ Minor statement issues.** Correctness of `P0` (Prop. 6.1) and the concrete results hold
for `t ≤ n − 2`. Under that hypothesis we prove that `P^min` and `P^basic` implement `P0`
(Thms. 6.5, 6.6), that `P0` is safe (Prop. 6.4) and that both protocols are optimal (Cor. 6.7). Two
statements are false as written. Prop. 6.4 fails with the paper's own definition of a 0-chain, and
Cor. 6.7 fails for `t = n − 1`. Both have evident repairs. The general Theorem 6.3 ("safe ⇒ optimal" in
every EBA context) has a gap in its proof. We prove it only with an extra hypothesis that holds in the
two concrete contexts. The general claim is neither proved nor refuted.

## Mistakes in the paper

* **Proposition 6.4 is false with the paper's definition of 0-chain.** Condition (c) of a 0-chain
  asks that `i_{m'}` *knows that `i_{m'−1}`* has just decided 0. In the minimal context an agent only
  learns that *somebody* just decided 0, not who. Take `n = 3`, `t = 0`, no failures and preferences
  `0, 1, 1` (the same failure-free example works for every `n ≥ 3`, `t ≤ n − 2`). At time 1 agent 2 has `jd = 0`. In the run with preferences `1, 0, 1` it has the same
  local state, so it does not know that agent 0 decided. Hence it has received no 0-chain. Yet every
  run in which it has this local state contains a preference 0. This breaks safety condition (1) for
  `P^min`, the unique implementation of `P0` there. The same example refutes the main-text claim that
  "`K_i(⋁_j jdecided_j = 0)` holds iff `i` receives a 0-chain". The proof of Prop. 6.1 reaches the
  paper's definition by an invalid step: from `K_i(⋁_j jdecided_j = 0)` it concludes
  `K_i(jdecided_j = 0)` for some `j`. The intended notion is "`i_{m'}` knows that *some* agent has just
  decided 0". With this repaired definition Prop. 6.4 holds, and Thm. 6.3 with the paper's definition
  still follows. Statement-level, borderline (see differencies.md).
  (`Counterexamples.prop_6_4_lit_false`, general `n ≥ 3`, `t ≤ n − 2`: `prop_6_4_lit_false_gen`;
  repaired: `prop_6_4_min`, `prop_6_4_basic`)
* **Corollary 6.7 is false for `t = n − 1`.** It is stated for all of `γ_min,n,t`, i.e. for every
  `t < n`. It is derived from Thms. 6.5/6.6, which assume `t ≤ n − 2`. Take `t = n − 1`. A 0-chain
  reaching time `n − 1` would need `n` agents besides the undecided agent. So `P0` already decides 1
  at time `n − 1 = t`, one round before `P^min` does. `P^min_{n−1}` implements `P0`, is an EBA
  protocol, and strictly dominates `P^min` (failure-free all-1 run: decisions at `n − 1` vs `n`). So
  `P^min` is not optimal. Missing hypothesis, statement-level.
  (`Counterexamples.cor_6_7_min_false`, `cor_6_7_min_false'`)
* **Theorem 6.3: gap in the proof; proved here with an extra hypothesis.** The proof takes the first
  round `k` in which `P` and a strictly dominating `P'` differ, for an agent `i` that "may be faulty".
  It has three gaps.
  - **The agent `i` may be faulty.** Safety (1) yields a run where all preferences are 1 and `i` has
    the same state. The contradiction ("`P'` decides 0 against Validity") needs `i` to be nonfaulty
    there. EBA imposes nothing on faulty agents.
  - **A case is missing.** The case "`P` decides at `k`, `P'` does not" is never treated.
  - **Repeated decisions.** "All agents have the same state up to time `k − 1`" fails if `P'`
    performs `decide` again after deciding. The spec allows this, and faulty agents may do it freely.

  We prove Thm. 6.3 for one-shot competitors under one extra hypothesis, `NFConsistent`: an
  undecided agent's local state also occurs, with the same preferences, in a run where that agent is
  nonfaulty. The hypothesis holds in `γ_min` (trivially) and in `γ_basic` (by swapping the roles of
  `i` and a nonfaulty agent). So Cor. 6.7 (`t ≤ n − 2`) is fully established for one-shot competitors.
  Whether Thm. 6.3 holds in *every* safe EBA context is open. Agents that can detect their own
  faultiness are the risk. (`Context.thm_6_3`, `Context.thm_6_3_lit`)
* **Proof gaps with true statements.**
  - *Prop. 6.4, γ_basic.* The proof builds the all-1 run with "the same adversary". In `γ_basic` this
    fails: an agent that decided 0 in `r` sends `(init,1)` in `r'` and changes the counts `#1`. We
    also silence each faulty agent from the round in which it decides 0. (`ZeroBiased.allOnes`)
  - *Prop. 6.4, safety (2).* The role-swap argument "details left to the reader" is replaced by
    explicit chain runs.
  - *Thm. 6.6.* The proof does not show `¬K_i(⋁_j jdecided_j = 0)` in the decide-1 case; it follows
    from safety (1).
  - *Typos in the proof of Thm. 6.5.* `I` should be the system of `P^min`, not of `P0`; `jdecided`
    should be `deciding`; "(Note that `t′ = m`.)".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous rounds, `n` agents `Fin n`, message passing.
* Failures: sending omissions `SO(t)`. A failure pattern `(N, F)` fixes the nonfaulty agents
  (`|Agt \ N| ≤ t`) and, for every round and pair, whether the message is delivered. Only faulty
  agents omit. Self-messages may be omitted too, as in the paper. The adversary is arbitrary.
* No randomness; protocols are deterministic.
* An EBA context (`Context`) is an information-exchange protocol plus a failure model. Local states
  are `(⟨time, init, decided, jd⟩, x)`, and the core part is updated exactly as §5 prescribes.
  Messages have a tag 0/1/none (the sets `M⁰`, `M¹`, `M²`).
* A run is determined by its initial global state (`Config`: pattern, preferences, initial extra
  state). Knowledge `K_i` quantifies over all admissible configurations and times; `Knows` is CSLib's
  `System.K` (`knows_iff_K`).
* `P0`, "implements", the EBA spec, domination and optimality are the paper's definitions.
  Domination is literal, quantifying over all decision times.
* Theorem 6.3 restricts competitors to one-shot protocols, which do nothing after deciding.
  Cor. 6.7 is proved in this sense; `cor_6_7_min_false'` refutes the paper's unrestricted sense.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Prop. 6.1 (all `P0` implementations are EBA, decide within `t+1` rounds, Validity for all) | `Context.prop_6_1` | `Prop61.lean` |
| — all implementations of `P0` generate the same runs | `Context.Implements.state_eq` | `Prop61.lean` |
| Thm. 6.3 (safe ⇒ optimal), with `NFConsistent`, one-shot competitors | `Context.thm_6_3`, `Context.thm_6_3_lit` | `Thm63.lean` |
| Thm. 6.3 in `γ_min` / `γ_basic`, `t ≤ n−2` (all implementations) | `thm_6_3_min`, `thm_6_3_basic` | `Main.lean` |
| Prop. 6.4 (repaired 0-chains), `n − t ≥ 2` | `prop_6_4_min`, `prop_6_4_basic` | `Main.lean` |
| Prop. 6.4 with the paper's 0-chains: **false** (`n=3,t=0`; every `n ≥ 3`, `t ≤ n−2`) | `Counterexamples.prop_6_4_lit_false`, `prop_6_4_lit_false_gen` | `Counterexamples.lean` |
| Thm. 6.5 | `thm_6_5` (general: `Min.pmin_implements`) | `Main.lean`, `MinCtx.lean` |
| Thm. 6.6 | `Basic.thm_6_6` | `BasicCtx.lean` |
| Cor. 6.7, `t ≤ n−2` | `cor_6_7_min`, `cor_6_7_basic` | `Main.lean` |
| Cor. 6.7 for `t = n−1`: **false** | `Counterexamples.cor_6_7_min_false`, `cor_6_7_min_false'` | `Counterexamples.lean`, `Main.lean` |
| safety (1) in contexts where decided agents are silent | `Context.ZeroBiased.allOnes`, `Implements.safe_one` | `AllOnes.lean` |
| undecided agents cannot detect their faultiness | `Min.nfConsistent`, `Basic.nfConsistent` | `MinCtx.lean`, `BasicCtx.lean` |

**Not formalized.** Section 7 (`P1`, full information, weak safety, Thms. 7.5–7.7, Prop. 7.9) and
Section 8 (bit/round counts). Cor. 6.7 for `P^basic` with `t = n − 1` is presumably also false (same
phenomenon) but is not formalized.

**Trust.** No `sorry`; all listed theorems use only `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity:
* `pmin_pbasic_eba`: `P^min` and `P^basic` are EBA decision protocols.
* The safety and `NFConsistent` hypotheses of `thm_6_3` are discharged in both contexts.
* `cor_6_7_min_false` exhibits a strictly dominating one-shot competitor, so the optimality notion is
  not trivial.

Knowledge is bridged to `Cslib.Knowledge.System`. The rest of the model is paper-specific.
