# Differences between the formalization and the paper

Paper: K. Alpturer, J. Y. Halpern, R. van der Meyden, *Optimal Eventual Byzantine Agreement Protocols
with Omission Failures*, PODC 2023 (arXiv:2305.06271v1). Scope: §§2–6 (Prop. 6.1 – Cor. 6.7).
Verdict rules refer to the verdict scale (R1–R6).

## Errors in the paper (statement level)

1. **Proposition 6.4 is false with the paper's Definition of 0-chain.**
   - *The definition.* Condition (c) reads "`i_{m'}` knows at the point `(r, m')` that `i_{m'−1}` has
     just decided 0" (rendered p. 8, to rule out extraction errors).
   - *Counterexample.* `γ_min,3,0`, implementation `P^min_1` (the unique implementation of `P0` up to
     reachable states, `Implements.state_eq`). Failure-free run with preferences `0,1,1`. At time 1
     agent 2 has state `⟨1, 1, ⊥, jd = 0⟩`. In the failure-free run with preferences `1,0,1` it has
     the same state while agent 0 did not decide, so it does not know that agent 0 just decided. It
     therefore has no 0-chain of length ≤ 1. Every run in which agent 2 has this state contains a
     preference 0, so safety condition (1) fails (`Counterexamples.prop_6_4_lit_false`). The
     example uses failure-free runs only, so it is not an artefact of `t = 0`: the same argument
     refutes Prop. 6.4 (literal chains) in `γ_min,n,t` for every `n ≥ 3`, `t ≤ n − 2`
     (`Counterexamples.prop_6_4_lit_false_gen`, implementation `P^min`).
   - *Repair.* With condition (c) replaced by "`i_{m'}` knows that *some* agent has just decided 0"
     (`IsZeroChain`; `i_{m'−1}` has just decided by (b)), Prop. 6.4 holds (`prop_6_4_min`,
     `prop_6_4_basic`). Agent 2 then has received a chain (`receivedChain_at_counterexample`).
   - *Call: ⚠️ by R3, borderline ❌.* The intended notion is recoverable from the paper itself:
     - "We will show that the second condition for deciding 0, that `i` knows that someone has just
       decided 0, holds iff `i` receives a 0-chain" (§6). This claim is false with the literal
       definition (same example) and true with the repaired one (`Implements.receivedChain_iff`
       together with `exists_chain`).
     - The proof of Prop. 6.1 derives the literal condition only through the invalid step
       `K_i(⋁_j jdecided_j = 0) ⇒ K_i(jdecided_j = 0)` for some `j`.
     - The proof of Prop. 6.4 never uses the knowledge clause.

     The fix is local: one clause of one definition. Against excusing it: the paper deliberately
     contrasts its definition with those of [1, 8]. Prop. 6.4 is not a headline result, so the worst
     case is ❌.
   - *Effect on Theorem 6.3.* None: safety with literal chains implies safety with repaired chains
     (`SafeWrt.of_lit`). Theorem 6.3 with the paper's definition of safety is `thm_6_3_lit`.
2. **Corollary 6.7 is false for `t = n − 1`.**
   - *Scope of the claim.* `γ_min,n,t` and `γ_basic,n,t` are defined for every `t < n`. Cor. 6.7 is
     stated without the hypothesis `t ≤ n − 2` of Thms. 6.5/6.6, from which it is "immediate".
   - *Counterexample.* For `t = n − 1` the implementation of `P0` is `P^min_{n−1}`, which decides 1 at
     time `n − 1` (`Min.pmin_implements` with `T = n − 1`). It is an EBA protocol (Prop. 6.1) and
     strictly dominates `P^min` (decides at `t + 1 = n`). Lean: `Counterexamples.cor_6_7_min_false`
     (one-shot sense) and `cor_6_7_min_false'` (the paper's sense).
   - *Call: ⚠️ by R4/R3.* The missing hypothesis holds at every use (it is the hypothesis of the two
     theorems the corollary is derived from).
   - *Not formalized.* The analogous failure for `P^basic`: at `t = n − 1`, state `⟨n−1, 1, ⊥, ⊥, 1⟩`
     is reachable, `P0` decides 1 there and `P^basic` does not.

## Theorem 6.3: what is proved

The paper claims: in every EBA context in which `P0` is safe, every implementation of `P0` is optimal.
We prove (`Context.thm_6_3_core`, `thm_6_3`, `thm_6_3_lit`) the following. If `P` implements `P0`,
satisfies the safety conditions for its own system, and satisfies **`NFConsistent`**, then no
**one-shot** EBA protocol strictly dominates `P`. `NFConsistent` says: every local state of an agent
undecided at time `m` also occurs at time `m`, with the same initial preferences, in a run where that
agent is nonfaulty. In the two contexts of interest both extra conditions are discharged:
* `NFConsistent`: `Min.nfConsistent`, `Basic.nfConsistent`. The latter uses the role swap of the
  paper's Prop. 6.4 proof.
* Safety for all implementations: via `Implements.state_eq`, `SafeWrt.congr`, `NFConsistent.congr`.

So `thm_6_3_min`, `thm_6_3_basic` and Cor. 6.7 (`t ≤ n − 2`) hold without caveats beyond "one-shot".

Gaps in the paper's proof:
* (a) **Faulty agent.** The agent `i` at the first difference may be faulty. The contradictions drawn
  from safety condition (1) ("`P'` decides 0 in an all-1 run, contradicting Validity") need `i`
  nonfaulty in that run. EBA imposes nothing on faulty agents. The paper's sentence "this is because
  Validity holds even for faulty agents" refers to `P`, but the decision is made by `P'`.
* (b) **Missing case.** The case "`P` decides at round `k`, `P'` does not" is not treated.
  `NFConsistent` + domination handles it.
* (c) **Repeated decisions.** "All agents have exactly the same state up to time `k − 1`: either they
  have not decided yet, or they have decided and made the same decision" is false if `P'` performs
  `decide_i(v)` again after deciding. Unique Decision allows this, and literal domination forbids it
  only for nonfaulty agents whose state is consistent with being nonfaulty.

Whether Theorem 6.3 holds in every safe EBA context (without `NFConsistent`, or for competitors that
repeat decisions) is **open**. The risk is contexts in which agents can learn that they are faulty
(e.g. through omitted self-messages). Safety condition (2) only forces such agents to be able to
decide 1. Theorem 6.3 is a headline result. It is not refuted, but in full generality it is not
established by the paper's proof. Statement-level we checked the restricted version, which is true.

## Proof repairs (statements true)

* **Prop. 6.1.**
  - The "observation" (deciding 0 ⇒ receiving a 0-chain) is false with literal chains and true with
    repaired chains (`Implements.exists_chain`). The rest of the proof is fine.
  - The termination argument is only sketched; the case "the only nonfaulty early chain member is
    `i_t`" (its `0` arrives exactly at time `t + 1`) needs a separate line. Covered in `prop_6_1`.
* **Prop. 6.4 (1), `γ_basic`.** "Let `r'` be the run where all agents start with preference 1 and the
  adversary is the same as in `r`" does not work in `γ_basic`. A faulty agent that decided 0 at round
  1 in `r` sends `(init,1)` (and later possibly a `1`) in rounds of `r'` where it is silent in `r`,
  changing `#1` and `jd` of agents that never heard its 0. Example: `n = 3`, faulty agent with preference 0 whose round-1 messages to the others
  are lost but whose later (empty) messages are delivered by the pattern. We silence every faulty
  agent from the round in which it decides 0 on (`ZeroBiased.allOnes`, for every context where
  decided agents send nothing and initial states do not depend on the preference).
* **Prop. 6.4 (2).** The paper's role-swap construction ("we leave details to the reader") is
  replaced by explicit chain runs: a chain of faulty agents relaying a 0, plus, in `γ_basic`, a set
  `E` of silent faulty agents that tunes `#1` (`chainCfg`, `chainCfgB`). This needs the bound
  `n − t ≤ #1 ≤ n − m` on reachable undecided states (`Basic.cnt_ge`), which the paper does not state.
  It also uses `j = i` when `i` itself is deciding 0, which the definition allows.
* **Thm. 6.5 / 6.6.** For the decide-1 case the paper shows only `K_i(⋀_j ¬deciding_j = 0)`. It also
  needs `¬K_i(⋁_j jdecided_j = 0)`, which we derive from the all-1 companion run
  (`ZeroBiased.not_knows_jDecided`). Typos in the proof of 6.5:
  - `I = I_{γ_min,P0}` should be the system of `P^min`;
  - "`K_i(⋀_j ¬(jdecided_j = 0))`" should be `deciding`;
  - "(Note that `t′ = m`.)".
* **Thm. 6.6.**
  - "#1_i > n − m … the only agents that can be involved in this 0-chain are ones that did not send
    an `(init,1)` message": we prove the sharper `#1 > n − d ⇒` no 0-decision at times `≥ d − 1`
    (`Basic.no_zero_of_cnt`).
  - The `jd = 1` case uses that 0-decisions precede 1-decisions (`Basic.zeroBeforeOne`).
  - Comparing with `n − time` for `time > n` needs `d ≤ n`; it follows from chain length
    (`lt_of_deciding_zero`).

## Modelling choices and resolved ambiguities

* **Local states** are pairs `(⟨time, init, decided, jd⟩, x)` with arbitrary `x : γ.X`.
  - All agents share one message type and one extra-state type. Agent-specific behaviour is allowed
    through the agent argument of `μ`, `δX`, `initX`. This is no loss of generality (take sums).
  - The sets `M⁰, M¹, M²` are given by a tag function; `⊥` is `none`.
* **`jd` when both a 0- and a 1-message arrive** in the same round: the paper's update rule is
  contradictory. We set `jd = 0`. This never happens with implementations of `P0` (0-decisions
  strictly precede 1-decisions); it only affects competitors.
* **Initial states.** Each agent must be able to start with either preference (`initX_nonempty`;
  "each agent starts with an independently selected value"). The proof of Thm. 6.3 uses it to build
  an all-0 run.
* **Failure model.** Prop. 6.1 claims termination "after at most `t + 1` rounds", so it needs
  `F ⊆ SO(t)`; we assume this (`hFM`). Literally the paper states Prop. 6.1 for every EBA context,
  whose failure model may drop messages of nonfaulty agents (then Agreement fails trivially); the
  paper only ever uses `SO(t)`, so this is an implied assumption (R4), not counted as an error. `thm_6_3_core` holds for any failure model;
  `thm_6_3`/`thm_6_3_lit` add `F ⊆ SO(t)` only to get the EBA part of optimality from Prop. 6.1. For
  `γ_min`/`γ_basic` the model is exactly `SO(t)`, including possible omission of self-messages.
* **`#1` update in `γ_basic`.** "if `decided_i = ⊥` … otherwise `#1_i` is set to 0": we read
  `decided_i` after the round, i.e. `#1 = 0` as soon as the agent has decided. This only changes
  `#1` in decided states, which are irrelevant for `P0`/`P^basic` and for knowledge tests at
  undecided states.
* **`n − time_i`** in `P^basic` is compared in `ℤ`, as in the paper.
* **Domination.** We use the paper's literal definition: every decision time of `P` is compared with
  every decision time of `P'`.
* **Competitors are one-shot** in `OptimalOneShot`: `P'_i(s) = noop` once `decided_i ≠ ⊥`. The
  paper's proof assumes this tacitly (gap (c) above). Our counterexample to Cor. 6.7 also refutes the
  unrestricted notion (`Optimal.optimalOneShot`).
* **Knowledge** is over admissible configurations (initial global states); runs are determined by
  them, as in §3. Equal local states force equal times (`time_eq_of_state_eq`), so `K_i` is the
  paper's `K_i` over all points. Bridge to CSLib: `knows_iff_K`.
* **"decides in round `m + 1`"** is formalized as `Deciding P c m j v` (`decided = ⊥` at `m`,
  `= v` at `m + 1`). "`i` does not decide before round `m + 1`" is `decided_i(m) = ⊥`.
* **`P^min` with a parameter `T`** (time of the 1-decision); the paper's `P^min` is `T = t + 1`.
  `Min.pmin_implements` covers `T ≤ t + 1`, `T ≤ n − 1`, (`t + 1 ≤ T` or `n − 1 ≤ T`).
* **Not formalized:** §7 (`P1`, full-information context, weak safety, Theorems 7.5–7.7,
  Prop. 7.9) and §8.
