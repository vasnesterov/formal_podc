# Fair Leader Election for Rational Agents — PODC 2018

Assaf Yifrach, Yishay Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018. DOI [10.1145/3212734.3212767](https://doi.org/10.1145/3212734.3212767).
Formalized version: arXiv [1805.04778](https://arxiv.org/abs/1805.04778) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The attacks on `A-LEADuni` hold: Lemma 2.4, the success
characterization (Lemmas 3.3–3.5), Lemma 4.1 (honest origin), Theorem 4.2 (`k ≥ √n`), the Cubic
Attack (Theorem 4.3, Lemmas 4.4–4.5), Corollary 4.6 (`ε < 1 − 1/n`) and Claim D.1 (`k < n/2`) are
proved. **Theorem 7.2 (no resilient FLE on `k`-simulated trees) is proved only for `n = 2`**: for
`n ≥ 3` its proof (Lemma F.3, Corollary F.4) has gaps we could not close, and its status there is
open. The other problems are edge cases (Corollary 4.6 and Theorem 7.2 fail at the boundary value of
`ε`; Claim D.1 omits the bound `k < n/2` that the introduction states), a proof gap in Lemma 4.1 and
slips. Theorem 5.1 (`∜n`-resilience) and Section 6 are not formalized.

## Mistakes in the paper

* **Theorem 7.2: its proof has gaps (proved here only for `n = 2`), and it is false at `ε = 1/n` for
  `n = 2`.**
  - *Lemma F.3 / Corollary F.4 (proof gap, status open for `n ≥ 3`).* Here `b` "simulates the rest of
    the tree" in a two-party protocol. That super-node is not a processor of the model: its behaviour
    toward the leaf depends on how the leaf's messages interleave with internal events. So neither
    "`a` assures `o` in `P_a` ⇒ `a` assures `o` in `P`" nor "`b` is a dictator" transfers. Also, for a
    super-node, termination under every fair schedule does not bound the number of messages
    (ping-pong until a third processor's message arrives), and Lemma F.2 needs such a bound. The same
    issue affects connected fibres in Corollary F.4. We prove Lemma F.2 itself, for two processors, in
    a generalized form: arbitrary output sets, finite inputs, and no message bound needed, since it
    follows from finite inputs (`Trees.lemma_F2`). From it we get Theorem 7.2 for `n = 2`, all
    `1 ≤ k ≤ 2`, `ε < 1/n` (`Trees.thm_7_2_two`). For `n ≥ 3` it is neither proved nor refuted.
  - *Reduction to coin toss (proof gap).* The last step goes through a coin toss (leader parity,
    Theorem 8.1). The coin can succeed while the election fails: processors may output different
    leaders of the same parity, so `Pr(coin = 0) ≤ Σ_{i even} Pr(leader = i)` does not follow. The
    proof also covers only even `n`. We replace this step by a direct lemma: a coalition that forces
    the leader into a proper subset breaks `ε`-`k`-resilience for every `ε < 1/n` and every `n`
    (`Trees.not_resilient_of_assures`).
  - *Boundary (false in an edge case).* The theorem is stated for `ε ≤ 1/n`. But every FLE protocol
    is `(1 − 1/n)`-resilient (see the Corollary 4.6 item), and for `n = 2`, `1 − 1/n = 1/n`. `K₂` is a
    1-simulated tree and has an FLE protocol: one processor draws a bit and both output it. So that
    protocol is `½`-`1`-resilient (`Trees.thm_7_2_boundary_false`). For `n ≥ 3` and `ε = 1/n` the
    status is open.
* **Lemma 4.1's attack deadlocks if the origin is an adversary (proof gap).** The lemma is stated for
  every coalition whose segments have length `≤ k − 1`. Only the origin wakes up spontaneously, and
  in the attack every adversary just forwards. With an adversarial origin nobody ever sends, and the
  outcome is `FAIL`. The statement is probably still true with a modified attack. We prove the lemma
  for an honest origin, which is all Theorems 4.2 and 4.3 need (`lemma_4_1_attack_deadlocks`,
  `lemma_4_1`).
* **Claim D.1 omits the bound `k < n/2` (missing hypothesis).** It claims `Pr(outcome = j) ≤ 1/n`
  for *every* consecutive coalition. For `n ≥ 3`, the block of all processors except the origin leaves
  one honest processor; its segment has length `1 ≤ k − 1`, so the attack of Lemma 4.1 forces any
  outcome (`claim_D_1_false`). The introduction presents Appendix D as a proof of the result of
  Abraham et al. for `k < n/2`, and the proof needs the honest segment to be longer than the
  coalition (the text says "length `k > l`", meant as `l > k`); the claim is not used elsewhere. We
  prove it for `2k + 1 ≤ n` and any position of the origin (`claim_D_1`). Consequence: `A-LEADuni`
  is `0`-`1`-resilient for `n ≥ 3` (`isResilient_aLead_one`).
* **Corollary 4.6 is false at its boundary `ε = 1 − 1/n` (edge case).** It is stated for
  `0 ≤ ε ≤ 1 − 1/n`. But no deviation can raise an expected rational utility by more than `1 − 1/n`:
  the deviation gets at most `max u`, and the honest run already gets `(1/n)·Σ u ≥ max u / n`. So
  every FLE protocol, in particular `A-LEADuni`, is `(1 − 1/n)`-`k`-resilient for every `k`. Theorems
  4.2 and 4.3 themselves use the strict `ε < 1 − 1/n`. We prove the corollary for `ε < 1 − 1/n`
  (`corollary_4_6_boundary_false`, `corollary_4_6`).
* **Lemma 3.3 is imprecise.** It says "the execution succeeds iff conditions 1–3". But `outcome`
  also needs the adversaries to terminate with the same output, which conditions 1–3 do not control.
  The right reading is "all honest processors terminate with the same valid output". Also, "sends `n`
  messages" should be "at least `n`", and the sums are over the first `n` messages. We prove the
  corrected statement, and its version for every fair schedule (`lemma_3_3`, `lemma_3_3_run`).
* **Definitions and remarks of Section 7.**
  - Definition 7.1 asks for a graph homomorphism `f` with `{(f(x), f(y)) | (x, y) ∈ E} ⊆ E_T`. A tree
    has no loops, so an edge inside a fibre is impossible and every connected fibre is a singleton
    (`Trees.IsKSimTreeLiteral.card_fiber_le_one`). This is a wording slip: the next sentence describes
    the intended notion (a partition into connected parts of size `≤ k` whose quotient is a tree),
    which we use.
  - "Every graph can be simulated by a tree of size 2 with parts of size `≤ ⌈n/2⌉`" is false: `K₁,₃`
    has no such partition. Claim F.5, which uses a star, is fine (not formalized).
* **Slips.**
  - Appendix A: the origin starts with `round = 1`. It then validates its `(n−1)`-th incoming message
    against `d₁` and sums only `n − 1` values, so the honest run aborts whenever `d₁ ≠ d₂`. The verbal
    description (validate the `n`-th message) is what we formalize.
  - Appendix C: in the Cubic Attack the zeros are sent only when `count == n−k−lᵢ` after incrementing
    `count`. This never happens if `n − k − lᵢ = 0`, and the attack deadlocks (e.g. `n = 4`, `k = 2`,
    `l = (2, 0)`). Following the text, we send them at wake-up.
  - Proof of Lemma 3.3: the case analysis swaps the numbering of conditions 1 and 2.
  - Proof of Theorem 4.3: `Σ_{i=1}^{k'−1}(k'−1)i` is written `(k'−1)k'(k'+1)/2`; it is
    `(k'−1)²k'/2` (harmless). Proof of Lemma 4.4: "since `l₁ = maxᵢ lᵢ`" does not follow from the
    relaxed conditions `l_k ≤ k−1`, `lᵢ ≤ lᵢ₊₁ + k − 1`; the lemma holds anyway, and our liveness
    proof does not use it.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous unidirectional ring of `n` processors (`Fin n`, origin `0`), with reliable FIFO links.
  Processors are deterministic and event driven: a processor is a function of its received history
  (shared model `Cslib.UniRing`, `Podc/Computability/Distributed/UniRing/Basic.lean`). Every processor
  may send at wake-up (honest normal processors send nothing then). Schedules are oblivious sequences
  of processors; fair = each one scheduled infinitely often. We *prove* that on a unidirectional ring
  the schedule does not matter (`terminates_iff`, `outcomeUnder_eq`).
* Randomness: honest secrets `d i` uniform in `Fin n`; probabilities by counting. Messages are values
  in `Fin n`.
* Outcome `v` iff all processors (adversaries included) terminate with output `v`; otherwise `FAIL`.
* Coalitions of size exactly `k` run arbitrary **deterministic** strategies (Def. 2.2). Rational
  utilities, `ε`-`k`-resilience (Def. 2.3), `ε`-`k`-unbiasedness and FLE are as in Section 2, for
  every fair schedule. Deterministic deviations suffice for all negative results. Our positive results
  (Claim D.1 and its corollaries) are proved against deterministic deviations only (see
  `differencies.md`, item 5).
* Section 7 (`Tree*.lean`, namespace `Podc.FairLeaderElection.Trees`) uses a general asynchronous
  model on a graph. Processors see the arrival order across their links, links are FIFO, schedules
  are sequences of directed links, and fair = every directed edge infinitely often. Protocols need not
  be symmetric; random inputs come from finite sets, uniformly. Two-party protocols are the
  unidirectional ring of size 2.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Schedule independence on the ring (remark in §2) | `Cslib.UniRing.terminates_iff`, `outcomeUnder_eq` | `Podc/…/UniRing/Basic.lean`, `Game.lean` |
| Lemma 2.4 | `lemma_2_4` | `Game.lean` |
| gain `≤ 1 − 1/n` for any FLE protocol (new) | `expU_le_add_one_sub`, `isResilient_one_sub_inv` | `Game.lean` |
| `A-LEADuni` elects `Σ dᵢ`; it is FLE | `outcome_aLead`, `isFLE_aLead` | `ALead.lean` |
| Lemmas 3.4, 3.5 | `lemma_3_4`, `lemma_3_5` | `Characterization.lean` |
| Lemma 3.3 (corrected) | `lemma_3_3`, `lemma_3_3_run` | `Characterization.lean` |
| Lemma 4.1 (origin honest) | `lemma_4_1` | `Attacks.lean` |
| Lemma 4.1's attack with adversarial origin fails | `lemma_4_1_attack_deadlocks` | `Attacks.lean` |
| Lemmas 4.4, 4.5 (any rushing attack) | `rushing_outcome`, `reach_finalCfg`, `lemma_4_4_4_5` | `Rushing.lean`, `Attacks.lean` |
| Theorem 4.2 | `theorem_4_2'` (`√n ≤ k`), `theorem_4_2` | `Attacks.lean` |
| Theorem 4.3 (Cubic Attack) | `theorem_4_3'` (`2∛n ≤ k`), `theorem_4_3` | `Attacks.lean` |
| Corollary 4.6 (`ε < 1 − 1/n`) / false at `ε = 1 − 1/n` | `corollary_4_6'` / `corollary_4_6_boundary_false` | `Attacks.lean` |
| Claim D.1 (`2k < n`) / false without the bound | `claim_D_1` / `claim_D_1_false` | `Consecutive.lean` |
| `A-LEADuni` is `0`-`1`-unbiased and resilient | `isUnbiased_aLead_one`, `isResilient_aLead_one` | `Consecutive.lean` |
| Lemma F.2 (generalized) | `Trees.lemma_F2` | `TreeTwoParty.lean` |
| assured proper subset ⇒ not resilient (replaces Thm 8.1's use) | `Trees.not_resilient_of_assures` | `TreeBounds.lean` |
| Theorem 7.2 for `n = 2` / false at `ε = 1/n`, `n = 2` | `Trees.thm_7_2_two` / `Trees.thm_7_2_boundary_false` | `TreeImpossibility.lean` |
| Definition 7.1 as written is degenerate | `Trees.IsKSimTreeLiteral.card_fiber_le_one` | `TreeModel.lean` |

**Not formalized.** Theorem 5.1 (`∜n`-resilience) and Conjecture 4.7; Appendix C (randomly located
adversaries) and Claim B.1; `PhaseAsyncLead` (Section 6, Appendix E); Theorem 8.1; Theorem 7.2 for `n ≥ 3` (Lemma F.3, Corollary F.4), Claim F.5; Appendices G
and H.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `A-LEADuni` is FLE (`isFLE_aLead`); the resilience notion is satisfiable
(`isResilient_aLead_one`, `isResilient_one_sub_inv`). The ring model is staged in
`Podc/Computability/Distributed/UniRing/Basic.lean` (CSLib candidate).
