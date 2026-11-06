# Fair Leader Election for Rational Agents — PODC 2018

Assaf Yifrach, Yishay Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018. DOI [10.1145/3212734.3212767](https://doi.org/10.1145/3212734.3212767).
Formalized version: arXiv [1805.04778](https://arxiv.org/abs/1805.04778) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The attacks on `A-LEADuni`, the paper's main focus, hold: Lemma 2.4, the success
characterization (Lemmas 3.3–3.5), Lemma 4.1 (honest origin), Theorem 4.2 (`k ≥ √n`), the Cubic
Attack (Theorem 4.3, Lemmas 4.4–4.5), Corollary 4.6 (`ε < 1 − 1/n`) and Claim D.1 (`k < n/2`) are
proved. But **Theorem 7.2 (no resilient FLE on `k`-simulated trees) is proved only for `n = 2`**, its
status for `n ≥ 3` is open, and the claimed equivalence of Fair Leader Election and Fair Coin Toss
(Theorem 8.1) has a wrong step and no repair. The resilience side was not checked: Theorem 5.1
(`∜n`-resilience) and Section 6 (`PhaseAsyncLead`) are not formalized.

## Mistakes in the paper

### ❌ Theorem 7.2 for `n ≥ 3` (no resilient FLE on `k`-simulated trees)
The proof's Lemma F.3 and Corollary F.4 treat `b`, which "simulates the rest of the tree", as a
processor of the model, but it is not one, so Theorem 7.2 is unestablished for `n ≥ 3`; we prove it
for `n = 2` (`Trees.thm_7_2_two`).

**Impact.** For `n ≥ 3` the theorem is neither proved nor refuted, and `n = 2` is only the two-party
case, none of the claimed generalization to trees. The attacks on `A-LEADuni` (Sections 3–4) are
unaffected.

**Details.** The super-node's behaviour toward the leaf depends on how the leaf's messages interleave
with internal events. So neither "`a` assures `o` in `P_a` ⇒ `a` assures `o` in `P`" nor "`b` is a
dictator" transfers. Also, for a super-node, termination under every fair schedule does not bound the
number of messages (ping-pong until a third processor's message arrives), and Lemma F.2 needs such a
bound. The same issue affects connected fibres in Corollary F.4.

**Repair.** For `n = 2` only. We prove Lemma F.2 itself, for two processors, in a generalized form:
arbitrary output sets, finite inputs, and no message bound needed, since it follows from finite inputs
(`Trees.lemma_F2`). With `Trees.not_resilient_of_assures` (see the next item) this gives Theorem 7.2
for `n = 2`, all `1 ≤ k ≤ 2`, `ε < 1/n`.

### ❌ Theorem 8.1, first direction (also the last step of the proof of Theorem 7.2)
The step `Pr(coin = 0) ≤ Σ_{i even} Pr(leader = i)` is wrong, because the parity coin can succeed while the election
fails: processors may output different leaders of the same parity.

**Impact.** The claimed equivalence of Fair Leader Election and Fair Coin Toss is not established. Theorem 8.1 is
neither repaired nor formalized; its status is unknown, not refuted.

**Details.** The last step of the proof of Theorem 7.2 goes through this coin toss (leader parity), and it also covers
only even `n`.

**Repair.** For the use in Theorem 7.2 only. We replace the coin-toss step by a direct lemma: a coalition that forces
the leader into a proper subset breaks `ε`-`k`-resilience for every `ε < 1/n` and every `n`
(`Trees.not_resilient_of_assures`).

### ⚠️ Lemma 4.1 (adversarial origin)
Lemma 4.1 is stated for every coalition whose segments have length `≤ k − 1`, but its attack
deadlocks when the origin is an adversary: only the origin wakes up spontaneously and every
adversary just forwards, so nobody ever sends and the outcome is `FAIL`
(`lemma_4_1_attack_deadlocks`).

**Impact.** Unestablished for an adversarial origin; the statement is probably still true with a
modified attack. We prove the lemma for an honest origin, which is all Theorems 4.2 and 4.3 need
(`lemma_4_1`).

### 🔧 Theorem 7.2 at the boundary `ε = 1/n`
For `n = 2` and `ε = 1/n` Theorem 7.2 is false: `K₂` is a 1-simulated tree, and the protocol in
which one processor draws a bit and both output it is `½`-`1`-resilient
(`Trees.thm_7_2_boundary_false`).

**Impact.** An edge case of the stated range `ε ≤ 1/n`: every FLE protocol is `(1 − 1/n)`-resilient
(see Corollary 4.6 under Slips), and for `n = 2`, `1 − 1/n = 1/n`. For `n ≥ 3` and `ε = 1/n` the
status is open.

**Repair.** The condition `ε < 1/n`, under which we prove the case `n = 2` (`Trees.thm_7_2_two`).

### ✏️ Slips
- Claim D.1 claims `Pr(outcome = j) ≤ 1/n` for *every* consecutive coalition, but for `n ≥ 3` the block of all
  processors except the origin forces any outcome by the attack of Lemma 4.1 (`claim_D_1_false`). That block leaves one
  honest processor; its segment has length `1 ≤ k − 1`. The proof needs the honest segment to be longer than the
  coalition (the text says "length `k > l`", meant as `l > k`), and the introduction presents Appendix D as a proof of
  the result of Abraham et al. for `k < n/2`. The claim is not used elsewhere. We prove it for `2k + 1 ≤ n` and any
  position of the origin (`claim_D_1`). Consequence: `A-LEADuni` is `0`-`1`-resilient for `n ≥ 3`
  (`isResilient_aLead_one`).
- Corollary 4.6 is stated for `0 ≤ ε ≤ 1 − 1/n`, but every FLE protocol, in particular `A-LEADuni`, is
  `(1 − 1/n)`-`k`-resilient for every `k` (`corollary_4_6_boundary_false`): no deviation can raise an expected rational
  utility by more than `1 − 1/n`, since the deviation gets at most `max u` and the honest run already gets
  `(1/n)·Σ u ≥ max u / n`. Theorems 4.2 and 4.3 themselves use the strict `ε < 1 − 1/n`, and we prove the corollary
  for `ε < 1 − 1/n` (`corollary_4_6`).
- Lemma 3.3 says "the execution succeeds iff conditions 1–3", but `outcome` also needs the adversaries to terminate
  with the same output, which conditions 1–3 do not control. The intended reading is "all honest processors terminate
  with the same valid output"; we prove it, and its version for every fair schedule (`lemma_3_3`, `lemma_3_3_run`).
  Also, "sends `n` messages" should be "at least `n`", and the sums are over the first `n` messages.
- Definition 7.1 asks for a graph homomorphism `f` with `{(f(x), f(y)) | (x, y) ∈ E} ⊆ E_T`. A tree
  has no loops, so every connected fibre is a singleton
  (`Trees.IsKSimTreeLiteral.card_fiber_le_one`). The next sentence describes the intended notion (a
  partition into connected parts of size `≤ k` whose quotient is a tree), which we use.
- The Section 7 remark "Every graph can be simulated by a tree of size 2 with parts of size
  `≤ ⌈n/2⌉`" is false: `K₁,₃` has no such partition. Claim F.5, which uses a star, is fine (not
  formalized).
- Appendix A: the origin starts with `round = 1`. It then validates its `(n−1)`-th incoming message
  against `d₁` and sums only `n − 1` values, so the honest run aborts whenever `d₁ ≠ d₂`. The verbal
  description (validate the `n`-th message) is what we formalize.
- Appendix C: in the Cubic Attack the zeros are sent only when `count == n−k−lᵢ` after incrementing
  `count`. This never happens if `n − k − lᵢ = 0`, and the attack deadlocks (e.g. `n = 4`, `k = 2`,
  `l = (2, 0)`). Following the text, we send them at wake-up.
- Proof of Theorem 4.3: `Σ_{i=1}^{k'−1}(k'−1)i` is written `(k'−1)k'(k'+1)/2`; it is
  `(k'−1)²k'/2` (harmless).
- Proof of Lemma 4.4: "since `l₁ = maxᵢ lᵢ`" does not follow from the relaxed conditions
  `l_k ≤ k−1`, `lᵢ ≤ lᵢ₊₁ + k − 1`; the lemma holds anyway, and our liveness proof does not use it.

### Typos
- Proof of Lemma 3.3: the case analysis swaps the numbering of conditions 1 and 2.

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
