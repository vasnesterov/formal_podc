# Consecutive Ballots in Paxos — PODC 2020

Eli Goldweber, Nuda Zhang, Manos Kapritsos. *Brief Announcement: On the Significance of Consecutive Ballots in
Paxos.* PODC 2020. DOI [10.1145/3382734.3405700](https://doi.org/10.1145/3382734.3405700). Formalized version:
arXiv [2006.01885](https://arxiv.org/abs/2006.01885) v1 (full version); numbering follows it.

**Verdict: ⚠️ Minor statement issues.** The main claim holds. A value may be learned once a majority has
accepted it in a consecutive span of ballots, and this keeps Paxos safe (Theorems 3.1, 3.2, Lemmas 4.1–4.3). It
stays safe when combined with Consecutive Proposals (Consecutive Paxos). However, Definition 6 (CQ Chosen) is
written so loosely that the auxiliary Lemmas 4.2′ and 4.3′ are false as stated. They are true for the evident
intended definition. The TLA+ invariant printed in Appendix B is vacuous.

## Mistakes in the paper

### ⚠️ Lemmas 4.2′ and 4.3′ (with Definition 6, CQ Chosen, as written)
Both lemmas are false for the literal Definition 6, because the ballot-`i` accept it requires need not be one of
the accepts forming the Consecutive Quorum (`lemma_4_3'_literal_false`, `lemma_4_2'_literal_false`).

**Impact.** Typo with evident intent: the proof reads the ballot-`i` accept as part of the CQ ("the acceptor in
`Qᵢ` that accepted `v` in ballot `i`"), and under that reading both lemmas hold (`lemma_4_3'`, `lemma_4_2'`).
Safety is not affected; Lemma 4.3 itself is true, but the paper derives it from the false Lemma 4.3′.

**Details.** Definition 6 says `Chosen(i, v) ≡ ∃Qᵢ. CQ(Qᵢ, v) ∧ ∃α ∈ Qᵢ. accept(i, v)_α ∈ sent_α`.
Counterexample with five acceptors in Classic Paxos:
* Ballot 3: `A, B, C` promise; `x` is proposed and accepted by `A`.
* Ballot 5: `B, C, D` promise, all `⊥`; `y` is proposed and accepted by `D`.
* Ballot 9: `A` reports `(3, x)`, `B, C` report `⊥`; `x` is proposed and accepted by `A, B, C`.

Then `{A, B, C}` in ballot 9 is a CQ for `x`, and `A` also sent `accept(3, x)`, so "`x` is chosen in ballot 3".
But `y` was proposed in ballot 5 > 3 (against Lemma 4.3′) and accepted by `D` in ballot 5 > 3 (against
Lemma 4.2′). Safety is not affected: `y` can never be chosen.

### Typos and slips
- Appendix B's TLA+ check is vacuous as printed: `ConsecQ(Q, b, v) ≜ ∀ r ∈ Acceptor : ∧ NotIn(Q, r) ∧ …` makes
  `r ∉ Q` a top-level conjunct for every acceptor `r`, so `ConsecQ` is false for every nonempty `Q`,
  `AgreedConsecQ` never holds, and the invariant `SafeValue` is true independently of the protocol
  (`tla_agreedConsecQ_false`). (`NotIn(Q, r) ⟹ …` was presumably meant, and the inner `∃ n ∈ msgs : … ⟹ …` should
  presumably be `∀`.) This concerns the paper's supporting evidence, not its theorems.
- In the proof of Lemma 4.1′, "an acceptor that has accepted *v* in ballot *j*" should say *w*.
- Appendix A writes `Chosen(v, i)` for the earlier `Chosen(i, v)` and uses `ℤ⁺` for ballots, where Section 3
  uses `ℕ`.
- Definitions 7–9 are properties of the protocol (Definition 8 is an invariant), not definitions.

## Proof gaps (statements true)

### 🛠️ Lemma 4.3′ (missing case in the proof)
The base case treats `i` as the largest ballot of the CQ, but when `i` is a smaller ballot of the CQ the
intersecting acceptor may have accepted `v` in a ballot `≥ j`, after promising `j`, so its promise reports nothing
useful.

**Impact.** Statement true (for the intended Definition 6); repaired (`propose_eq_of_interval`).

**Details.** The base case says the intersecting acceptor accepted `v` "in ballot `i` or in some ballot `< i`".
The statement still holds because every ballot in the CQ's span carries `v`.

**Repair.** Strong induction on the ballot over the whole span `[lo, hi]` of the CQ: every proposal in a ballot
`≥ lo` has value `v` (`propose_eq_of_interval`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Single-decree Paxos over asynchronous message passing, in the style of the paper's own TLA+ appendix.
  The global state holds, for each acceptor, `maxBal` and its highest accepted proposal. It also holds the set
  of all messages ever sent.
* Actions: prepare (1a), promise (1b), propose (2a), accept (2b). Each may fire whenever its guard holds, in
  any interleaving. A crash is an agent that stops taking steps. Messages can be lost or delayed, because a
  proposer or learner may use any subset of the sent messages.
* There is no Byzantine behaviour and no randomness. Ballots are `ℕ`, with one proposal per ballot.
* Quorums form an arbitrary intersecting quorum system. The paper's majorities of `2f+1` acceptors are an
  instance (`QuorumSystem.majority`); the proofs only use intersection.
* A flag `cp` switches the Consecutive Proposals of Definitions 11–12 on (Consecutive Paxos) or off (Classic
  Paxos). All safety results hold for both.
* Proposers may use any sent message. That is more than they can actually have received, so the model allows
  more behaviours and the safety results are stronger.
* Learning (Definition 3 and its CQ version) is a predicate on the set of messages a learner received. Any
  two learners, at any two times of an execution, are covered.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3.2 (Chosen Invariant, CQ Chosen) | `theorem_3_2` | `Safety.lean` |
| Theorem 3.1 (Safety, CQ learning) | `theorem_3_1`, `theorem_3_1_execution` | `Safety.lean` |
| Lemmas 4.1, 4.2, 4.3 | `lemma_4_1`, `lemma_4_2`, `lemma_4_3` | `Safety.lean` |
| Lemma 4.1′ | `lemma_4_1'` | `Safety.lean` |
| Lemmas 4.2′, 4.3′ (intended Def. 6) | `lemma_4_2'`, `lemma_4_3'` | `Safety.lean` |
| Lemmas 4.2′, 4.3′ (literal Def. 6) — false | `lemma_4_2'_literal_false`, `lemma_4_3'_literal_false` | `Counterexample.lean` |
| Core: a CQ spanning `[lo, hi]` forces all proposals `≥ lo` | `propose_eq_of_interval`, `cq_propose_eq` | `Safety.lean` |
| Definition 8 (Accept ⇒ Propose), Definition 9 | `accept_implies_propose`, `chosen_implies_propose` | `Safety.lean` |
| §4 "CQ Chosen is weaker than Chosen"; §4.2 liveness preserved | `classicChosen_cqChosen'`, `classicLearned_cqLearned` | `Safety.lean` |
| Strictly weaker (Table 3) | `table3_cqChosen`, `table3_not_classicChosen`, `table3_only_x` | `Examples.lean` |
| Tables 1–2: same value by a majority in non-consecutive ballots is unsafe | `table2_naive_unsafe` | `Examples.lean` |
| Definitions 1–2: consecutive sets are intervals | `ConsecutiveSet.mem_of_le_of_le` | `ConsecutiveSet.lean` |
| §6.2 Consecutive Paxos is safe | `theorem_3_2` with `cp = true`; example `consecPaxos_example` | `Safety.lean`, `Examples.lean` |
| Appendix B TLA+ `SafeValue` vacuous | `tla_agreedConsecQ_false` | `TLAAppendix.lean` |

**Not formalized.** Liveness under partial synchrony: only the weakening argument of §4.2 is checked. The §4.3
discussion and the IronFleet/Dafny Multi-Paxos refinement of §6 are also not formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: concrete reachable executions with five acceptors. These are Table 3, Table 2 extended by ballot
11, the counterexample, and a Consecutive Paxos run in which ballot 2 is proposed by a Consecutive Proposal
without Phase 1 (`consecPaxos_example`). The model is self-contained (Mathlib only).
