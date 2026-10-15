# Ranking opinions in population protocols — PODC 2026

Tom-Lukas Breitkopf, Julien Dallot, Antoine El-Hayek, Stefan Schmid. *Ranking Opinions with Few States in
Population Protocols.* PODC 2026. DOI [10.1145/3796701.3815913](https://doi.org/10.1145/3796701.3815913).
Formalized version: arXiv [2605.18707](https://arxiv.org/abs/2605.18707) v1.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Theorem 1.1 (Circles: relative majority with `k³` states) is proved, and so are
Theorems 4.2, 4.3, 5.1 and 5.2, under the readings explained below. **Theorem 4.1 (TieReport) is false**, and
**the ranking protocol of Theorem 1.2 is incorrect as written**. Each has a small fix, and the fixed protocols
are proved correct with the same state counts.

## Mistakes in the paper

1. **Theorem 1.2: the ranking protocol is incorrect (false claim).** Take `k = 2` and three agents with colours
   `0, 1, 1` (every colour present, no tie). There is a globally fair execution that, after 9 steps, reaches
   `⟨0,1|0,1⟩, ⟨1,0|1,0⟩*, ⟨1,1|0,1⟩*` (`*` = token holder). No interaction changes this configuration, and
   agent 2 outputs ranking 1 instead of 0. Cause: an agent holding the token of its *own* bra colour never updates
   its own bra ranking, because rule (4) updates only *other* agents; the proof of Lemma 6.10 overlooks this. The
   failure is not a quirk of one reading: the literal protocol also fails for counts (1,2), (2,3), (3,2), (1,4)
   (`k = 2`) and (1,2,3) (`k = 3`), under every orientation reading. Fix: after each interaction, an agent with a
   token and `bc = kc` sets `br := kr`. The fixed protocol is correct with `2k⁴` states
   (`Ranking.Counterexample.literal_not_correct`; fix `Ranking.ranking_correct`).
2. **Theorem 4.1 (TieReport) is false in the no-tie case (false claim).** Take `k = 3` and four agents with
   colours `0, 0, 1, 2` (unique majority 0), and schedule `(1,2), (0,3), (0,2)`. Agent 0 decays from `⟨0|0⟩` to
   `⟨0|2⟩`, becomes a tie spreader, and recombines to `⟨0|0⟩`. The brakets are then stable, and agent 0 is the
   *only* diagonal agent. Rule 3 lets a diagonal agent reset only *other* agents, so agent 0 outputs "tie"
   forever under every fair continuation. This holds under both readings of the ambiguous rule 2; the proof of
   Lemma 8.1 overlooks the remaining `⟨μ|μ⟩` agent itself. A second, tie-case failure (`k = 2`, colours
   `0,0,1,1`) exists only if rule 2 is read literally *and* applied simultaneously in both directions, so it is an
   ambiguity rather than a definite error. Fix: a diagonal agent also resets itself, and tie spreading affects
   only `no_tie` agents. The tie case then needs an invariant the paper lacks: there is always a diagonal agent
   or a spreader (`tieReport_counterexample_noTie`, `tieReport_counterexample_tie`; fix
   `tieReport_fixed_correct`).
3. **Theorem 4.2 (TieSharing): true only under specific readings (clarification).** If all status rules read the
   pre-interaction statuses, the theorem fails already for colours `0, 0, 1` (`tieShare_pre_counterexample`).
   With the rules applied sequentially, as listed, it holds. "The output of every winner is its initial colour"
   also needs a status-dependent output map. If every agent outputs its `out` variable, the theorem fails
   (`OutCounterexample.tieShare_out_counterexample`: `k = 2`, colours `0,0,1,1`).
4. **Theorems 5.1, 5.2: orientation of weak fairness (clarification).** Ordering and Ord-Circles are asymmetric:
   mostly only the initiator changes. They are correct if every *ordered* pair interacts infinitely often, the
   natural reading of §2.1's directed interaction graph. Under an unordered-pair reading of Definition 2.1 both
   fail (`k = 2`, colours `0, 0, 1`; `ordering_not_weaklyFair`, `ordCircles_not_weaklyFair`). Symmetrized
   versions work under either reading.
5. **Proof gaps (statements true).**
   - Lemma 8.11: "a used label never becomes free" is false (reachable with `k = 3`, colours `0,0,1,1`), but the
     lemma itself holds by a different potential.
   - Lemma 8.2 ignores tokens alive after stabilization; Lemma 8.3's proof is a sketch.
   - Lemma 8.4's "the maximum weight is in `f(G_q)`" needs an arc argument. TieBreak leaves token transfer
     between agents with equal weight and bra unspecified (we keep the token in place).
   - "Pending agents do not interact otherwise" must also exclude Circles step (5) for an agent that became
     pending in step (4) of the same interaction, or Invariant 3.3 breaks.
   - Lemma 6.2 (backward) and 6.12 need Section 6's standing no-tie assumption; Lemma 6.12's indexing is off by
     one; the set X of Def. 6.4 is closed only as a set.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib, `Cslib/Computability/Distributed/PopulationProtocols/`).
- Population protocols on the complete graph with `n ≥ 1` labelled agents and deterministic two-way transitions
  `δ : Q → Q → Q × Q` (initiator, responder). No failures and no randomness; the scheduler is adversarial.
- Weak fairness: every unordered pair of distinct agents interacts infinitely often. This is the weaker
  hypothesis, except in Section 5, where ordered-pair fairness is used (item 4). Global fairness (for ranking) is
  defined on labelled configurations. That is slightly stronger than the paper's multiset view, so
  `Ranking.ranking_correct` is slightly weaker than claimed.
- Inputs are colours `Fin k` (ordered) or any type with decidable equality (Section 5, at most `k` colours occur).
  Correctness: from some time on, every agent forever outputs the required value; for Theorem 1.1 we also prove
  output stability. Circles' termination holds for every execution, without fairness, as in the paper.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemmas 3.2, 3.7, Theorem 3.4 | `greedy_majority`, `eq_layers_of_stable`, `eventually_const` | `Layers.lean`, `Dynamics.lean` |
| Theorem 1.1 / 3.5 (Circles, `k³` states) | `circles_correct`, `card_CState` | `Circles.lean` |
| Theorem 4.1: counterexamples; fixed protocol | `tieReport_counterexample_noTie`; `tieReport_fixed_correct` | `TieReport.lean` |
| Theorem 4.2 (TieSharing, `3k³`) | `tieShare_correct` | `TieShareMain.lean` |
| Theorem 4.3 (TieBreak, `2k³`) | `tieBreak_correct` | `TieBreak.lean` |
| Theorems 5.1, 5.2 (ordered fairness; symmetrized) | `ordering_correct`, `ordCircles_correct`; `orderingSymm_correct`, `ordCirclesSymm_correct` | `UnorderedOrdering.lean`, `UnorderedOrdCircles.lean` |
| Theorem 1.2: counterexample; fixed protocol (`2k⁴`) | `Ranking.Counterexample.literal_not_correct`; `Ranking.ranking_correct` | `RankingCounterexample.lean`, `RankingMain.lean` |

**Not formalized.** The binary win/lose output variants (`4k²`, `3k²` states), Remark 1 (unordered ranking), time
complexity (Section 3.3), and the "exactly one token per sector" part of Lemma 8.3.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. All
counterexamples are explicit fair executions checked in Lean.
