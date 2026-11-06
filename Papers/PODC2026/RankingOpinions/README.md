# Ranking opinions in population protocols — PODC 2026

Tom-Lukas Breitkopf, Julien Dallot, Antoine El-Hayek, Stefan Schmid. *Ranking Opinions with Few States in
Population Protocols.* PODC 2026. DOI [10.1145/3796701.3815913](https://doi.org/10.1145/3796701.3815913).
Formalized version: arXiv [2605.18707](https://arxiv.org/abs/2605.18707) v1.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Theorem 1.1 (Circles: relative majority with `k³` states) is proved, and so are
Theorems 4.2, 4.3, 5.1 and 5.2, under the readings explained below; the proofs of Theorem 4.2 and of Lemma 8.11
needed new arguments. **Theorem 4.1 (TieReport) is false**, and **the ranking protocol of Theorem 1.2 is incorrect
as written**, but each has a small fix, and the fixed protocols are proved correct with the same state counts.
Time complexity and the binary win/lose variants were not checked.

## Mistakes in the paper

### 🔧 Theorem 1.2 (the ranking protocol of Section 6)
The ranking protocol is incorrect: for `k = 2` and three agents with colours `0, 1, 1` a globally fair execution
reaches, after 9 steps, a configuration that no interaction changes and in which agent 2 outputs ranking 1
instead of 0 (`Ranking.Counterexample.literal_not_correct`).

**Impact.** The protocol as written fails, but a small fix works with the same state count: the fixed protocol is
correct with `2k⁴` states (`Ranking.ranking_correct`).

**Details.** The instance has every colour present and no tie. The stuck configuration is
`⟨0,1|0,1⟩, ⟨1,0|1,0⟩*, ⟨1,1|0,1⟩*` (`*` = token holder). Cause: an agent holding the token of its *own* bra
colour never updates its own bra ranking, because rule (4) updates only *other* agents; the proof of Lemma 6.10
overlooks this. The failure is not a quirk of one reading: the literal protocol also fails for counts (1,2),
(2,3), (3,2), (1,4) (`k = 2`) and (1,2,3) (`k = 3`), under every orientation reading.

**Repair.** After each interaction, an agent with a token and `bc = kc` sets `br := kr`
(`Ranking.ranking_correct`).

### 🔧 Theorem 4.1 (TieReport, no-tie case)
TieReport fails with a unique majority: for `k = 3`, colours `0, 0, 1, 2` and schedule `(1,2), (0,3), (0,2)`,
agent 0 ends as the only diagonal agent and outputs "tie" forever under every fair continuation
(`tieReport_counterexample_noTie`).

**Impact.** Theorem 4.1 is false as stated; a small fix gives a correct protocol with the same `3k³` states
(`tieReport_fixed_correct`).

**Details.** Agent 0 decays from `⟨0|0⟩` to `⟨0|2⟩`, becomes a tie spreader, and recombines to `⟨0|0⟩`. The
brakets are then stable, and agent 0 is the *only* diagonal agent. Rule 3 lets a diagonal agent reset only
*other* agents, so agent 0 is never reset. This holds under both readings of the ambiguous rule 2; the proof of
Lemma 8.1 overlooks the remaining `⟨μ|μ⟩` agent itself.

A second, tie-case failure (`k = 2`, colours `0,0,1,1`) exists only if rule 2 is read literally *and* applied
simultaneously in both directions, so it is an ambiguity rather than a definite error
(`tieReport_counterexample_tie`).

**Repair.** A diagonal agent also resets itself, and tie spreading affects only `no_tie` agents. The tie case then
needs an invariant the paper lacks: there is always a diagonal agent or a spreader (`tieReport_fixed_correct`).

### 🔧 Theorem 4.2 (output of TieSharing)
TieSharing keeps Circles' "Output: return out", and with it the claim that every winner outputs its initial colour
is false (`OutCounterexample.tieShare_out_counterexample`: `k = 2`, colours `0,0,1,1`, a fixed configuration with a
winner spreader of colour 1 and `out = 0` forever).

**Impact.** One line defining the output by status saves the theorem at no state cost (`tieShare_correct`).

**Details.** The paper states no output rule for TieSharing; its proof only says that agents "update their out
accordingly".

**Repair.** A status-dependent output map: winners output their bra, losers `out`.

### ✏️ Slips
- Lemma 6.2 (backward direction) and Lemmas 6.7(2) and 6.12 need Section 6's standing assumptions (no tie, every
  colour present); read alone, Lemma 6.2 fails for `k = 2` and counts (1, 1).
- Lemma 6.12's indexing is off by one: ranks `0..l−1` are called "the `l−1` most popular colors".

### Typos
- The set X of Def. 6.4 is closed only as a set.
- Ord-Circles, "pending agents do not interact otherwise": the rule must also exclude Circles step (5) for an agent
  that became pending in step (4) of the same interaction, or Invariant 3.3 breaks. Read step by step, the printed
  sentence says this, but it is placed at step (2). Theorem 5.2 holds with this reading (`ordCircles_correct`).

## Proof gaps (statements true)

### 🛠️ Lemmas 8.2 and 8.3 (TieSharing)
Lemma 8.2 ignores tokens alive after stabilization, and Lemma 8.3's proof is a sketch.

**Impact.** The statements Theorem 4.2 needs are true, with a new argument (`tieShare_correct`).

**Details.**
- Lemma 8.2 (`r = 1`): the tokens still alive can demote majority agents or promote others, and tokens can
  multiply, so their extinction needs a separate potential argument (`extinction`).
- Lemma 8.3 (`r > 1`): Claim 3 holds only once all agents of colour `μ_s` have their final braket (`witness`), and
  "token ascent until attached" with the inductive spreading of tokens does not work as written.

**Repair.** Tokens off top brakets die out (`no_spurious`), the set of token holders stabilizes, and the induction
gets a starting token from the last ket exchange.

### 🛠️ Lemma 8.11 (Ordering, finitely many ordering-state changes)
The proof's step "a used label never becomes free" is false (reachable with `k = 3`, colours `0,0,1,1`).

**Impact.** The lemma itself holds by a different potential (`oc_ord_stabilizes`).

**Details.** A label used only by leaders in state `I`, left over from before leader stability, can be freed, and
the counting argument of the proof rests on this step.

**Repair.** The labels of `U`-leaders, a cyclic-distance potential and a non-leader rank potential.

### 🔧 Lemma 8.4 (TieBreak)
Lemma 8.4's "the maximum weight is in `f(G_q)`" needs an arc argument.

**Impact.** The statement is true; a short arc comparison fills the step (`exists_key_gt`, `w_add_of_closest`;
Theorem 4.3: `tieBreak_correct`).

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
- Shared infrastructure: counterexample executions are CSLib's `Execution.ofSched`; potential arguments use
  `Nat.eventually_const_of_succ_le`/`_of_le_succ` (`Cslib/Foundations/Data/Nat/Descent.lean`); leader counts are `numLeaders`
  (`Cslib/Computability/Distributed/PopulationProtocols/Nondet.lean`).

**Readings of ambiguous rules** (clarifications, not mistakes).
- Theorem 4.2 (TieSharing) depends on the order of its rules. If all status rules read the pre-interaction
  statuses, the theorem fails already for colours `0, 0, 1` (`tieShare_pre_counterexample`). With the rules applied
  sequentially, as listed, it holds.
- Theorem 4.3: TieBreak leaves token transfer between agents with equal weight and bra unspecified (we keep the
  token in place).
- Theorems 5.1, 5.2 depend on the orientation of weak fairness. Ordering and Ord-Circles are asymmetric: mostly
  only the initiator changes. They are correct if every *ordered* pair interacts infinitely often, the natural
  reading of §2.1's directed interaction graph. Under an unordered-pair reading of Definition 2.1 both fail
  (`k = 2`, colours `0, 0, 1`; `ordering_not_weaklyFair`, `ordCircles_not_weaklyFair`). Symmetrized versions work
  under either reading.

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
