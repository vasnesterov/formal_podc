# Ranking Opinions with Few States in Population Protocols (PODC 2026)

Tom-Lukas Breitkopf, Julien Dallot, Antoine El-Hayek, Stefan Schmid.
*Ranking Opinions with Few States in Population Protocols.* PODC 2026, Egham.
DOI [10.1145/3796701.3815913](https://doi.org/10.1145/3796701.3815913), arXiv:2605.18707.

## Model assumptions

- Population protocols (Angluin et al. 2006) on the complete interaction graph; deterministic two-way
  transitions `δ : Q → Q → Q × Q` (initiator, responder); `n ≥ 1` labelled agents (any `Fintype`).
  Framework: CSLib `Cslib/Computability/Distributed/PopulationProtocols/`, namespace
  `Cslib.PopulationProtocol`.
- Asynchronous, no failures, no randomness; adversarial scheduler constrained by
  - weak fairness: every unordered pair of distinct agents interacts infinitely often (Def. 2.1), or
  - global fairness (on labelled configurations) (Def. 2.2), for the ranking protocol.
- Inputs: colors `Fin k` (ordered setting) or an arbitrary finite type with equality only (unordered
  setting, Section 5). `x_c` = number of agents with input `c` (`inputCount`).
- Output: an output map on states; correctness = from some time on, forever, every agent outputs the
  required value (Theorem 1.1 also: output stability).

## Main results ↔ Lean

| Paper | Lean | File | Status |
|---|---|---|---|
| Weight `w(⟨i|j⟩)` (Sec. 3.1) | `w`, `w_eq_sub` | Weights.lean | ✔ |
| Def. 3.1 greedy independent sets | `greedy` | Layers.lean | ✔ (direct definition) |
| Def. 3.6 circle braket sets | `circle`, `nxt` | Layers.lean | ✔ |
| Lemma 3.2 (majority color) | `greedy_majority`, `diag_mem_layers_iff` | Layers.lean | ✔ |
| Lemma 3.3 (braket invariant) | `bra_const`, `kets_const`, `counts_execution` | Dynamics.lean | ✔ |
| Thm 3.4 (stabilization) | `eventually_const` | Dynamics.lean | ✔ (any execution) |
| Lemma 3.7 (stable config = ⋃ f(G_p)) | `eq_layers_of_stable`, `brakets_eq_layers` | Layers/Dynamics | ✔ |
| Thm 3.5 / **Thm 1.1** (Circles, k³ states) | `circles_correct`, `card_CState`, `circlesCore_main` | Circles.lean | ✔ |
| Thm 4.1 (TieReport) | **false** (no-tie case): `tieReport_counterexample_noTie`; tie case only under an ambiguous reading: `tieReport_counterexample_tie`; fixed: `tieReport_fixed_correct`, `card_TRState` | TieReport.lean | ✔ (counterexample + fix) |
| Thm 4.2 (TieSharing, 3k³) | `tieShare_correct` (sequential rule reading, status-dependent output map), `card_TSState`; clarifications: `tieShare_pre_counterexample` (simultaneous reading), `OutCounterexample.tieShare_out_counterexample` (output = `out` reading) | TieShare*.lean | ✔ |
| Thm 4.3 (TieBreak, 2k³ states) | `tieBreak_correct`, `card_TBState` | TieBreak.lean | ✔ |
| Thm 5.1 (Ordering) | `ordering_correct` (ordered-pair fairness), `orderingSymm_correct` (symmetrized, weak fairness); clarification (unordered-pair reading of Def. 2.1 fails): `ordering_not_weaklyFair` | UnorderedOrdering.lean | ✔ |
| Thm 5.2 (Ord-Circles) | `ordCircles_correct`, `ordCircles_ordering` (Lemma 8.13), `ordCirclesSymm_correct`, `card_ocState_le`; clarification (unordered-pair reading fails): `ordCircles_not_weaklyFair` | UnorderedOrdCircles.lean | ✔ |
| Thm 1.2 (ranking, 2k⁴, global fairness) | **false as written**: `Ranking.Counterexample.literal_not_correct`; fixed protocol: `Ranking.ranking_correct`, `final_closed` (L6.5), `reach_final` (P6.6), `card_RState` | Ranking*.lean | ✔ (counterexample + fix) |

All finished theorems were checked with `lean_verify` (axioms: `propext`, `Classical.choice`, `Quot.sound`).

## Findings

- **Theorem 4.1 is false** in the no-tie case (both readings of the ambiguous rule 2; 4 agents, k = 3).
  The tie-case counterexample is *ambiguity-dependent*: it needs the literal rule 2 and simultaneous
  application of rule 2 in both directions (with one direction first, no failure is found). A minimal fix
  (a diagonal agent also resets itself; tie spreading only affects `no_tie` agents) is proved correct.
  See `differencies.md` items 14–17.
- Theorem 4.2 (clarifications): it needs the rules applied sequentially (the simultaneous reading fails for
  3 agents) and an output map where winners output their own color; if every agent outputs `out`, the
  winners' claim fails (`differencies.md` 19, 19c).
- Several unstated but needed facts were added (e.g. termination needs no fairness; tie-break needs a
  rule for equal (weight, bra); Lemma 8.4's "max weight in f(G_q)" needs an arc argument).
- **Theorem 1.2 (ranking) is false for the protocol as written**: a token holder of its own bra color
  never updates its own bra ranking; globally fair counterexample with 3 agents, k = 2. One-line fix,
  proved correct. (`differencies.md` 29–31.)
- Theorems 5.1/5.2 hold for ordered-pair weak fairness, the natural reading since Sec. 2.1 uses a directed
  interaction graph (clarification: under the unordered reading they fail; symmetrized protocols fix it).
  Proof gap in Lemma 8.11 ("used labels never become free" is false; the lemma itself holds).
  (`differencies.md` 24–27.)
- Note: Lemma 6.2's backward direction needs the no-tie assumption of Def. 6.1 (standing in Section 6).
- Global fairness is defined on labelled configurations, a slightly stronger hypothesis than the
  paper's multiset view, so `ranking_correct` is slightly weaker than the paper's claim.

## Status

- No `sorry` in Weights, Layers, Dynamics, Circles, TieReport, TieBreak.
- No `sorry` in Unordered*, Ranking*.
- No `sorry` in TieShare*. Everything in this folder is sorry-free; all main theorems pass `lean_verify`.
- Not formalized: binary win/lose output variants (4k², 3k² states), Remark 1 (unordered ranking), time complexity (Sec. 3.3), exact-one-token-per-sector part of Lemma 8.3.
- Minor duplication: `UnorderedBasic.lean` has `Execution.ofSchedRec` (same role as `Podc`'s
  `Execution.ofSched`), and generic `eventually_const_of_antitone/monotone`.

## Tools

`tools/mc.py`: explicit-state model checker (subfolders `unordered/`, `ranking/`: the sub-agents' checkers, incl. a C++ one for multiset configurations) (exact for "every weakly/globally fair execution is eventually
always good" on small instances); `tools/protos.py`, `tools/tiereport_variants.py`, `tools/tieshare*.py`:
encodings of the protocols used to find the counterexamples. Run with `python3 -I`.

## CSLib candidates

- Done: the population-protocol framework (`Basic`, `Schedules`, `Eventually`, `Symmetrize`: protocols,
  executions, weak/global fairness, closed sets, homomorphisms, executions from schedules, `eventually_all`,
  ordered-pair fairness and symmetrization `P.symm`) moved to CSLib as
  `Cslib/Computability/Distributed/PopulationProtocols/` (namespace `Cslib.PopulationProtocol`, same
  declaration names; vasnesterov/cslib PR #23).
- Possibly: the cyclic-successor/arc lemmas in `Weights.lean`/`Layers.lean` (`nxt`, `nxt_injOn`,
  `w_add_of_closest`) as modular-arithmetic facts.

## Token spend (rough)

Core (framework + Theorem 1.1): ~0.15M tokens. Tie handling (4.1, 4.3, model checking): ~0.25M.
Section 5 (sub-agent): ~0.35M. Section 6 (sub-agent): ~0.31M. Section 4.2 (sub-agent): ~0.45M.
Total ≈ 1.6M tokens.
