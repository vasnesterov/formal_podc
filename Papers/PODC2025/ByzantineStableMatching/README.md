# Byzantine Stable Matching (PODC 2025)

Andrei Constantinescu, Marc Dufay, Diana Ghinea, Roger Wattenhofer. *Byzantine Stable Matching.*
PODC 2025, DOI 10.1145/3732772.3733525; arXiv:2502.05889v2 (full version with appendix; the version
formalized, numbering follows it).

## Status

**Complete, no `sorry`, no axioms.** All main theorems were checked with `lean_verify`: they use only
`propext`, `Classical.choice` and `Quot.sound`. `lake build Papers.PODC2025.ByzantineStableMatching.Main`
succeeds.

The classical agreement protocols are taken as **explicit hypotheses**, as the task allows: Fitzi–Maurer
general-adversary BB, Dolev–Strong, and the paper's Theorems 8/9 (Phase-King BA/BB with omissions). See
`Hypotheses.lean`.

All reductions and impossibility proofs are formalized: Lemmas 1, 2, 3, 4 (Q3), 5, 6, 7, 8, 9–12, 13.
The sufficiency side uses Gale–Shapley (Theorem 1), the parallel composition BB → IC, the majority and
signature relays with omissions, and the protocol ΠbSM.

**Findings** (details in `differencies.md`):
- The characterizations (Theorems 2–7) are **false for `k = 1`**: bSM is then trivially solvable. Lean
  counterexample: `bSM_solvable_k1`, `theorem2_only_if_false_k1`. They are **true for all `k ≥ 2`** and
  are proved for all `k ≥ 2`.
- The paper's proofs have three gaps:
  - Theorem 2's necessity proof does not cover `k = 2`.
  - Lemma 13's reduction through Lemma 3 is invalid, e.g. for `k = 4` (`lemma3_not_enough_for_lemma13`).
  - Theorem 7's case `tR = k`, `tL < k/3` cites an inapplicable theorem.
- Several typos (Corollary 1 should say `tR < k/2`, among others).

## Model (explicit)

The shared model is `Cslib/Computability/Distributed/Byzantine/LockStep/`.

- `2k` parties `Fin k ⊕ Fin k` (`L = inl`, `R = inr`) run deterministic protocols in **synchronous
  lock-step rounds**.
- Communication is over a fixed graph (`fully`, `oneSided`, `bipartite`) with authenticated
  point-to-point channels. There is no randomness.
- The Byzantine adversary is **static**. It may corrupt at most `tL` parties in `L` and `tR` in `R`
  (`thresholds k tL tR`). Byzantine behaviour is arbitrary, including rushing.
- In the **authenticated setting**, signatures are ideal unforgeable abstract tokens. The adversary is
  rushing and eavesdropping.
- A party's output is its first decision.
- bSM (Definition 1) and sSM (Section 3) are stated as specs on the inputs, the honest set and the
  decision relation (`Problem.lean`).

## Main results ↔ Lean (namespace `Papers.PODC2025.ByzantineStableMatching`)

| Paper | Lean | File |
|---|---|---|
| Thm 1 (Gale–Shapley) | `Cslib.StableMatching.galeShapley`, `galeShapley_isStable` (computable) | CSLib `Cslib/Algorithms/Lean/StableMatching/GaleShapley.lean` |
| Def 1 bSM, sSM, networks, adversary | `bSM`, `sSM`, `CommonProps`, `fully`, `oneSided`, `bipartite`, `thresholds` | `Problem.lean` |
| Lemma 1 (BB ⇒ bSM) | `lemma1`, `lemma1_auth` (via `IC_of_BB`, `offlineMatch`) | `Lemma1.lean`, `Cslib/Computability/Distributed/Byzantine/LockStep/Parallel.lean` |
| Lemma 2 (sSM ≤ bSM) | `lemma2`, `lemma2_auth` | `Problem.lean` |
| Lemma 3 (scaling) | `lemma3`, `lemma3_auth`; general `Solvable.of_groupSim`, `SolvableAuth.of_groupSim` | `Scaling.lean` |
| Lemma 4 / Thm 10 | `lemma4_Q3` (proved), `lemma4` (from hypothesis `FitziMaurerBB`) | `Hypotheses.lean` |
| Lemma 5 (12-node cover) | `lemma5` (every `k ≥ 2`, every network), `Lemma5.not_solvable_of_groups` | `Lemma5.lean` |
| Lemma 6, Cor 1, Cor 2 | `Solvable.relay_majority` (generic), `corollary1`, `corollary2` | `Cslib/Computability/Distributed/Byzantine/LockStep/Relay.lean`, `Main.lean` |
| Lemma 7 (8-cycle) | `lemma7` (every `k ≥ 2`, every network without `L–L` edges) | `Lemma7.lean` |
| Lemma 8, Cor 3, Cor 4 | `SolvableAuth.relay_sig` (generic), `corollary34` | `Relay.lean`, `Main.lean` |
| Lemma 10 (relay with omissions) | `relay_sig_sim`, `relay_sig_omissions`, `terminatesBy_relay_sig` | `Relay.lean` |
| Thms 8, 9 | hypotheses `OmissionBA`, `OmissionBB` | `Hypotheses.lean` |
| ΠbSM, Lemmas 11, 12 | `PiBSM.phi`, `PiBSM.phi_bSM` | `PiBSM.lean` |
| Lemma 9 | `lemma9` (bipartite and one-sided) | `Main.lean` |
| Lemma 13, Cor 5 | `lemma13_sSM`, `bSM_not_solvableAuth_R`, `bSM_not_solvableAuth_L` | `Lemma13.lean`, `Necessity.lean` |
| **Theorem 2** | `theorem2` | `Main.lean` |
| **Theorem 3** | `theorem3` | `Main.lean` |
| **Theorem 4** | `theorem4` | `Main.lean` |
| **Theorem 5** | `theorem5` | `Main.lean` |
| **Theorem 6** | `theorem6` | `Main.lean` |
| **Theorem 7** | `theorem7` | `Main.lean` |
| `k = 1` counterexample | `bSM_solvable_k1`, `bSM_solvableAuth_k1`, `theorem2_only_if_false_k1` | `Necessity.lean` |
| side symmetry ("the case … is symmetrical") | `sSM_solvable_swap`, `bSM_solvableAuth_swap`, … | `Symmetry.lean` |

Theorems 2–7 are stated as `↔` for `k ≥ 2`. Sufficiency takes the hypotheses `FitziMaurerBB`,
`DolevStrongBB`, and `OmissionBA`/`OmissionBB` (as needed). Necessity uses no hypotheses.

## Infrastructure built (shared, `Podc/`)

- `Cslib/Computability/Distributed/Byzantine/LockStep/`:
  - `Basic`: the synchronous lock-step model.
  - `Cover`: the generic FLM covering/shifting-scenario lemma.
  - `Auth`: the ideal-signature model and legality of cover adversaries.
  - `Relabel`: renaming parties.
  - `Agreement`: the BB/BA/IC/weak-agreement specs.
  - `Parallel`: parallel composition and IC from BB.
  - `Relay`: channel simulation by majority or signature relays, with omissions.
- CSLib `Cslib/Algorithms/Lean/StableMatching/` (namespace `Cslib.StableMatching`): stable matchings and a
  computable Gale–Shapley with a stability proof.

## CSLib candidates

- Done: stable matching and Gale–Shapley moved to CSLib (`Cslib/Algorithms/Lean/StableMatching/`, same
  declaration names under `Cslib.StableMatching`; vasnesterov/cslib PR #25).
- Done: the synchronous lock-step model (`Basic`, `Cover`, `Auth`, `Relabel`, `Agreement`, `Parallel`, `Relay`)
  moved to CSLib (`Cslib/Computability/Distributed/Byzantine/LockStep/`, namespace `Cslib.Byzantine.LockStep`,
  same declaration names; PRs #31, #32), with a bridge to the partially synchronous model (PR #36).

## Token spend

Roughly 1.2M tokens in total, including 3 subagents: Gale–Shapley plus parallel/Lemma 1, relabel plus
relays, and Lemma 3.
