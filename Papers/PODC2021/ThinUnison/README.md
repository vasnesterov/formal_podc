# A Thin Self-Stabilizing Asynchronous Unison Algorithm (PODC 2021)

Yuval Emek, Eyal Keren. *A Thin Self-Stabilizing Asynchronous Unison Algorithm with Applications to
Fault Tolerant Biological Networks.* PODC 2021, pp. 93–102. DOI 10.1145/3465084.3467922.
Full version: arXiv (PDF in `papers/2021/`).

## Status

- **Theorem 1.1: fully formalized and verified.** No `sorry`. `lean_verify` shows only `propext`,
  `Classical.choice` and `Quot.sound`. The result:
  - AlgAU with `k = 3D+2` has `12D+6` states.
  - It is a deterministic self-stabilizing asynchronous unison algorithm on graphs of diameter `≤ D`,
    under every fair asynchronous schedule.
  - It stabilizes within an explicit `N(D) ≤ 70 (D+1)³` rounds.
- All of Observations 2.1–2.9 and Lemmas 2.10–2.22 are proved. Some are in repaired or slightly
  generalized form; see `differencies.md`.
- The paper is morally correct. The issues found are all minor:
  - Obs 2.8 omits a short extremal-point step; Lemma 2.11 has an imprecise cyclic comparison (presentation only).
  - Lemma 2.13 fails for `|ℓ| = 1` as proved, but it is never used there.
  - Lemma 2.19's constant `k(k−1)` is not justified by its argument; we prove `4(k−1)²`.
  - Lemma 2.22's choice of `x_t` needs a fixed-walk argument.
  - Obs 2.9 / Lemma 2.20 have an off-by-one at `s = t'`.
- Corollary 1.2 (synchronizer): **formalized for deterministic Π and static tasks** (`corollary_1_2`,
  `≤ f + 71(D+1)³` rounds). As stated for *arbitrary* tasks, the corollary is **false** (Lean counterexample for `D = 1`); see below.
- Theorems 1.3/1.4 (randomized LE/MIS): **skipped**. They are out of scope: randomized, with w.h.p.
  analysis.

## Model (explicit assumptions)

- **Graph:** finite simple graph `G` with diameter at most `D` (Mathlib's `G.ediam ≤ D`; equivalently,
  `SimpleGraph.ediam_le_coe_iff`, every two nodes are joined by a walk of length `≤ D`).
- **Stone age model:**
  - Anonymous, deterministic finite-state nodes running the same transition function
    `δ : Q → Set Q → Q`.
  - A node senses the *set* of states present in its closed neighbourhood.
- **Schedule:**
  - An adversarial asynchronous (distributed) daemon `A : ℕ → Set V` chooses which nodes are
    activated at each step. Activated nodes apply `δ` simultaneously; the others keep their state.
  - Fairness: every node is activated infinitely often.
  - Time is measured in rounds: `ϱ(t)` is the earliest time by which every node has been activated
    since `t`, and `R(i) = ϱ^i(0)`.
- **Faults:** arbitrary initial configuration (self-stabilization), no other faults.
- **AU task (`Cslib.StoneAge.AUFrom`):**
  - Clock values in `ZMod (2k)`.
  - Safety: neighbours' clocks differ by `−1`, `0` or `+1`.
  - `+1`-only updates.
  - Liveness: `≥ i` updates in `[t, ϱ^{d+i}(t))`, with `d = diam(G)` or any bound `≤ D`.

## Main theorems ↔ Lean

| Paper | Lean (namespace `ThinUnison`) | File |
|---|---|---|
| AlgAU (Sec. 2.2, Table 1) | `Turn`, `δ`, `algAU`, `aaCond_iff` | `Defs.lean` |
| state space `4k−2` | `card_turn`, `card_states` (`12D+6`) | `StateSpace.lean`, `Main.lean` |
| **Theorem 1.1** | `theorem_1_1`, `theorem_1_1_diam`, `theorem_1_1_exists`, `theorem_1_1_general` (any `k ≥ 3D+2`) | `Main.lean` |
| time bound `O(D³)` | `stabRounds`, `stabRounds_le` (`≤ 70 (D+1)³`) | `Main.lean` |
| Obs 2.1–2.6 | `AURun.obs21` … `obs26` (+ pure cores `obs21_pure` …) | `Observations.lean` |
| Obs 2.7/2.9 | `natAbs_le_of_walk`, `AURun.obs29` | `Observations.lean` |
| Obs 2.8 + Lemma 2.11 | `exists_offsets`, `uclk_inv`, `uclk_rho_iter`, `auFrom_of_allGood` | `Good.lean` |
| Lemma 2.10 | `AURun.allGood_succ`, `allGood_le` | `Good.lean` |
| Lemma 2.12 | `AURun.fa_core`, `AURun.lemma_2_12` | `OutProtected.lean` |
| Lemma 2.13 | `AURun.lemma_2_13_edge` (paper form, `2 ≤ \|ℓ\|`), `lemma_2_13` (node form), `lemma_2_13'` | `OutProtected.lean`, `Protected.lean` |
| Lemma 2.14 | `AURun.lemma_2_14` (exact bound), `lemma_2_14_aux` | `OutProtected.lean` |
| Corollary 2.15 | `AURun.corollary_2_15`, `outRounds` | `OutProtected.lean` |
| Lemma 2.16 | `AURun.lemma_2_16` | `Justified.lean` |
| Corollary 2.17 | `AURun.corollary_2_17` (`T₁ = ϱ^{2k−3}(T₀)`) | `Justified.lean` |
| Lemma 2.18 | `AURun.lemma_2_18` | `Justified.lean` |
| Lemma 2.19 | `AURun.lemma_2_19` (`4(k−1)²` rounds) | `Protected.lean` |
| Lemma 2.20 | `AURun.lemma_2_20_claim`, `AURun.lemma_2_20` | `Protected.lean` |
| Lemma 2.21 | `Grounded`, `AURun.lemma_2_21` | `Protected.lean` |
| Lemma 2.22 | `AURun.lemma_2_22_aux`, `AURun.lemma_2_22` | `Protected.lean` |
| Corollary 1.2 false for arbitrary tasks | `toggle_sync`, `no_async_alg`, `no_async_alg_roundRobin` | `Counterexample.lean` |
| Corollary 1.2 (deterministic, static tasks) | `synchronizer`, `synchronizer_simulation`, `corollary_1_2`, `corollary_1_2_exists` | `Synchronizer.lean` |

Other files:
- `Step.lean`: one-step transition lemmas.
- `LvlTac.lean`: the tactic `lvl_omega` for level arithmetic.
- `tools/algau.py`: an explicit-state model checker used to validate the reading of the algorithm.

Non-vacuity (`Main.lean`):
- the synchronous and round-robin schedules are fair (`Cslib.StoneAge.fair_sync`, `fair_roundRobin`);
- `R_sync`;
- an instantiation of Theorem 1.1 on `K₃` with the synchronous schedule.

## Corollary 1.2 (synchronizer)

`Synchronizer.lean`:
- **Construction.** `synchronizer P k` builds Π* with states `Q × Q × Turn k`, as in Section 4. On an
  AlgAU AA step the node computes `(δ_Π(q, S), q, ν')`, where
  `S = {r | (r,·,ν) or (·,r,ν') is sensed}`. Otherwise the first two coordinates are unchanged.
- **`synchronizer_simulation`.** From `R(N(D) + D)` on, every node shows the synchronous execution of Π
  (from some configuration `D0`) at its own simulated round `r t v`:
  - `r t v` is monotone in `t`;
  - it is `≥ i` from `R(N(D) + D + i)` on;
  - it differs by at most 1 across edges.
- **`corollary_1_2` / `_general` / `_exists`.** Take a deterministic synchronous Π that self-stabilizes
  on `G` within `f` rounds to a *static* legal output (`SyncStabilizes`). Then Π* stabilizes to a legal
  fixed output by `R(N(D) + D + f)`, i.e. within `f + O(D³)` rounds.
- **Not formalized:**
  - randomized Π with expectation / w.h.p. bounds;
  - the `|Q*| = O(D|Q|²)` count, which is immediate.
- **Paper error.** Corollary 1.2 is stated for arbitrary tasks T, and that is false already for
  `D = 1`, i.e. complete graphs. Counterexample in Lean (`Counterexample.lean`), for the task "all
  nodes output the same bit at every time, and the outputs change infinitely often":
  - `toggle_sync`: the synchronous algorithm `δ(b, S) = ¬(true ∈ S)` solves it within 1 round on every
    complete graph. It does not work on, e.g., `P₃`, where it cycles; the class `D = 1` suffices.
  - `no_async_alg_roundRobin`: on `K₂` under the fair round-robin schedule, no deterministic SA
    algorithm solves it, Π* included. A node that is not activated keeps its output, so the first
    output change after agreement breaks agreement.
  - The construction is correct for tasks whose specification tolerates per-node skew of the
    simulated rounds, e.g. static tasks such as LE and MIS. Those are the paper's applications.

## Infrastructure (migrated to CSLib)

- `Cslib/Computability/Distributed/SelfStabilization/StoneAge.lean`:
  - the stone-age model (deterministic);
  - executions under asynchronous schedules and fairness;
  - the round operator `ϱ` with its monotonicity/iteration API;
  - fair synchronous and round-robin schedules;
  - interval-induction helpers.
- `Cslib/Computability/Distributed/SelfStabilization/Unison.lean`: the asynchronous-unison spec `AUFrom` (the former `DiamLE` was dropped in favour of
  Mathlib's `ediam`).


## Token spend (rough)

About 0.6M tokens in total:
- about 0.45M for the main agent;
- about 0.13M for the subagent on Lemmas 2.10/2.11 (good phase);
- about 0.15M for the subagent on Corollary 1.2 (synchronizer).
