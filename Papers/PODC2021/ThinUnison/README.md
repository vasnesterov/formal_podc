# A Thin Self-Stabilizing Asynchronous Unison Algorithm — PODC 2021

Yuval Emek, Eyal Keren. *A Thin Self-Stabilizing Asynchronous Unison Algorithm with Applications to Fault Tolerant
Biological Networks.* PODC 2021, pp. 93–102. DOI [10.1145/3465084.3467922](https://doi.org/10.1145/3465084.3467922).
Formalized version: the full version, arXiv:2102.12787v2 (18 May 2021).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Theorem 1.1 is correct and fully proved, with explicit constants. AlgAU with
`k = 3D + 2` (`12D + 6` states) is a self-stabilizing asynchronous unison on graphs of diameter `≤ D`, and it
stabilizes within `70(D+1)³` rounds. The analysis has several minor gaps, all repaired. **Corollary 1.2 (the
synchronizer) is false for arbitrary tasks, as stated.** It holds for static tasks such as LE and MIS, which are the
paper's applications.

## Mistakes in the paper

- **Corollary 1.2 is false as stated (false statement).** The synchronizer Π* does not make the nodes simulate one
  global synchronous execution. Each node shows the synchronous execution at its *own* simulated round, and
  neighbouring rounds may differ by 1. Tasks constrained at every time instant therefore cannot be transferred.
  Counterexample with `D = 1`: the task "all nodes output the same bit at all times, and the outputs change
  infinitely often".
  - Synchronously it is solved on every complete graph within one round by `δ(b, S) = ¬(true ∈ S)`.
  - On `K₂` under the fair round-robin schedule, no deterministic stone-age algorithm (Π* included) solves it. A
    node that is not activated keeps its output, so the first output change after agreement breaks agreement.

  The construction is correct for *static* tasks (eventually fixed legal outputs). We prove that version with the
  bound `f + N(D) + D` rounds. (`toggle_sync`, `no_async_alg_roundRobin`, `corollary_1_2`)
- **Lemma 2.19: the constant `k(k−1)` is not justified by the argument (proof gap; we prove `4(k−1)²`).** The proof
  charges one application of Lemma 2.13 per level. It ignores three things:
  - both endpoints of an edge may move;
  - a node may have several non-protected edges that resolve one after another;
  - edges `{k, −k}` may become non-protected in the meantime.

  We prove `4(k−1)²` in two phases. The node first moves inwards until it is protected or at `±1`; then every
  neighbour reaches `∓1` or becomes protected. The final `O(D³)` is unaffected. We did not decide whether
  `k(k−1)` itself holds. (`lemma_2_19`)
- **Lemma 2.13: the proof fails for `|ℓ| = 1`.** The proof needs the endpoint at level `ℓ` to make an AF move.
  Levels `±1` have no faulty turn, so a non-protected node there is stuck. The lemma is used only with `|ℓ| ≥ 2`,
  so we prove it under that hypothesis. Whether the `|ℓ| = 1` case is false is open. The time bound also has a
  typo, `t'` for `t`. (`lemma_2_13_edge`)
- **Lemma 2.22: the potential argument re-chooses `x_t` at every time.** When the node to which Lemma 2.19 was
  applied becomes protected, `x_t` may already be a different node at the same distance. So "the distance decreases
  or `v` becomes grounded" does not follow literally. Repair: fix the walk at the start of each phase and recurse
  on its length. (`lemma_2_22_aux`, `lemma_2_22`)
- **Obs 2.9 / Lemma 2.20: off by one at `s = t'`.** Obs 2.9 needs `|λ_v^s| < k − d` only for `s < t'`. With
  `s = t'` included, the application in Lemma 2.20 at `d = D` fails, because `v` is at level exactly `k − D` at
  `t'`. The paper's proof only uses `s < t'`. (Lemma 2.20's conclusion for an arbitrary later `t'` also needs
  persistence of protection after `T₁`; the paper does supply this, via Lemmas 2.10 and 2.18.)
  (`AURun.obs29`, `lemma_2_20`)
- **Minor.**
  - Obs 2.8 omits a short extremal-point step. Pairwise distances `≤ D` imply a window of `D + 1` levels only
    because `2k > 3D`.
  - Lemma 2.11 compares levels cyclically (presentation only).
  - Lemma 2.14's inner induction needs strong induction on the remaining distance.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Finite simple graph with `G.ediam ≤ D` (Mathlib), which implies connectivity.
- Stone-age model: anonymous deterministic finite-state nodes that sense the *set* of states in their closed
  neighbourhood. The paper's model allows randomized transitions, but AlgAU is deterministic.
- Schedule: an adversarial asynchronous daemon `A : ℕ → Set V`, which may also activate the empty set. It is
  fair, i.e. every node is activated infinitely often. Rounds are measured by the paper's operator `ϱ`.
- Faults: arbitrary initial configuration, no other faults.
- AU specification: clocks in `ZMod (2k)`; neighbours differ by at most 1; clocks change only by `+1`; at least `i`
  ticks in `[t, ϱ^{d+i}(t))`.
- The AlgAU transition rules (Table 1) are formalized as written. An explicit-state model checker
  (`tools/algau.py`, on K₂, K₃, P₃, C₄) was used to sanity-check this reading.

**Main results in Lean** (namespace `ThinUnison`).

| Paper | Lean | File |
|---|---|---|
| AlgAU, `4k − 2` states | `algAU`, `card_turn`, `card_states` | `Defs.lean`, `StateSpace.lean`, `Main.lean` |
| **Theorem 1.1** (any `k ≥ 3D + 2`; `d = diam G`) | `theorem_1_1`, `theorem_1_1_general`, `theorem_1_1_diam` | `Main.lean` |
| `O(D³)` bound | `stabRounds_le` (`≤ 70(D+1)³`) | `Main.lean` |
| Obs. 2.1–2.9, Lemmas 2.10–2.11 | `AURun.obs21` … `AURun.obs29`, `auFrom_of_allGood` | `Observations.lean`, `Good.lean` |
| Lemmas 2.12–2.14, Cor. 2.15 | `AURun.lemma_2_12`, `AURun.lemma_2_13_edge`, `AURun.lemma_2_14`, `AURun.corollary_2_15` | `OutProtected.lean` |
| Lemmas 2.16, 2.18, Cor. 2.17 | `AURun.lemma_2_16`, `AURun.corollary_2_17`, `AURun.lemma_2_18` | `Justified.lean` |
| Lemmas 2.19–2.22 | `AURun.lemma_2_19`, `AURun.lemma_2_20`, `AURun.lemma_2_21`, `AURun.lemma_2_22` | `Protected.lean` |
| Corollary 1.2, static tasks | `synchronizer_simulation`, `corollary_1_2` | `Synchronizer.lean` |
| Corollary 1.2 false for arbitrary tasks | `toggle_sync`, `no_async_alg_roundRobin` | `Counterexample.lean` |

**Not formalized.** Theorems 1.3/1.4 (randomized LE and MIS, w.h.p. analysis). Corollary 1.2 for randomized Π.
The `|Q*|` count.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. For
non-vacuity, `Main.lean` instantiates Theorem 1.1 on `K₃` under the synchronous schedule. The synchronous and
round-robin schedules are proved fair. The stone-age model and the unison specification come from CSLib,
`Cslib/Computability/Distributed/SelfStabilization/`. `SyncStabilizes` is pseudo-stabilization
within `f` rounds of the synchronous executions (`syncStabilizes_iff`, shared notions of
`Cslib/Computability/Distributed/SelfStabilization/`).
