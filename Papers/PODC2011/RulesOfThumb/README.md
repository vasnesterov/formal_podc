# Distributed Computing with Rules of Thumb — PODC 2011

Aaron D. Jaggard, Michael Schapira, Rebecca N. Wright. *Distributed computing with rules of thumb.*
PODC 2011. DOI [10.1145/1993806.1993870](https://doi.org/10.1145/1993806.1993870). Formalized version:
arXiv [0910.1585](https://arxiv.org/abs/0910.1585) v2 (*Distributed Computing with Adaptive Heuristics*,
the ICS 2011 / full version); numbering follows it.

**Verdict: ❌ False claim.** The main impossibility result, Theorem 4.1, is true for deterministic,
self-independent, stationary bounded-recall reaction functions (the version restated and proved in
Appendix F) and for non-stationary 1-recall ones. Examples 4.2 and 4.3 are correct. The game-theoretic
application, Corollary 5.2 (and Theorems 5.1 and B.2), is false as stated: with "consistent tie-breaking",
a pure Nash equilibrium need not be a stable state of best-response dynamics. For non-stationary reaction
functions the paper's proof has a gap; we repair it for 1-recall, and for `k ≥ 2` it remains open.

## Mistakes in the paper

* **Corollary 5.2 / Theorem B.2 / Theorem 5.1 are false as stated (false statement).** Corollary 5.2
  says that if a game has two pure Nash equilibria, then best-response dynamics with consistent
  tie-breaking can fail to converge asynchronously. Counterexample: a 2×2 game. Player 0 gets 1
  unless it plays `y` against `x`, so `x` weakly dominates `y`. Player 1 gets 1 iff it matches player 0.
  The pure equilibria are `(x,x)` and `(y,y)`. Break ties towards `x`. Then player 0 always plays `x`,
  player 1 copies player 0, and every fair dynamics converges to `(x,x)`. The proof applies Theorem 4.1
  to the Nash equilibria, but `(y,y)` is not a fixed point of the tie-broken best-response map, so it is
  not a stable state. The same example refutes Theorem 5.1 ("all bounded-recall self-independent
  dynamics can oscillate"). What is true, and what we prove, is the statement for two equilibria that are
  fixed points of the best-response map; this is automatic when best responses are unique.
  (`corollary_5_2_false`, `theorem_5_1_false`; repaired: `corollary_5_2`, `corollary_5_2_of_unique`)
* **Theorem 4.1 for non-stationary reaction functions: proof gap.** The main text says Theorem 4.1
  holds "even if nodes' reaction functions are not stationary". The valency argument (Appendix F)
  builds a fair run in which every history is bivalent, meaning at least two limits are still possible.
  For stationary functions such a run cannot converge: once the run sits at a limit `c` for `k` steps,
  `c` is a fixed point, so only `c` remains reachable. For non-stationary functions this step fails. A
  run can converge to `c` while every history stays bivalent, because `c` may be reproduced only at the
  time steps at which the run happens to activate the nodes. Appendix F.7 (Theorem F.14) avoids the
  problem by quietly changing what a stable state is ("a vector of actions and a time after which it is
  a fixed point"). That is not the notion of Section 3, and the proof also assumes finite action spaces.
  Appendix F.8 extends it to `k`-recall only by a sketch. Two further defects: the act-and-tell
  translation lets `W` reveal an empty set of reactions, and the "number of time steps" argument then
  counts steps with an empty activation set, which Section 3 forbids. We repair the argument as
  follows. The FLP-style extension lemma holds for non-stationary `k`-recall; we only allow `W` when
  something is pending. Non-convergence follows once the limit of every fair dynamics is eventually
  absorbing. We prove that absorption property for 1-recall functions with arbitrary action spaces: a
  node that deviates infinitely often could be made to oscillate fairly. For non-stationary `k`-recall
  with `k ≥ 2` we could neither prove nor refute Theorem 4.1. A brute-force search over small periodic
  systems found no counterexample. (`not_convergent_of_absorbing`, `absorbingAfter_of_oneRecall`,
  `theorem_4_1_oneRecall`)
* **"Stable state" must mean the limit of a *fair* dynamics (under-specified definition).** Section 3
  calls `a` a stable state when the `(s⁰, σ)`-dynamics converges to `a`, for a schedule `σ` that need not
  be fair. Read literally, Theorem 4.1 is false. Take the system in which every node always plays `x`. It
  is historyless, self-independent and convergent, but the unfair dynamics that only ever activates
  node 0 converges to `(x,y)`. The intended reading is clear from the paper's remark that in the
  historyless case the stable states are exactly the fixed points; we use it. (`stableState_literal_reading`)
* **Randomized reaction functions (not formalized).** The main text says Theorem 4.1 also holds for
  randomized reaction functions, but the paper never defines convergence of randomized dynamics:
  every realization, or almost surely. The proof in Appendix F treats deterministic functions only.
  We formalize deterministic reaction functions.
* Typos and slips:
  - Section 3 types `f(i,t) : H_t → Δ(A_i)`, but the dynamics applies `f(i,w+1)` to `s⁰ ∈ H_w`. The
    input is `H_{t−1}`.
  - Section 3 writes `s(t) = a` for a history `s(t)`; it means the last profile.
  - "Safe" (Appendix F, Example 4.2) is used for "convergent".
  - In the proof of Lemma F.12, case `e = e_i, e' = W`, "the second color equality" should be the
    first one.
  - Lemma F.13's "activate `v` first" suffices only for 1-recall. For `k`-recall `v` must be activated
    `k` times, as F.8 notes.
  - Def. F.4 defines a "fair extension" as an arbitrary finite extension; the fairness actually used is
    the one in the proof of Lemma F.8.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`)
* Finitely many nodes `ι` (a `Fintype`). Node `i` has an arbitrary action type `A i`, so infinite
  action spaces are allowed.
* A history `h ∈ H_w`, `w ≥ 1`, is stored as the current profile plus the earlier ones, most recent
  first. `h.time = w`.
* Reaction functions are **deterministic**: `F.f i t h` is node `i`'s action at time step `t` after
  the history `h`.
* A schedule `σ : ℕ → Finset ι` activates the nonempty set `σ t` at absolute time `t`. The
  `(s⁰, σ)`-dynamics `F.run s⁰ σ` starts at time `w + 1` with any initial history. Activated nodes
  react simultaneously, so the model is synchronous lock-step with an adversarial asynchronous
  activation pattern. There are no failures and no randomness, and monitoring is perfect.
* `Fair σ`: every node is activated infinitely often. `Convergent`: for every initial history and
  every fair schedule, the profile is eventually constant. `IsStableState a`: some fair dynamics
  converges to `a`.
* Restrictions, as in Section 3:
  - `SelfIndependent`: the reaction depends only on the other nodes' actions.
  - `HasRecall i k`: on histories with at least `k` entries, the reaction at each time step depends
    only on the `k` most recent profiles.
  - `Stationary i k`: one function of the `k` most recent profiles for all time steps.
  - `Historyless`: `Stationary i 1`.

**Proof structure.**
* `Valency.lean`: the stable colouring `F.lims h P`, the set of limits of fair dynamics from `h` whose
  next activation set contains `P`. It also proves that two histories differing only in node `j`'s
  actions become equivalent after `j` is activated alone `k` times.
* `FLP.lean`: the act-and-tell model, in which `e_j` adds `j` to the pending set and `W` reveals a
  nonempty pending set. It proves the extension lemma `exists_bivalent_after` (Lemmas F.8 + F.12) for
  non-stationary `k`-recall functions. We prove it directly in this model rather than through the
  abstract IoD framework.
* `Bivalence.lean`: an initial bivalent history (Lemma F.13 and its F.7/F.8 variants), and segments.
* `Concat.lean`: concatenation of segments into a fair schedule (the iteration of Theorem F.9).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.1 (stationary bounded recall, as restated in App. F) | `System.theorem_4_1` | `Theorem41.lean` |
| Theorem 4.1 / F.14 (non-stationary 1-recall, any action spaces) | `System.theorem_4_1_oneRecall` | `NonStationary.lean` |
| Theorem 4.1, non-stationary `k`-recall: reduction to absorption | `System.not_convergent_of_absorbing` | `Theorem41.lean` |
| Lemmas F.8 + F.12 (extension lemma, non-stationary `k`-recall) | `System.exists_bivalent_after`, `System.exists_segment` | `FLP.lean`, `Bivalence.lean` |
| Lemma F.13 (a bivalent history exists) | `System.exists_biv_hist` | `Bivalence.lean` |
| Theorem F.9 (fair forever-bivalent run) | `System.exists_fair_of_segments` | `Concat.lean` |
| Example 4.2 | `example_4_2` | `Examples.lean` |
| Example 4.3 | `example_4_3` | `Examples.lean` |
| Corollary 5.2 / Thm B.2 as stated: false | `corollary_5_2_false` | `Games.lean` |
| Theorem 5.1 as stated: false | `theorem_5_1_false` | `Games.lean` |
| Corollary 5.2 corrected | `corollary_5_2`, `corollary_5_2_of_unique` | `Games.lean` |
| Literal "stable state" makes Thm 4.1 false | `stableState_literal_reading` | `Examples.lean` |

**Not formalized.**
* Theorem 4.1 for non-stationary `k`-recall with `k ≥ 2` (open, see above), and randomized reaction
  functions.
* Sections 6–8: `r`-convergence and snakes in boxes (Theorem 6.2), the communication and computational
  complexity results (Theorems 7.1, 7.2), and no-regret dynamics.
* The other applications of Section 5 (circuits, diffusion, BGP, congestion control) and the
  consensus results of Appendix G.

**Trust.**
* No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity:
  - `copySys_not_convergent`: two nodes that copy each other satisfy all hypotheses of Theorem 4.1.
  - Examples 4.2 and 4.3 are convergent systems with several stable states.
  - `ex43_not_selfIndependent` derives the failure of self-independence from Theorem 4.1.
* The model is new (paper-local, `Model.lean`). The stateless-protocol model of PODC 2017
  (`Papers/PODC2017/StatelessComputation`) has arc labels and `r`-fair schedules and no histories, so
  it does not fit. CSLib candidates (marked `-- CSLib candidate`): the adaptive-heuristics model with
  bounded recall (`Model.lean`), the act-and-tell extension lemma (`FLP.lean`), and segment
  concatenation (`Concat.lean`).
