# Time-Optimal Self-Stabilizing Leader Election in Population Protocols — PODC 2021

Janna Burman, Ho-Lin Chen, Hsueh-Ping Chen, David Doty, Thomas Nowak, Eric Severson, Chuan Xu.
*Time-Optimal Self-Stabilizing Leader Election in Population Protocols.* PODC 2021. DOI
[10.1145/3465084.3467898](https://doi.org/10.1145/3465084.3467898). Formalized version: arXiv
[1907.06068](https://arxiv.org/abs/1907.06068) v5 (29 Nov 2021); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The structural results hold: SSLE needs `≥ n` states and exact knowledge
of `n` (Theorem 2.1, proved here), `Silent-n-state-SSR` solves ranking (Lemmas 2.2, 2.3, Theorem 2.4), and
Observation 2.5 holds. **`Optimal-Silent-SSR` as printed (Protocol 3) never stabilizes**: an off-by-one in the
recruitment guard means rank `n` can never be assigned. With the evidently intended guard `≤ n` we prove the protocol
correct: from every valid configuration a silent, correctly ranked configuration is reachable (for
`Rmax, Dmax ≥ 2`, which the paper's choices satisfy). Observation 2.6's explicit tail bound fails for `n = 2` (and for `n = 3`, large `α`). The time bounds and Section 5
(`Sublinear-Time-SSR`) are not formalized.

## Mistakes in the paper

* **Protocol 3 (`Optimal-Silent-SSR`) is incorrect as printed; Theorem 4.3 fails for it.** Line 9 lets a settled
  agent recruit only if `2 · i.rank + i.children < n`. New ranks are created only by `Reset` (rank 1) and by
  recruitment (rank `2·rank + children`), so **no agent can ever obtain rank `n`** unless it already had it. Hence
  from the all-`Unsettled` configuration — or from any configuration after a complete reset — no correctly ranked
  configuration is ever reached, for every `n ≥ 2` and all `Rmax, Dmax, Emax`; the protocol stabilizes with
  probability 0. Figure 1 (rank 12 assigned for `n = 12`) shows that `≤ n` is meant. This is a typo-level fix, but
  the printed protocol is false. (`OptimalSilent.asWritten_never_ranked`, `asWritten_not_selfStabilizes`; fixed
  version: `OptimalSilent.fixed_selfStabilizes`)
* **Observation 2.6's explicit bound is false for `n = 2` (degenerate); the proof has a wrong estimate.** The
  claim "for any `α > 0`, probability `≥ ½ n^{-3α}` to require `≥ α n ln n` convergence time" fails for `n = 2`:
  `Silent-n-state-SSR` with two agents is correctly ranked after the first interaction from every configuration,
  under every schedule, so its convergence time is at most `1/2 < 2 ln 2`. In the proof,
  `(1 − 3/n²)^{α n² ln n} ≥ ½ e^{−3α ln n}` is false for large `α` (e.g. `n = 10`, `α = 7`), and
  `1/C(n,2) < 3/n²` needs `n ≥ 4`. For `n = 3` the claim also fails for large `α` (e.g. `α = 10`; checked
  numerically, not in Lean). The claim holds for `n ≥ 4` with the exact success probability
  `2/(n(n−1))`, and the `Ω(n)` expected-time statement is fine. (`obs26_n2_counterexample`; the deterministic core
  and the geometric tail are `obs26_null_of_ne`, `obs26_two_leaders`, `obs26_stay_prob`)
* **Under-specified pseudocode of Protocols 2–4.** The field list of Protocol 3 omits `resetcount = 0`;
  `Propagate-Reset(a, b)` is written for a Resetting `a` but called also when only `b` is Resetting; the `leader`
  bit of agents brought into `Resetting` is not set (the text says `L`); "just became 0" and line 10's
  `b.role ≠ Resetting` (for `i = b`) are ambiguous. We fixed one reading (`differencies.md`, item 21); the
  off-by-one does not depend on it, and the model checker finds the fixed protocol correct under the alternative
  reading of line 10 too.
* **Typos.** Proof of Lemma 2.2: `∑_{j=1}^{n−1} m_j = n` (should start at `j = 0`) and `S_k − S_{k−r+1}` (should be
  `S_{k−r−1}`, `S_{−1} = 0`). Proof of Theorem 2.4: the slow initial configuration is "`m_1(C_0) = 2`" but should be
  `m_0(C_0) = 2`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Population protocols on the complete graph with labelled agents (`A → Q`, `|A| = n`), ordered pairs of distinct
  agents. Randomized transitions `S × S → Dist(S × S)` are modelled by their support (`NProtocol`); deterministic
  CSLib protocols (`Cslib.PopulationProtocol.Protocol`) embed into this.
* Self-stabilization "with probability 1" (uniformly random scheduler) is formalized as: from every configuration a
  stably correct configuration is reachable. `RandomScheduler.lean` proves that this is equivalent to the paper's
  notion: for any Markov kernel whose positive entries are exactly the protocol's steps (e.g. the uniform
  scheduler, `uniformKernel`), it implies absorption with probability 1, and unreachability implies probability 0.
* Lower bounds (Theorem 2.1) assume only this reachability property (the weakest, "positive probability"
  reading) and allow randomized transitions and arbitrary sets of leader states.
* For `Silent-n-state-SSR` we additionally prove deterministic statements for arbitrary schedulers (at most
  `n(n−1)` non-null interactions in every execution) and weakly fair schedulers (CSLib `Execution.WeaklyFair`).
* `Optimal-Silent-SSR`: explicit state type (roles with their fields) and the interaction as the composition of the
  pseudocode blocks, with a flag selecting the printed (`<`) or the fixed (`≤`) recruitment guard. Its Lean
  transition function agrees with the Python model checker `tools/oss.py` on all state pairs (checked for
  `n = 3`). Its state type has unbounded `ℕ` fields, so the probability-1 bridge applies to the finite set of
  valid states; it is not instantiated for this protocol in Lean.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (SSLE needs `≥ n` states) [Cai–Izumi–Wada] | `NProtocol.card_le_card_states` | `LowerBound.lean` |
| Theorem 2.1 (strong nonuniformity: no protocol works for two sizes) | `NProtocol.not_solvesSSLE_two_sizes` | `LowerBound.lean` |
| Lemma 2.2 (barrier rank exists) | `SilentSSR.exists_barrier` | `SilentSSR.lean` |
| Lemma 2.3 (barrier is preserved) | `SilentSSR.IsBarrier.step` | `SilentSSR.lean` |
| Theorem 2.4 (correctness: SSR, SSLE) | `SilentSSR.solvesSSR`, `SilentSSR.solvesSSLE` | `SilentSSR.lean` |
| Theorem 2.4, deterministic strengthening | `SilentSSR.card_changes_le`, `SilentSSR.weaklyFair_eventually_ranked` | `SilentSSR.lean` |
| "with probability 1" ⇔ reachability | `NProtocol.tendsto_not_stablyCorrect`, `prob_stablyCorrect_eq_zero`, `uniform_tendsto` | `RandomScheduler.lean` |
| Observation 2.5 | `Obs25.obs25_solvesSSLE`, `obs25_silent`, `obs25_not_solvesSSR` | `Observations.lean` |
| Observation 2.6 (core, geometric tail) | `obs26_null_of_ne`, `obs26_two_leaders`, `NProtocol.obs26_stay_prob` | `Observations.lean`, `Obs26Prob.lean` |
| Observation 2.6 fails for `n = 2` | `obs26_n2_counterexample` | `Observations.lean` |
| Protocol 3 as printed never ranks | `OptimalSilent.asWritten_never_ranked`, `asWritten_not_selfStabilizes` | `OptimalSilent.lean` |
| Ranked configurations are silent | `OptimalSilent.Ranked.reachable` | `OptimalSilent.lean` |
| Theorem 4.3 (correctness, fixed guard; `Rmax, Dmax ≥ 2`) | `OptimalSilent.fixed_reachable_ranked`, `fixed_selfStabilizes`, `valid_step` | `OptimalSilentCorrect.lean` |

**Not formalized.** All time and probability bounds (Theorem 2.4's `Θ(n²)`, Lemmas 2.7–2.11, 3.2–3.3, Theorem 3.4,
Corollary 3.5, Lemmas 4.1–4.2, the `O(n)` time and state count of Theorem 4.3, Corollary 4.4), Section 5
(`Sublinear-Time-SSR`, exponential states, Theorem 5.7) and the derandomization of Section 6.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Silent-n-state-SSR` and the protocol of Observation 2.5 satisfy the SSLE/SSR hypotheses of the
lower bounds (`solvesSSLE`, `obs25_solvesSSLE`). Built on CSLib's `Cslib.Computability.Distributed.PopulationProtocols`
and `Cslib.Probability.Markov.Absorption`, and on the shared library: the support model `NProtocol`
(`Cslib/Computability/Distributed/PopulationProtocols/Nondet.lean`, with sub-population embedding `exists_reach_of_embedding`), the uniform
scheduler `uniformKernel` (`Cslib/Computability/Distributed/PopulationProtocols/RandomScheduler.lean`), `StablyCorrect`/`SelfStabilizes`
(`StablyIn`/`SelfStabilizes` of `Cslib/Computability/Distributed/SelfStabilization/TransitionSystem.lean`) and the reachability/probability-1 bridge
(`Cslib/Computability/Distributed/SelfStabilization/Markov.lean`). CSLib candidates (marked in the code): the pair/triple run-lifting lemmas of
`OptimalSilentCorrect.lean`.
