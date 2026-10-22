# Towards Efficient Verification of Population Protocols — PODC 2017

Michael Blondin, Javier Esparza, Stefan Jaax, Philipp J. Meyer. *Towards Efficient Verification of
Population Protocols.* PODC 2017. DOI [10.1145/3087801.3087816](https://doi.org/10.1145/3087801.3087816).
Formalized version: arXiv [1703.04367](https://arxiv.org/abs/1703.04367) v3 (full version with appendix);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The soundness of the new class is proved: WS³ ⊆ WS² ⊆ WS
(Propositions 19 and 20, StrongConsensus ⇒ Consensus via traps and siphons), and so are Lemmas 21 and 22.
The threshold protocol `P_thr` is in WS³ (Propositions 17 and 18), so it computes `∑ aᵢxᵢ < c`.
All statements hold, but the proof of Proposition 18 relies on a false intermediate claim and misses
cases; we repaired it with a lexicographic ranking function. `P_thr` is also slightly under-specified
(only the leaders' transitions are given; we complete it with silent transitions).

## Mistakes in the paper

* **Proof of Proposition 18 (`P_thr[T₁]` is silent): a false monotonicity claim.** The proof says
  that, "as observed in [1]", `aᵢ` (the total absolute value of the non-leaders) never increases:
  `a₀ ≥ a₁ ≥ ⋯`. This is false. When two leaders meet, the responder becomes a non-leader and keeps
  the overflow `g(n, n')`. For example, with `c = 1` and `v = vmax = 2` (the case `c > 0` treated in the
  appendix), the `T₁`-step `(1,2,0),(1,2,0) ↦ (1,2,0),(0,2,0)` raises `a` from 0 to 2
  (`nonleaderAbs_not_antitone`). This is a proof gap; the statement is true. Leader–leader steps lower
  the number of leaders, which the proof also uses, so the repair is to order the measures
  lexicographically, with the number of leaders first.
* **Proof of Proposition 18: missing cases.** The proof then says that, once leaders, `a` and the
  inconsistent leaders are stable, every non-silent `T₁`-transition is `(1,x,1),(0,0,0) ↦ (1,x,1),(0,0,1)`.
  This misses the *saturated* interactions: `(1,v,0),(0,n,1) ↦ (1,v,0),(0,n,0)` for `n > 0`, and the
  mirror case `(1,−v,1),(0,n,0) ↦ (1,−v,1),(0,n,1)` for `n < 0` (`saturated_flip`). These flip opinions in one direction only,
  so the conclusion survives once a fourth potential is added. Our proof uses the lexicographic ranking
  (leaders, `a`, inconsistent leaders, flippable non-leaders) and checks that it strictly decreases on every
  non-silent `T₁`-transition (`t1_silent`). The paper's case split on the sign of `c` is unnecessary:
  the partition `T₁ = {t : pre(t) ∉ L₀ × N₁}`, `T₂ = T \ T₁` works for every `c` (`proposition_18_with`).
* **`P_thr` is under-specified.** The definition says that `T` *contains* the transitions of pairs whose
  first state is a leader, and is silent about the other pairs, while the model requires a transition for
  every pair of states. We add identity transitions for the remaining pairs, as in Example 1 for the
  majority protocol. Silent transitions only add self-loops, so this changes neither reachability,
  potential reachability, terminal configurations, nor (up to stuttering) the fair executions.
* **Proof of Proposition 17: trap argument incomplete in a trivial case.** "The set of leaders forms a
  U-trap … which implies that `C'` contains a leader" only follows when some transition in `U = ⟦x⟧` moves
  an agent *into* the leaders. Every listed transition of `P_thr` does, so in the paper's protocol the only
  missing case is `x = 0` (then `C' = C`); with the added silent non-leader transitions, `U` may consist of
  these only, and the flow equations show that the number of leaders is unchanged
  (`exists_leader_of_potReachVia`). A minor gap.
* **Proposition 19(a), "⇒ follows immediately from the definitions".** This direction needs fair
  executions to exist. With the paper's edge-based fairness, that takes a construction (a globally fair run of the "edge
  system"; `exists_edgeFair`). An omitted routine step.
* **Typos.** Lemma 21 writes "`x(q) ≥ 0` for every `q ∈ Q`, and `x(q) > 0` for some `q ∈ Q`" where `x`
  is indexed by transitions (`x(t)`, `t ∈ U`). In the proof of Proposition 18, "every execution of `P_thr[T₁]`
  is fair" should read "silent", and "set the opinion of non leaders to 0" should read "to 1".
  Observation 11 writes `C(S) = 0` for `C(P) = 0`. Lemma 22 is stated for `S = T \ U` inside one
  protocol but used (Prop. 7) for `P[Tᵢ]` with `U = T₁ ∪ ⋯ ∪ Tᵢ₋₁`; we state it for arbitrary `S`, `U`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* The paper's model. Configurations are multisets of states (`Multiset Q`, finite `Q`). Transitions
  are a relation `T ⊆ Q² × Q²`, with `pre(t) = ⦃p, q⦄` and `post(t) = ⦃p', q'⦄`, total on pairs of states.
  A step fires one enabled transition. Executions are infinite runs. There is no randomness: the
  scheduler is adversarial, subject to fairness.
* Fairness is the paper's: if `C` occurs infinitely often and `C → C'`, then the consecutive pair `C C'` occurs
  infinitely often (`Run.EdgeFair`; stronger than CSLib's state-based global fairness, which it implies).
* Inputs are populations `X` with `|X| ≥ 2`. Silence, Termination, Consensus, well-specification,
  `P[S]` (with all identity transitions added), LayeredTermination (Def. 4, with an explicit list as the
  ordered partition), flow equations, `U`-traps and `U`-siphons, potential reachability (Def. 12) and
  StrongConsensus (Def. 14) are transcribed literally.
* "For every configuration" ranges over all multisets, including those with fewer than 2 agents.
  These are terminal and have no executions, so nothing changes.
* `P_thr` is formalized for any value bound `v ≥ |c| + 1` with `|aᵢ| ≤ v` (`Threshold.protocol`). The paper's
  `vmax = max(|aᵢ|, |c| + 1)` is the instance `Threshold.Pthr`.

**Main results in Lean.** (namespace `Podc.PPVerification`)

| Paper | Lean | File |
|---|---|---|
| Prop. 19 (WS² ⇔ Termination ∧ Consensus) | `proposition_19` (from `MProtocol.silent_iff_termination`, `MProtocol.wellSpecified_iff_consensus`) | `Soundness.lean` |
| Prop. 20 (LayeredTermination ⇒ Termination) | `proposition_20` | `Soundness.lean` |
| Observation 11, `C →* C'` ⇒ `C ⇢ C'` | `FiresSeq.trap`, `FiresSeq.siphon`, `MReach.potReach` | `Podc/.../Multiset/PotentialReach.lean` |
| StrongConsensus ⇒ Consensus; WS³ ⊆ WS² ⊆ WS (§4.3) | `consensus_of_strongConsensus`, `ws3_subset_ws2`, `ws3_wellSpecified` | `Soundness.lean` |
| Lemma 21 | `lemma_21` (any transition set: `lemma_21_set`) | `Lemma21.lean` |
| Lemma 22 (characterization behind Prop. 7) | `lemma_22` | `Lemma22.lean` |
| Prop. 23 (flow equations preserve `val`) | `Threshold.flowEq_val` | `Prop17.lean` |
| Prop. 24 | `Threshold.consensus_of_terminal` (output is `val(C) < c`) | `Prop17.lean` |
| Prop. 17 (`P_thr` StrongConsensus) | `Threshold.proposition_17`, `Threshold.proposition_17_Pthr` | `Prop17.lean` |
| Prop. 18 (`P_thr` LayeredTermination) | `Threshold.proposition_18` (`_with`: any `c`, partition `[T₁, T₂]`; layers `t1_silent`, `t2_silent`, `t2_dead`) | `Prop18.lean`, `Prop18T1.lean` |
| `P_thr ∈ WS³`; `P_thr` computes `∑ aᵢxᵢ < c` | `Threshold.pthr_ws3`, `Threshold.pthr_computes` | `Main.lean` |
| Proof-gap witnesses for Prop. 18 | `Threshold.nonleaderAbs_not_antitone`, `Threshold.saturated_flip` | `Remarks.lean` |

**Not formalized.** The complexity results (Prop. 3, Props. 6, 7, 15, Cor. 8, Thm. 16) and Section 5's
remainder protocol and closure under negation and conjunction (Props. 25–29). The experiments (§6) are
also out of scope.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
`P_thr` (for every `a`, `c`) is a non-vacuous instance of WS³. Before the proofs we model-checked Prop. 18
for `v ≤ 3`, all `c`, and populations of up to 3 agents: both of the paper's partitions satisfy (a) and (b) for every `c`.
Shared model (staged for CSLib): `Podc/Computability/Distributed/PopulationProtocols/Multiset/{Basic,PotentialReach}.lean`
and `Podc/Computability/Distributed/SelfStabilization/EdgeFair.lean` (on top of CSLib's
`Cslib.TransitionSystem.Run`; the anonymous multiset model is parallel to CSLib's labelled `NProtocol`, and a
bridge between the two is not yet formalized).
