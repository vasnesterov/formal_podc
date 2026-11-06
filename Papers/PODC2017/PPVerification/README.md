# Towards Efficient Verification of Population Protocols — PODC 2017

Michael Blondin, Javier Esparza, Stefan Jaax, Philipp J. Meyer. *Towards Efficient Verification of
Population Protocols.* PODC 2017. DOI [10.1145/3087801.3087816](https://doi.org/10.1145/3087801.3087816).
Formalized version: arXiv [1703.04367](https://arxiv.org/abs/1703.04367) v3 (full version with appendix);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The soundness of the new class (WS³ ⊆ WS² ⊆ WS, Propositions 19 and 20, StrongConsensus ⇒
Consensus via traps and siphons), Lemmas 21 and 22, and the membership of `P_thr` in WS³ (Propositions 17 and 18, so
it computes `∑ aᵢxᵢ < c`) all hold. The only real defects are in the proof of Proposition 18, and they are repaired
by ordering the paper's potentials lexicographically and adding one more. The DP complexity results and the closure
properties that give WS³ its full expressive power were not checked, so this label covers soundness and the threshold
protocol only.

## Mistakes in the paper

### ✏️ Slips
- **Lemma 21 (indexing of `x`).** It writes "`x(q) ≥ 0` for every `q ∈ Q`, and `x(q) > 0` for some `q ∈ Q`", but `x`
  is indexed by transitions (`x(t)`, `t ∈ U`). With that indexing the lemma holds (`lemma_21`, `lemma_21_set`).
- **Definition of `P_thr` (transitions not total).** It says that `T` *contains* the transitions of pairs whose first
  state is a leader and is silent about the other pairs, while the model requires a transition for every pair of
  states. We add identity transitions for the remaining pairs, as in Example 1 for the majority protocol. Silent
  transitions only add self-loops, so this changes neither reachability, potential reachability, terminal
  configurations, nor (up to stuttering) the fair executions.
- **Proposition 17 (trap argument).** "The set of leaders forms a U-trap … which implies that `C'` contains a leader"
  only follows when some transition in `U = ⟦x⟧` moves an agent *into* the leaders. Every listed transition of
  `P_thr` does, so in the paper's protocol the only missing case is `x = 0` (then `C' = C`). With the added silent
  non-leader transitions, `U` may consist of these only, and the flow equations show that the number of leaders is
  unchanged (`exists_leader_of_potReachVia`).
- **Proof of Proposition 18.** "Every execution of `P_thr[T₁]` is fair" should read "silent", and "set the opinion of
  non leaders to 0" should read "to 1".
- **Observation 11** writes `C(S) = 0` for `C(P) = 0`.
- **Lemma 22** is stated for `S = T \ U` inside one protocol but used (Prop. 7) for `P[Tᵢ]` with
  `U = T₁ ∪ ⋯ ∪ Tᵢ₋₁`; we state it for arbitrary `S`, `U`.

## Proof gaps (statements true)

### 🔧 Proposition 18 (`P_thr[T₁]` is silent: false monotonicity claim)
The proof says that, "as observed in [1]", `aᵢ` (the total absolute value of the non-leaders) never increases, but a
leader–leader step can raise it from 0 to 2 (`nonleaderAbs_not_antitone`).

**Impact.** Statement true; repaired by ordering the measures lexicographically, with the number of leaders first
(`t1_silent`).

**Details.** The claim is `a₀ ≥ a₁ ≥ ⋯`. When two leaders meet, the responder becomes a non-leader and keeps the
overflow `g(n, n')`. For example, with `c = 1` and `v = vmax = 2` (the case `c > 0` treated in the appendix), the
`T₁`-step `(1,2,0),(1,2,0) ↦ (1,2,0),(0,2,0)` raises `a` from 0 to 2 (`nonleaderAbs_not_antitone`). Leader–leader
steps lower the number of leaders, which the proof also uses.

### 🔧 Proposition 18 (missing saturated cases)
The proof claims that, once leaders, `a` and the inconsistent leaders are stable, every non-silent `T₁`-transition
is `(1,x,1),(0,0,0) ↦ (1,x,1),(0,0,1)`, which misses the *saturated* interactions (`saturated_flip`).

**Impact.** Statement true; the conclusion survives once a fourth potential is added (`t1_silent`,
`proposition_18_with`).

**Details.** The missed transitions are `(1,v,0),(0,n,1) ↦ (1,v,0),(0,n,0)` for `n > 0`, and the mirror case
`(1,−v,1),(0,n,0) ↦ (1,−v,1),(0,n,1)` for `n < 0` (`saturated_flip`). These flip opinions in one direction only.

**Repair.** Our proof uses the lexicographic ranking (leaders, `a`, inconsistent leaders, flippable non-leaders) and
checks that it strictly decreases on every non-silent `T₁`-transition (`t1_silent`). The paper's case split on the
sign of `c` is unnecessary: the partition `T₁ = {t : pre(t) ∉ L₀ × N₁}`, `T₂ = T \ T₁` works for every `c`
(`proposition_18_with`).

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

**Proof remarks.** Proposition 19(a), "⇒ follows immediately from the definitions", needs fair executions to exist.
With the paper's edge-based fairness, that takes a construction (a globally fair run of the "edge system";
`exists_edgeFair`). An omitted routine step.

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

**Not formalized.** The complexity results (Prop. 3, Props. 6, 7, 15, Cor. 8, Thm. 16), including the polynomial-time
claims of Lemma 22 and of the maximal trap/siphon remark, and Section 5's remainder protocol and closure under negation
and conjunction (Props. 25–29), hence the claim that WS³ is as expressive as WS. The experiments (§6) are also out of
scope.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
`P_thr` (for every `a`, `c`) is a non-vacuous instance of WS³. Before the proofs we model-checked Prop. 18
for `v ≤ 3`, all `c`, and populations of up to 3 agents: both of the paper's partitions satisfy (a) and (b) for every `c`.
Shared model (staged for CSLib): `Podc/Computability/Distributed/PopulationProtocols/Multiset/{Basic,PotentialReach}.lean`
and `Podc/Computability/Distributed/SelfStabilization/EdgeFair.lean` (on top of CSLib's
`Cslib.TransitionSystem.Run`; the anonymous multiset model is parallel to CSLib's labelled `NProtocol`, and a
bridge between the two is not yet formalized).
