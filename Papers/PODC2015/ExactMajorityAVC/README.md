# Fast and Exact Majority (AVC) — PODC 2015

Dan Alistarh, Rati Gelashvili, Milan Vojnović. *Fast and Exact Majority in Population Protocols.*
PODC 2015. DOI [10.1145/2767386.2767429](https://doi.org/10.1145/2767386.2767429). Formalized version:
the full version, Microsoft Research technical report MSR-TR-2015-13 (February 2015, with appendices).
Numbering follows it.

**Verdict: ⚠️ Weakened.** With a one-symbol typo in Figure 1 fixed, AVC solves exact majority with probability 1 from
every configuration with non-zero sum (Lemma A.1, Theorem 4.1 first part), for all `n`, `m`, `d`. The four-state lower
bound announced in the abstract (Theorem B.1) is proved only for unordered interactions, the convention of the paper's
proof, while the paper states it for all protocols in its ordered model. The convergence-time bounds, the paper's main
claim, and the `Ω(log n)` lower bound were not checked.

## Mistakes in the paper

### ⚠️ Theorem B.1 for ordered interactions (unestablished)
Theorem B.1 is stated for "any majority algorithm using four states" with ordered
(initiator, responder) interactions, but its proof treats `[S0, X]` and `[X, S0]` as one interaction
with a single outcome, so it does not cover protocols whose two orientations differ.

**Impact.** Not refuted, and very likely true: we prove Theorem B.1 for unordered interactions, the
convention of the paper's proof (`theorem_B_1`, hypothesis `Symmetric P`); for ordered protocols the
gap is closed only by a script, not in Lean. For unordered interactions, every correct four-state
protocol preserves `#S0 − #S1`, so the probability of converging within `t` steps is at most
`2t(ϵn+1)/(n(n−1))`.

**Details.** Section 2 defines `δ : Q × Q → Q × Q` with ordered (initiator, responder) pairs, and
AVC itself assigns different states to initiator and responder. Claims B.2–B.5 do not need symmetry
(we prove them for both orientations), and an exhaustive search over ordered protocols with
populations of at most 5 agents refutes every protocol that does not preserve `#S0 − #S1`. Since
refuting certificates on small populations are valid for every `n`, this search would close the
gap, but it is a script, not Lean. `Symmetric P` means that both orientations of a pair give the
same multiset of states, though possibly to different agents. See [differencies.md](differencies.md)
(item 7).

### ✏️ Slips
- **Figure 1, line 12 (`value` for `weight`).** Line 12 reads "`weight(x)·weight(y) = 0` and
  `value(x) + value(y) > 0`", so a weak node meeting a node of *negative* value skips lines 12–14 and falls through to
  line 19, which changes nothing: `+0` never becomes `−0`, and AVC can fail when `B` is the majority (`literal_fails`,
  `not_tendsto_literal`).
  - Counterexample with `m = d = 1`, the four-state protocol, and inputs `A, B, B` (states `1₁, −1₁, −1₁`). The first
    two agents interact by line 17 into `−0, +0`. The configuration `−0, +0, −1₁` is silent, and agent 2 outputs `A`
    forever. This happens after one step with positive probability, so the probability of converging to `B` does not
    tend to 1.
  - A model checker finds the same failure for `m = 3` (inputs `A, B, B` give `+3, −3, −3`) and every other small
    parameter set we tried, from many initial configurations.
  - The prose under Figure 1 describes the intended condition `weight(x) + weight(y) > 0` ("zero meets non-zero"). With
    it, the protocol is sign-symmetric (`update_neg`) and solves exact majority with probability 1 (`lemma_A_1`,
    `theorem_4_1_correct`).
  - The proof of Lemma A.1 assumes "without loss of generality `S > 0`", and for `S > 0` the literal rule happens to
    work; it is the sign symmetry behind this WLOG that the typo destroys.

### Typos
Small typos in the case analysis of Appendix B (we checked the stated interaction sequences by script):
- "two nodes in S9" (Case 1) should be `S0`.
- "three nodes starting in C0" (Case 2.3) should be `S0`.
- In Case 2.4.1 the configuration "two `X`, three `S1`" needs two applications of `[X, Y] → [S1, X]`, not one.
- At the end of Case 2.4.1 ("`[X, Y]` into `[S0, Y]`") the contradiction is with the second property, not the third.

## Proof gaps (statements true)

### 🔧 Claim B.8 (inside the proof of Theorem B.1: meeting probability)
The unique minority agent meets one of the `ϵn + 1` majority agents with probability
`2(ϵn+1)/(n(n−1))`, not `(ϵn+1)/n²`.

**Impact.** The paper's value is too small, the wrong direction for a lower bound, but only by a
factor of about 2, so `Ω(1/ϵ)` is unaffected (`hitProb_le`, `sum_tail_ge`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Population protocols on the complete graph, CSLib's model: `n` labelled agents, a deterministic
  transition function `δ` on ordered (initiator, responder) pairs, no failures. AVC is `avc d`;
  its states are `±0`, `±1_j` and strong values `v` (odd, `3 ≤ |v| ≤ m`). Figure 1 is transcribed
  line by line (`update`): `lit = true` is the printed version, `lit = false` the corrected one.
* Randomness: the uniformly random scheduler of Section 2, i.e. an ordered pair of distinct agents
  drawn uniformly at each step (CSLib's `uniformKernel`, a Markov kernel on the finite set of
  configurations over valid states). "With probability 1" means that the probability of not being
  converged after `t` steps tends to `0`; the converged set is proved closed.
* Theorem B.1: four states `S0, S1, X, Y`, a CSLib protocol `P : Protocol Q4` and an output map
  `γ`. The three correctness properties are stated for every population size on anonymous
  configurations (multisets of states, the Podc multiset model `MStep`/`MReach`). This is equivalent
  to labelled agents because protocols are anonymous. Interactions are unordered (`Symmetric P`:
  both orientations give the same multiset), as in Appendix B. The lower bound uses CSLib's labelled
  uniform scheduler.
* The probability of convergence within `t` steps is the first-step recursion `hitProb`. "Expected
  parallel time `Ω(1/ϵ)`" is formalized as a tail bound plus a lower bound on the partial sums
  `∑_{t<K} P(τ > t)`, whose full sum is `E[τ]`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Figure 1 (AVC), as printed / corrected | `avcLiteral`, `avc` (`update`) | `AVC.lean` |
| Invariant 4.3 (sum of values never changes) | `total_reachable` (`value_update`) | `AVCCorrect.lean` |
| Lemma A.1, reachability of `sgn S` for all agents (three phases) | `exists_reachable_converged` | `AVCCorrect.lean` |
| Lemma A.1, "no node can ever have a different sign" | `converged_closed`, `lemma_A_1_closed` | `AVCCorrect.lean`, `AVCProb.lean` |
| Lemma A.1, with probability 1 | `lemma_A_1` | `AVCProb.lean` |
| Theorem 4.1, first part (AVC solves majority w.p. 1) | `theorem_4_1_correct` | `AVCProb.lean` |
| Figure 1 as printed fails | `literal_fails`, `not_tendsto_literal` | `AVCLiteral.lean` |
| Claim B.2, Corollary B.3 | `claim_B_2`, `corollary_B_3` | `FourClaims.lean` |
| `γ(S_i) = i`, `γ(X) ≠ γ(Y)` | `gamma_S`, `gamma_X_ne_gamma_Y` | `FourClaims.lean` |
| Claim B.4, Claim B.5 (both orientations) | `claim_B_4`, `claim_B_5` | `FourClaims.lean` |
| Claims B.6, B.7, Cases 1–3 (outcome: `#S0 − #S1` is invariant) | `theorem_B_1_invariant` | `FourMain.lean` |
| Claim B.8 | `hitProb_le`, `sum_tail_ge` | `FourLowerBound.lean` |
| Theorem B.1 (`Ω(1/ϵ)`, tail form) | `theorem_B_1` | `FourLowerBound.lean` |

The case analysis (Claims B.6, B.7, Cases 1–3, with Claim B.9) is replaced by two certified case
trees (`FourTreeA.lean`, `FourTreeB.lean`; 514 and 532 leaves, one tree per value of `γ(X)`). A
script generates them (`tools/gen2.py`, `tools/emit.py`), and the kernel checks them with `decide`
against the soundness theorem `checkTree_sound` (`FourChecker.lean`). Each leaf refutes a partial
transition table with a certificate on at most 7 agents: a common configuration reachable from two
initial configurations (Claim B.2), a closed set of wrong-output configurations (second property), or
a closed set without correct-output configurations (third property, which covers the potential
arguments of Claim B.9). The other leaves are complete tables preserving `#S0 − #S1`.

**Not formalized.** The convergence-time bounds of Theorem 4.1 and Corollary 4.2 (Claims A.2–A.4,
4.4, 4.5) and the `n³(m+d+1)` expected-time bound of Lemma A.1; Theorem C.1 (`Ω(log n)` for any
number of states); ordered (asymmetric) four-state protocols in Theorem B.1 (only model-checked).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`; the case trees and the counterexample are checked by `decide`. Non-vacuity: the
classical four-state protocol satisfies the three properties of Theorem B.1 for every population
size (`std_correct`, `FourExample.lean`). The model checkers are in [`tools/`](tools/) and are not
part of the Lean development: `avc.py` (AVC, literal and corrected), `b1.py` (symmetric four-state
protocols), `genasym.py` (ordered ones). Models come from CSLib
(`Cslib.Computability.Distributed.PopulationProtocols.{Basic,RandomScheduler}`,
`Cslib.Computability.Distributed.SelfStabilization.Markov`) and Podc
(`Podc/Computability/Distributed/PopulationProtocols/Multiset/Basic.lean`).

CSLib candidates (marked `-- CSLib candidate`): `sum_interact`, `reach_of_measure`
(`AVCCorrect.lean`), `hitProb` with `hitProb_mono` and `hitProb_nonneg_le_one`
(`FourLowerBound.lean`), the `ms_eq` tactic and `Reach.add_right` (`FourModel.lean`).
