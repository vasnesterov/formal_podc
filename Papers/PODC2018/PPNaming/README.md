# Space-Optimal Naming in Population Protocols — PODC 2018

Janna Burman, Joffroy Beauquier, Devan Sohier. *Brief Announcement: Space-Optimal Naming in Population
Protocols.* PODC 2018. DOI [10.1145/3212734.3212791](https://doi.org/10.1145/3212734.3212791). Formalized version:
the full version, LRI research report HAL [hal-01790517v3](https://inria.hal.science/hal-01790517v3)
("Space-Optimal Naming in Population Protocols", 21 pp., also DISC 2019); the 2-page brief announcement has no
proofs. Numbering follows the full version.

**Verdict: 🛠️ Hard fix.** All formalized propositions hold, for `P ≥ 2`: the impossibilities (Propositions 1, 3, 4,
Theorem 11), the sink property (Proposition 6), Lemma 2 and the protocols of Propositions 12, 13 and 14. The proof
of Theorem 11, the subtlest result, has a real gap, and we replace it with a different adversary argument; the
summary in Table 1 and the introduction leaves out that without a leader, symmetric naming is impossible for `n = 2`
agents whatever the number of states. Propositions 16 and 17 and the with-leader cells of Proposition 12 were not
checked, so the classification is checked only in part.

## Mistakes in the paper

### ✏️ Slips
- Table 1 and §1 (no leader, global fairness, symmetric rules: "P + 1 states"). The summary says naming without
  leader under global fairness is possible with `P + 1` states, but with `n = 2` agents no symmetric leaderless
  protocol, with any number of states, names them (`not_solvesGlobal_of_card_two`, `not_solvesWeak_of_card_two`).
  From a uniform configuration of two agents, both orientations of the only pair apply `(s, s) → (s', s')`, so every
  reachable configuration is uniform. This holds under any fairness. Only the summary is affected: Proposition 13
  itself states the restriction `n > 2` and is correct (`prop13_solvesGlobal`). Since the model asks for one protocol
  that works for all `n ≤ P`, this table cell (and "the norm is `P + 1` states" in §1) holds only for populations of
  at least 3 agents.
- Propositions 3, 4 and Theorem 11 are false for `P = 1` (one state, at most one mobile agent: naming is
  trivial). All our statements assume `P ≥ 2`.

## Proof gaps (statements true)

### 🛠️ Theorem 11 (no `P`-state symmetric naming of non-initialized agents under weak fairness)
The proof builds the execution `e` by alternating segments from the two indistinguishable worlds `C⁻ˢ`/`C`
(Lemmas 8–10) but never shows that `e` is weakly fair, and then lets `e` end in a stable `C*` through a segment
with an idle `s`-agent that the construction does not provide.

**Impact.** The theorem holds, but the paper's construction cannot be patched locally: it takes a different
adversary argument (`thm11`, `thm11_paper`).

**Details.** Lemmas 9/10 transfer segments in which the plus world's `s`-agent stays idle. Every segment the
construction produces ends with that agent being reduced. A final segment reaching a named `C*` (which contains
`s`) can be transferred only if the `s`-agent was idle there, and nothing ensures this. For Protocol 1 under global
fairness the leader must meet the `s`-agent before it can finish. Also, with arbitrarily initialized mobile agents
the "hidden agent" construction of `C₁` and `C₁⁻ˢ` is not needed: both are initial configurations.

**Repair.** Let `m` be the sink and `s ≠ m`. Two reduced configurations with the same leader state are related
(`Rel`) if, as multisets, plus `+ {m}` = minus `+ {s}` and minus has no `s`. A reduced step of the *minus* world
can always be mirrored in the plus world; the roles swap exactly when the minus world creates `s` (`mirror`).
By weak-fairness correctness, every reachable reduced configuration reaches a named one by reduced steps
(`exists_rreach_injective`), so a driving minus world eventually creates `s` (`drive`). The adversary always lets
the minus world drive. When the actual execution is the minus world, it first performs the pair that weak fairness
requires next; otherwise it follows the other world until the roles swap again. This execution is weakly fair and
has two `m`-agents infinitely often, so it never names the agents (`thm11_core`, built with
`exists_weaklyFair_of_phases`).

### 🔧 Proposition 4 and Lemma 2 (stabilized configurations taken as terminal)
Lemma 2 and Proposition 4 take for granted that a stabilized configuration is terminal, i.e. that no continuation
can change a name, and under weak fairness stabilization of one execution does not give this.

**Impact.** One added fact lets the paper's mirroring go through: correctness implies that a *closed* named
configuration is reachable from every reachable configuration (`exists_stablyGood_of_weaklyFair`).

**Repair.** Our proof of Proposition 4 mirrors the leader's interactions in a closed named configuration
(`prop4_core`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Deterministic population protocols on the complete interaction graph, CSLib's
  `Cslib.PopulationProtocol.Protocol` with labelled configurations. Asynchronous, no failures, adversarial
  scheduler. *Weak fairness*: every unordered pair of agents interacts infinitely often (CSLib's
  `WeaklyFair`). *Global fairness*: CSLib's `GloballyFair` on labelled configurations. No randomness.
- *Symmetric* protocol: `δ q p = (δ p q).swap` (`IsSymmetric`). Leader protocols (`LeaderProtocol L Q`) have
  separate rules for mobile–mobile, leader–mobile and mobile–leader interactions and are encoded as a CSLib
  protocol on `L ⊕ Q` with agents `Option A` (`none` is the leader). The leader's state set `L` is arbitrary,
  even infinite; it must be finite only for global fairness.
- *Naming*: the names `name (state)` of the mobile agents are eventually constant and pairwise distinct
  (`SolvesWeak` / `SolvesGlobal`, for every fair execution from the allowed initial configurations). The name
  is an arbitrary function of the state; for `P`-state protocols it is shown to be injective (Lemma 2).
- Initializations: arbitrary (`Set.univ`, `initArb`), uniform (`{fun _ => q₀}`, `initUniform`), initialized
  leader with arbitrary mobile agents (`initLeader`), arbitrary leader with uniform mobile agents.
- "For every population size `n ≤ P`" is quantified over finite agent types. The impossibilities use only
  the sizes actually needed (`P`, or `P - 1` and `P`), which makes them stronger.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Correctness ⇒ a terminal named configuration is reachable (used implicitly) | `exists_stablyGood_of_weaklyFair`, `exists_stablyGood_of_globallyFair` | `Podc/…/PopulationProtocols/Phases.lean` |
| Prop. 1 (no leader, weak fairness, symmetric: impossible; even `n`) | `prop1` | `Prop1.lean` |
| Lemma 2 | `lemma2`, `lemma2_leader` | `Basic.lean` |
| Prop. 3 (no leader, `P` states: impossible, weak/global) | `prop3_weak`, `prop3_global`, `prop3_weak_arb` | `Basic.lean` |
| Prop. 4 (arbitrary leader, `P` states: impossible, weak/global, arbitrary or uniform mobiles) | `prop4_weak`, `prop4_weak_uniform`, `prop4_global`, `prop4_global_uniform` | `Basic.lean` |
| Lemma 5 (form used for Prop. 6) | `lemma5` | `Sink.lean` |
| Prop. 6 (sink) | `prop6` | `Sink.lean` |
| Theorem 11 | `thm11`, `thm11_paper` | `Thm11.lean` |
| Prop. 12 (asymmetric, `P` states, weak and global) | `prop12_solvesWeak`, `prop12_solvesGlobal` | `Prop12.lean` |
| Prop. 13 (symmetric, no leader, `P + 1` states, global, `3 ≤ n ≤ P`) | `prop13_solvesGlobal`, `prop13_isSymmetric` | `Prop13.lean` |
| `n > 2` is needed in Prop. 13 | `not_solvesGlobal_of_card_two`, `not_solvesWeak_of_card_two` | `Prop13.lean` |
| Prop. 14 (initialized leader and mobiles, `P` states, weak and global) | `prop14_solvesWeak`, `prop14_solvesGlobal` | `Prop14.lean` |

**Proof remarks.** Lemma 2 says "symmetric naming protocol", but symmetry is not needed (`lemma2_core`).

**Not formalized.** Corollary 7 and Lemmas 8–10 are bypassed by the repaired proof of Theorem 11. Lemma 5 is
proved only in the form that Proposition 6 uses (states of a stably named configuration of size `P - 1`).
Theorem 15 (cited from [6]) and Propositions 16 and 17, which build on the unpublished internals of that counting
protocol, are not formalized. The "with leader" cells of Proposition 12 are not formalized either.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Propositions 12–14 also show that the correctness notions are satisfiable. The model is CSLib's
`Computability/Distributed/PopulationProtocols` (Basic, Schedules); the phase lemma and the
stabilization/reachability bridges are staged in `Podc/Computability/Distributed/PopulationProtocols/Phases.lean`
(CSLib candidate).

**CSLib candidates** (marked `-- CSLib candidate`):
- `Podc/Computability/Distributed/PopulationProtocols/Phases.lean` (whole file): `runList`,
  `exists_execution_of_segments`, `exists_weaklyFair_of_phases`, `Execution.Stabilizes`, `StablyGood`,
  `exists_stablyGood_of_weaklyFair` / `_of_globallyFair`, `stabilizes_of_globallyFair`. Its
  `exists_run_prefix` duplicates `Podc.PPStateComplexity.Protocol.exists_run_prefix` and is really a
  `TransitionSystem.Run` lemma.
- `eventually_const_of_potential` (`Prop12.lean`): an execution whose steps are null or decrease a
  natural-number potential is eventually constant.
- `interact_eq_update` (`Prop13.lean`): `Protocol.interact` as two `Function.update`s, the unfolded form of
  CSLib's `Protocol.interact_eq_upd` (`Nondet.lean`).
