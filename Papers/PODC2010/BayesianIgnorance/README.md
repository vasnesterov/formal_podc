# Bayesian Ignorance — PODC 2010

Noga Alon, Yuval Emek, Michal Feldman, Moshe Tennenholtz. *Bayesian Ignorance.* PODC 2010. DOI
[10.1145/1835698.1835785](https://doi.org/10.1145/1835698.1835785). Formalized version: the full version of
May 9, 2010 (17 pp., with appendix; no arXiv version); numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** All numbered results we checked hold: Observations 2.1–2.2,
Lemmas 3.1, 3.2, 3.3 ("ignorance is bliss"), 3.6, 3.7, 3.8, Proposition 4.1 and Lemma 4.2, and the reduction
of Lemma 3.5. The one statement-level problem is the claim that Rosenthal's potential is a Bayesian
potential of Bayesian NCS games: with the paper's own `∞` costs it is not, and the proof of Lemma 3.8
built on it has to minimise the potential over feasible profiles only. The appendix proofs of Lemmas 3.6
and 3.7 are swapped, and several proofs contain small slips; all are repaired.

## Mistakes in the paper

### ⚠️ End of Section 2 (Rosenthal's potential for Bayesian NCS games)
The claim that `Q(s) = ∑_t p(t) ∑_e c(e) H(|{i : e ∈ s_i(t_i)}|)` is a Bayesian potential is false under
the paper's definitions, where actions are arbitrary edge sets and an agent whose set misses her path
pays `∞`.

**Impact.** Local: the identity holds between profiles in which every agent connects her terminals, which
is what the paper evidently means (in the NCS literature strategies are paths). Existence of
equilibria and Lemma 3.8 survive with that restriction (see the proof gap below).

**Details.** A deviation from a connecting edge set to a non-connecting one raises the agent's cost by
`∞` but changes `Q` by a finite amount, so `C_i(s) − C_i(s') = Q(s) − Q(s')` fails. The global minimiser
of this `Q` is the all-empty profile (`Q = 0`), in which every agent with a non-trivial type pays `∞`; it
is not an equilibrium. Lean counterexample on the one-agent, one-edge network `0 → 1`:
`RosenthalCounterexample.no_finite_bayesPotential` (no finite-valued function is a Bayesian potential)
and `RosenthalCounterexample.empty_minimises_not_isBayesEq`.

**Repair.** The per-state Rosenthal identity between two connecting profiles
(`payment_add_potential_update`) gives the potential identity between *feasible* profiles (every agent
connects whenever possible); a minimiser of `Q` over feasible profiles is a Bayesian equilibrium
(`isBayesEq_of_isMin`, `exists_isBayesEq`).

### Typos and slips
- Proof of Lemma 3.7: the unique Nash equilibrium when agent `k+1` stays at `u` has agents `1, …, k` buy
  the edge `(u, w)`, not `(u, v)`.
- Proof of Lemma 3.7: the cost of an agent under `s` is `1 + 2/k − 1/k²`, not `1 + 2/k − 2/k²`. The
  chosen range `2/k − 1/k² < ε` is exactly what the correct value needs.
- Proof of Lemma 3.2: "agent `i` buys the right edge with probability `1/m`" should be `1/(m+1)` (a point
  lies on `m+1` lines), and `K(s) = m(1 − 1/m)` forgets agent `k`'s edge and holds only as a lower bound;
  the correct bound is `opt^P ≥ 1 + m²/(m+1) ≥ k − 1`.

## Proof gaps (statements true)

### 🛠️ Lemmas 3.6 and 3.7 (appendix proofs swapped)
The appendix "proof of Lemma 3.6" shows `worst-eq^P/worst-eq^C = O(1/k)`, which is Lemma 3.7's claim,
and the "proof of Lemma 3.7" shows `Ω(k)`, which is Lemma 3.6's claim.

**Impact.** Both statements are true; each is proved by the other's construction (`lemma_3_6`,
`lemma_3_7`; the two constructions are `worstConstructionA` and `worstConstructionB`).

**Details.** In the "3.6" game every Bayesian equilibrium costs `3/2 + ε` while the underlying game with
agent `k+1` at `v` has a Nash equilibrium of cost `k+2`, so `worst-eq^P ≤ 3/2 + ε` and
`worst-eq^C ≥ (k+2)/2`. In the "3.7" game a Bayesian equilibrium costs `k + 2` while `worst-eq^C = O(1)`.
The uniqueness claim in the "3.6" proof is also only argued against the all-via-`v` profile; profiles
with some agents on each route have to be excluded too (they are, by a simple share comparison).

### 🛠️ Lemma 3.3 (the equilibrium analysis on Anshelevich's graph)
The proof never fixes `ε`, claims that `s` is the *unique* Bayesian equilibrium, and replaces the
argument by "by induction on `i`".

**Impact.** Statement true; repaired (`Lemma33.lemma_3_3`, `Lemma33.worstEqP_le`).

**Details.** Agent `i` joins `(x, z)` only if `ε < 1/(2i+1)`, so the claimed equilibrium needs
`ε < 1/(2k−1)`; for larger `ε` it is not an equilibrium. Agents may also add zero-cost edges `(z, y_j)`,
so the equilibrium is unique only up to such edges (its cost `1 + ε` is unique, which suffices). The
induction must also rule out agents buying other agents' direct edges.

**Repair.** For `ε(2k − 1) < 1` we show by strong induction on the agent index that every Bayesian
equilibrium has all agents on `(x, z)`, using that no agent buys a positive-cost edge she does not need
(`not_isBayesEq_of_removable`); hence `worst-eq^P ≤ 1 + ε`. Every Nash equilibrium of the state where
agent `k` stays at `x` costs `≥ H(k−1)` (`hnum_le_stateCost`).

### 🛠️ Lemma 3.8 (`best-eq^P ≤ H(k) · opt^P`)
The proof takes a global minimiser of the potential `Q`, which is the empty profile (see the ⚠️ item).

**Impact.** Statement true; repaired (`lemma_3_8`).

**Repair.** Minimise `Q` over feasible profiles; turn an optimal profile into a feasible one without
changing it on the support of the prior; the case of an unreachable destination of positive probability
(`opt^P = ∞`) is trivial.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A Bayesian game: finitely many agents, finite action and type spaces, a common prior `p` on type
  profiles, pure strategies `s_i : T_i → A_i`, ex-ante costs `C_i(s) = ∑_t p(t) C_{i,t}(s(t))`, pure Bayesian
  equilibria (no profitable unilateral deviation in ex-ante cost) and pure Nash equilibria of the underlying
  complete-information games. No randomness other than the prior; no dynamics.
* Costs are `ℝ≥0∞`-valued (the NCS cost is `∞` when an agent's edge set misses her path); expectations are
  finite sums with `0 · ∞ = 0`. `opt`, `best-eq`, `worst-eq` are `⨅`/`⨆` over `ℝ≥0∞` (an empty `best-eq` is
  `∞`, an empty `worst-eq` is `0`; Bayesian NCS games always have an equilibrium, `exists_isBayesEq`).
* NCS games on an abstract network (`step e u v`, non-negative edge costs) covering directed and undirected
  (multi)graphs; types `T_i = V × V`, actions `A_i = 2^E`, fair cost sharing, as in the paper.
* Ratios are stated multiplicatively (`worst-eq^P ≤ k · opt^C`), asymptotic claims with explicit constants
  and explicit vertex counts.
* Section 4 uses its own model with strictly positive real costs and distributions in `stdSimplex`, as in the
  paper.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Observation 2.1 | `Cslib.GameTheory.BayesianGame.observation_2_1` | `Podc/Foundations/GameTheory/BayesianGame.lean` |
| Observation 2.2 | `Cslib.GameTheory.BayesianGame.observation_2_2` | `Podc/Foundations/GameTheory/BayesianGame.lean` |
| Bayesian NCS games have pure equilibria (§2) | `exists_isBayesEq` | `UpperBounds.lean` |
| §2: Rosenthal's `Q` is a Bayesian potential — **false** with `∞` costs | `RosenthalCounterexample.no_finite_bayesPotential`, `RosenthalCounterexample.empty_minimises_not_isBayesEq` | `UpperBounds.lean` |
| Lemma 3.1 | `lemma_3_1` | `UpperBounds.lean` |
| Lemma 3.2 | `Lemma32.lemma_3_2`, `Lemma32.lemma_3_2_prime` | `Lemma32.lean` |
| Lemma 3.3 | `Lemma33.lemma_3_3` | `Lemma33.lean` |
| "Ignorance is bliss": `worst-eq^P = opt^C`, `best-eq^C = Ω(log k)` (§1, §3) | `Lemma33.ignorance_is_bliss` | `Lemma33.lean` |
| Lemma 3.5 (the reduction; online lower bound assumed) | `Lemma35.lemma_3_5` | `Lemma35.lean` |
| Lemma 3.6 (via the paper's "proof of 3.7") | `lemma_3_6`, `worstConstructionB` | `Lemma36.lean` |
| Lemma 3.7 (via the paper's "proof of 3.6") | `lemma_3_7`, `worstConstructionA` | `Lemma36.lean` |
| Lemma 3.8 | `lemma_3_8` | `UpperBounds.lean` |
| Table 1, universal bounds `O(k)`, `Ω(1/log k)`, `Ω(1/k)` | `table_upper_k`, `bestEqC_le_hnum_mul_bestEqP`, `worstEqC_le_card_mul_worstEqP` | `UpperBounds.lean` |
| Proposition 4.1 | `proposition_4_1`, `roeBound_iff_eorBound` | `Section4.lean` |
| `RoE(φ) = EoR(φ)` (§4) | `CostTuple.roe_eq_eor` | `Section4.lean` |
| Lemma 4.2 | `CostTuple.lemma_4_2` | `Section4.lean` |

Unqualified names are in the namespace `Podc.BayesianIgnorance`. Proposition 4.1 is proved in the stronger
form that the RoE and EoR bounds are equivalent for every `r` (a reparametrisation of the simplex), which
avoids the appendix's tacit assumption that `sup_p min_i` is attained. Lemma 4.2 uses Sion's minimax
theorem from Mathlib. Lemma 3.3's game also gives `worst-eq^P = opt^C = 1 + ε` for `k ≥ 3`, the paper's
"the worst Bayesian equilibrium achieves the expected cost of the globally optimal outcome". The price of
stability `H(k)` and the price of anarchy `k` of complete-information NCS games, which the paper cites, are
re-derived as the point-mass cases of Lemmas 3.8 and 3.1 (`bestNash_le_hnum_mul_opt`,
`worstNash_le_card_mul_opt`).

**Not formalized.** Lemma 3.4 (needs the FRT tree embedding); the online Steiner tree lower bound behind
Lemma 3.5 (Imase–Waxman with Yao's principle; it is the hypothesis `hLB`); the remarks after Lemma 3.5
(diamond graph best-eq bound, Euclidean plane) and after Lemma 4.2 (zero costs); the directed variants of
Lemmas 3.6–3.7.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The lower-bound constructions come with existence of equilibria (`exists_isBayesEq`), so the
`worst-eq`/`best-eq` bounds are not vacuous. The Bayesian-game and NCS-game layer is staged for CSLib in
`Podc/Foundations/GameTheory/{BayesianGame,NetworkCostSharing}.lean` (`-- CSLib candidate`); a few generic NCS share bounds in `Lemma36.lean` (`triPay_le_of_subset`, `triPay_ge_of_mem`, `triIsNashEq_of`, …) are also marked as CSLib candidates.
