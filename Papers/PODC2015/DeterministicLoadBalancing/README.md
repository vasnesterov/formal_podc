# Deterministic Load Balancing — PODC 2015

Petra Berenbrink, Ralf Klasing, Adrian Kosowski, Frederik Mallmann-Trenn, Przemysław Uznański.
*Improved Analysis of Deterministic Load-Balancing Schemes.* PODC 2015. DOI
[10.1145/2767386.2767413](https://doi.org/10.1145/2767386.2767413). Formalized version: arXiv
[1404.4344](https://arxiv.org/abs/1404.4344) v4 (same text and numbering as the proceedings PDF).

**Verdict: ❌ False claim.** Observation 3.2 is false: `SEND([x/d⁺])` is a good `(d⁺ − 2d)`-balancer
only when `d◦ = d + 1`; in general it is a good `s`-balancer exactly for `s ≤ ⌈d⁺/2⌉ − d`, about
half the claimed value. That is still `Ω(d)` for `d⁺ ≥ 3d`, so the Table 1 entries built on it
survive. Observations 3.6 and 3.8 as printed (`max` instead of `min`) are false; the intended `min`
versions hold. All three lower bounds of Section 4 (Theorems 4.1–4.3) and Lemmas 3.5 and 3.7 are
true. The proofs of Theorems 4.2 and 4.3 needed repairs. The spectral upper bounds (Theorems 2.3,
3.3) were not formalized.

## Mistakes in the paper

* **Observation 3.2 is false (first claim).** The paper says `SEND([x/d⁺])` is a good
  `(d⁺ − 2d)`-balancer for `d⁺ > 2d`. When `x/d⁺` is rounded up, the `d` original edges use up `d`
  of the `e = x mod d⁺` extra tokens. Only `e − d` self-loops then get `⌈x/d⁺⌉`, but self-preference
  asks for `min{s, e}` of them. Smallest case: `d = 1`, `d◦ = 4`, `x = 3`. The original edge gets
  `[3/5] = 1` token and the four self-loops share the remaining two, so two self-loops get
  `⌈3/5⌉ = 1`. Self-preference with `s = 3` needs `min{3, 3} = 3`.
  We prove the exact characterisation: on a `d`-regular graph with `d < d◦`, `SEND([x/d⁺])` is a
  good `s`-balancer iff `1 ≤ s ≤ ⌈d⁺/2⌉ − d`. So, with halves rounded up, the paper's claim holds iff `d◦ = d + 1`. (The paper does not fix the
  tie rule; the counterexample above has no tie, so it refutes every reading.)
  Because `⌈d⁺/2⌉ − d ≥ (d◦ − d)/2`, the uses in Table 1 survive: `s ≥ 1` for `d⁺ > 2d`, and
  `s = Ω(d)` for `d⁺ ≥ 3d`. (`observation_3_2_false`, `sendRound_isGood_iff`)
* **Observations 3.6 and 3.8 are false as printed.** They bound the potential drop over `[t, t']`
  by `∑_{u∈U} max{s, x_t(u) − cd⁺}` (respectively `max{s, cd⁺ + s − x_t(u)}`). Counterexample: `K₂`
  with two self-loops per node and the good 2-balancer `SEND(⌊x/3⌋)`. Take `c = 1` and loads
  `(4, 0)`. Node 0 drops to load `3 = cd⁺` and `φ(1)` drops by only 1, but the printed bound demands
  `max{2, 1} = 2`. 3.8 fails the same way, with `c = 0` and loads `(1, 3)`. Appendix B.4 actually
  uses `min{s, ·}`, so this is a typo with evident intent. We prove the `min` versions.
  (`observation_3_6_false`, `observation_3_8_false`; repaired: `observation_3_6`,
  `observation_3_8`)
* **Theorem 4.3's construction is wrong; the theorem is true.** Appendix C.3 sets
  `f₀(v₁, v₂) = L` as soon as `b(v₁) ≥ ϕ` **or** `b(v₂) ≥ ϕ`. Take a node in layer `ϕ − 1 ≥ 1` with a neighbour
  in layer `ϕ`; every node of the shortest odd cycle through `u` at distance `ϕ − 1` from `u` is
  such a node. It sends `L ± 2` towards layer `ϕ − 2` and `L` towards layer `ϕ`, which contradicts the claimed
  `|f_t(v, v₁) − f_t(v, v₂)| ≤ 1`. No rotor-router step produces this; for example, on the 5-cycle
  the neighbour of `u` sends `L − 2` and `L`. For `ϕ = 1` every value is `L` and the discrepancy is
  `0`. Replacing "or" by "and" fixes the construction, i.e. the offset becomes
  `max{ϕ − min(b(v₁), b(v₂)), 0}`. We also make two smaller fixes. The proof's "odd cycle
  `u ⇝ v₁ → v₂ ⇝ u`" is only an odd closed walk; we prove that an odd closed walk contains an odd
  cycle that is no longer. And `u` can be any vertex. (`theorem_4_3`)
* **Theorem 4.2's proof fails for `d ≤ 3`; the theorem is true.** The paper uses a clique of
  `⌊d/2⌋` nodes with load `ℓ = |C| − 1`. That gives discrepancy `⌊d/2⌋ − 1`, which is `0` for
  `d ≤ 3`. The clique `{0, …, ⌊d/2⌋}` is also present in the paper's circulant graph and gives
  discrepancy `⌊d/2⌋ ≥ d/3` for `d ≥ 2`. For `d = 1` a single token suffices. The neighbour
  indices are written "mod `d`" where "mod `|C|`" is meant. The proof needs the stateless algorithm
  to be anonymous: every node uses the same `p◦, p₁, …, p_d`, and the adversary chooses the port
  numbering. We formalize the theorem in that model. (`theorem_4_2`)
* **Minor.**
  * Theorem 4.1's construction gives discrepancy `0` on `K₂` (`d = diam = 1`). That case needs a
    separate argument: one token on two nodes.
  * Theorem 4.1 needs a connected graph (otherwise the diameter is infinite), and Theorem 4.2 needs
    `d < n`.
  * The paper's offset set for the circulant graph contains `0`, i.e. a self-loop.
  * The introduction says that removing self-loops yields `Ω(d · diam)` (Theorem 4.3). Theorem 4.3
    gives `Ω(d · ϕ)`, where `2ϕ + 1` is the odd girth. The two agree on odd cycles.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`)
* Synchronous discrete diffusion on a finite simple graph `G` (usually `d`-regular) with `dl = d◦`
  self-loops per node, `d⁺ = deg + dl`. No failures, no randomness.
* A `Balancer` is deterministic and local. Node `v` in local state `σ` with load `x` sends
  `out v σ x w` tokens to each neighbour `w`, keeps `keep v σ x` tokens and moves to a new state;
  tokens are conserved. Stateless algorithms have `σ = Unit`.
* Self-loops matter only through their total, which is the tokens kept. The fairness predicates
  require a split `g : Fin dl → ℕ` of the kept tokens over the individual self-loops.
* `RoundFair` is the class of [17]: every edge, self-loops included, gets `⌊x/d⁺⌋` or `⌈x/d⁺⌉`.
  `CumulativelyFair` is Definition 2.1, and `IsGood` is Definition 3.1. They quantify over all
  local states and loads, or over all executions.
* `disc x = max − min`. "Cannot achieve discrepancy better than `D`" means: at every time step the
  discrepancy is `≥ D`.
* **ROTOR-ROUTER** (`RotorRouter.lean`, no self-loops): each node has a cyclic order of its edges
  and a rotor. The edge at position `i` gets `⌊x/d⌋ + [(i − ρ) mod d < x mod d]` tokens, and the
  rotor advances by `x mod d`. Theorem 4.3 chooses the edge orders and the initial rotors, as the
  paper's proof does.
* **Stateless algorithms in Theorem 4.2** (`StatelessLB.lean`): `StatelessAlg d` is one function
  of the load, giving the kept amount and one amount per port, used at every node. The adversary
  chooses the graph, the port numbering and the loads.
* Lemmas 3.5 and 3.7 are proved for arbitrary (also non-regular) graphs, with per-node threshold
  `c·(deg v + dl)`. They use only the one-step part of Definition 3.1.

**Main results in Lean.** Namespace `Podc.DeterministicLoadBalancing`.

| Paper | Lean | File |
|---|---|---|
| Theorem 4.1 (round-fair balancers: discrepancy `≥ d·diam/2`) | `theorem_4_1` | `RoundFairLB.lean` |
| Theorem 4.2 (stateless: discrepancy `≥ d/3`, every even `n`, `d < n`) | `theorem_4_2` | `StatelessLB.lean` |
| Theorem 4.3 (rotor-router, `d⁺ = d`: discrepancy `≥ d·ϕ`) | `theorem_4_3` | `RotorRouterLB.lean` |
| Lemma 3.5 (monotonicity and drop of `φ_t(c)`) | `lemma_3_5`, `phi_antitone` | `Potential.lean` |
| Lemma 3.7 (monotonicity and drop of `φ'_t(c)`) | `lemma_3_7`, `phi'_antitone` | `Potential.lean` |
| Observation 3.6 as printed — false | `observation_3_6_false` | `Potential.lean` |
| Observation 3.6 with `min` | `observation_3_6` | `Potential.lean` |
| Observation 3.8 as printed — false | `observation_3_8_false` | `Potential.lean` |
| Observation 3.8 with `min` | `observation_3_8` | `Potential.lean` |
| Observation 3.2 (`SEND([x/d⁺])` good `(d⁺−2d)`-balancer) — false | `observation_3_2_false` | `SendRound.lean` |
| Observation 3.2, exact version | `sendRound_isGood_iff` | `SendRound.lean` |
| Observation 2.2 (`SEND([x/d⁺])` cumulatively 0-fair) | inside `sendRound_isGood` | `SendRound.lean` |
| Observation 2.2 (ROTOR-ROUTER cumulatively 1-fair) | `rotorRouter_cumulativelyFair` | `RotorFair.lean` |

Auxiliary results:
* `rotorRouter_periodic`: any symmetric two-phase flow is realised periodically by the
  rotor-router.
* `exists_fair_rule`: a round-fair, fully self-preferring step exists for every load.
* `SimpleGraph.Walk.exists_odd_isCycle`, `SimpleGraph.oddGirth`, `SimpleGraph.oddGirth_le_length`
  (staged in `Podc/Foundations/Combinatorics/SimpleGraph/OddGirth.lean`, CSLib candidate).

**Not formalized.**
* Theorem 2.3 and Lemma 3.4 (spectral comparison with the continuous diffusion), Proposition A.2,
  Theorem 3.3 (phase argument on top of Lemma 3.4), and the ROTOR-ROUTER* part of Observation 3.2.
* The bounds of Table 1 depend on these and are not checked.

**Trust.**
* No `sorry`; the listed theorems use only `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity checks: `k2Send_isGood` (a good 2-balancer), `sendRound_isGood` (good `s`-balancers
  exist for all `d < d◦`), and Theorem 4.2 instantiated for a concrete algorithm. The balancers of
  Theorems 4.1 and 4.3 are explicit.
* Graph notions come from Mathlib (`SimpleGraph.dist`, `diam`, `IsRegularOfDegree`, walks/cycles).
  The odd girth is new (staged in `Podc/`).
