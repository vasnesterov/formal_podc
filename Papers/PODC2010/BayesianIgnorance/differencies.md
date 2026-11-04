# Differences between the formalization and the paper

Paper: Alon, Emek, Feldman, Tennenholtz, *Bayesian Ignorance*, PODC 2010 (full version of May 9, 2010,
17 pp., with appendix). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Model

1. **Costs are `ℝ≥0∞`-valued** (`Cslib.GameTheory.BayesianGame`). The paper's general model allows real
   (possibly negative) costs `C_{i,t} : A → ℝ`; its NCS games have costs in `ℝ≥0 ∪ {∞}`. All quantities the
   paper studies (ratios of social costs) only make sense for non-negative costs, and every result of Section 3
   is about NCS games, so nothing is lost. Section 4 uses its own real-valued model (positive costs), as the
   paper does (`CostTuple`).
2. **Expectations** are finite sums `∑_t p(t) · X(t)` in `ℝ≥0∞` with `0 · ∞ = 0`: type profiles of prior
   probability 0 never matter. The paper's conditional form of the equilibrium condition
   (`E[X_i(s) | t_i] ≤ …`) is replaced by the ex-ante form (the paper's primary definition); the conditional
   form is derived when the agent's ex-ante cost is finite (`IsBayesEq.cond_le`). With infinite costs at
   another type of the same agent the two forms are *not* equivalent (`⊤ ≤ ⊤`); the paper calls them
   equivalent. This only matters in the degenerate case where some destination of positive probability is
   unreachable (then `opt^C = ∞` and all of Section 3 is trivial). Not a mistake of any numbered statement.
3. **Ratios are stated multiplicatively**, e.g. `worst-eq^P ≤ k · opt^C` instead of
   `worst-eq^P / opt^C ≤ k`. This is the paper's meaning when the denominator is in `(0, ∞)` and avoids
   `0/0`, `∞/∞`.
4. **Minima/maxima over equilibria** are `⨅`/`⨆` in `ℝ≥0∞` (`best-eq = ⊤`, `worst-eq = 0` if no equilibrium
   exists). The paper restricts attention to games with pure equilibria; we prove existence for every
   Bayesian NCS game (`exists_isBayesEq`), and Observation 2.2 assumes an equilibrium exists.
5. **Exact potentials in additive form** (`C_i(s) + Q(s') = C_i(s') + Q(s)`), equivalent to the paper's
   difference form for finite values.
6. **Networks** are abstract: a step relation `step e u v` and costs `c : E → ℝ≥0`
   (`Cslib.GameTheory.Network`); this covers directed and undirected (multi)graphs at once, so Lemmas 3.1
   and 3.8 are proved for both. "`a_i` contains an `(x_i, y_i)`-path" is reachability inside `a_i`
   (`Connects`); the empty set connects `x` to `x`.
7. **Type spaces** `T_i = V × V`, action spaces `A_i = 2^E`, exactly as in the paper.
8. **Asymptotic statements** (`Ω(k)`, `O(1/log k)`, `Θ(k)` vertices) are made explicit: for every `k₀` there
   is `k ≥ k₀` and a game with explicit vertex count and an explicit inequality with explicit constants.
   The paper's "`k`-agent" games of Lemmas 3.6 and 3.7 have `k + 1` agents (as in the paper's proofs).

## Section 2

9. **Observation 2.1** is proved verbatim (additive form, `observation_2_1`). **Observation 2.2**
   (`observation_2_2`) is proved for games with a pure Bayesian equilibrium, as stated; we also prove
   `opt^C ≤ best-eq^C ≤ worst-eq^C` (the latter when every underlying game of positive probability has a
   pure Nash equilibrium).
10. **The Rosenthal potential of Bayesian NCS games (end of Section 2) is not a potential as written.**
    The paper defines the cost of an agent whose edge set does not contain her path as `∞`, with
    `A_i = 2^E`, and then claims (via Observation 2.1) that
    `Q(s) = ∑_t p(t) ∑_e c(e) H(|{i : e ∈ s_i(t_i)}|)` is a Bayesian potential. A deviation from a
    connecting to a non-connecting edge set changes the agent's cost by `∞` but `Q` by a finite amount,
    so the identity `C_i(s) − C_i(s') = Q(s) − Q(s')` fails. Worse, the global minimiser of this `Q` is
    the all-empty profile (`Q = 0`), which is not an equilibrium. Rule **R4** (an implied restriction
    to path-containing actions, standard in the NCS literature where strategies are paths): **⚠️**.
    Repair: the identity holds between *feasible* profiles (every agent connects whenever possible),
    and a minimiser of `Q` over feasible profiles is a Bayesian equilibrium (`isBayesEq_of_isMin`,
    `exists_isBayesEq`), via the per-state identity `payment_add_potential_update`.
    Lean counterexample (one agent, one edge `0 → 1` of cost 1, point prior):
    `RosenthalCounterexample.no_finite_bayesPotential` (no finite-valued function is a Bayesian
    potential of that game) and `RosenthalCounterexample.empty_minimises_not_isBayesEq` (the empty
    profile minimises `Q` and is not an equilibrium). The same applies to the per-state sentence
    "this potential function turns out to be `q(a)`" (cited from [4], whose strategies are paths).

## Section 3

11. **Lemma 3.1** (`lemma_3_1`): proved as stated (multiplicatively), for directed and undirected graphs.
    The paper's proof uses the conditional equilibrium condition per type; we deviate at all types
    simultaneously to cheapest connecting sets, which needs no conditioning (see item 2).
12. **Lemma 3.2** (`Lemma32.lemma_3_2`, `Lemma32.lemma_3_2_prime`): proved, in the stronger form stated by
    the paper (`opt^P ≥ (k−1) · worst-eq^C`, with `worst-eq^C = 1`), plus the consequences
    `(k−1) · opt^C ≤ opt^P` and `(k−1) · best-eq^C ≤ best-eq^P`; `2(k−1)² + (k−1) + 1` vertices.
    - We use affine planes over `ZMod q`, `q` prime (the paper: any prime power); enough for "for every
      `k₀`". The prior is uniform over (line, permutation), as the paper intends (it does not say
      "uniform" explicitly).
    - Proof slip (typo-level): "agent `i` buys the right edge with probability `1/m`" should be `1/(m+1)`
      (a point lies on `m+1` lines); "`K(s) = m(1 − 1/m) = m − 1`" forgets agent `k`'s edge and is only a
      lower bound (agents may buy more). Correct bound: `opt^P ≥ 1 + m²/(m+1) ≥ m = k − 1`.
    - "The unique Nash equilibrium" is unique only up to zero-cost edges `(v_ℓ, w_p)`; every Nash
      equilibrium costs exactly `1` (`isNashEq_inl`), which is what is needed.
13. **Lemma 3.3** (`Lemma33.lemma_3_3`): proved, with `worst-eq^P ≤ 1 + ε`, `best-eq^C ≥ H(k−1)/2` and
    `ln k · worst-eq^P ≤ 4 · best-eq^C`; graph with `k + 1` vertices (Θ(k)).
    - The paper never fixes `ε` (it appears only in Figure 1). The claimed equilibrium needs
      `ε < 1/(2i+1)` for the agent `i` joining `(x, z)`, i.e. `ε < 1/(2k−1)`; we assume
      `ε(2k−1) < 1` (`worstEqP_le`) and `ε > 0` (`half_hnum_le_bestEqC`). For larger `ε` the profile is
      not an equilibrium. Proof gap (🛠️), together with the next point.
    - "`s` is the *unique* Bayesian equilibrium" is false literally: agents may additionally buy
      zero-cost edges `(z, y_j)`. All equilibria have the same social cost `1 + ε`, which is what we
      prove (and what the lemma needs). Same for "the unique Nash equilibrium" when agent `k` stays at
      `x`: unique up to zero-cost edges; we prove every Nash equilibrium there costs `≥ H(k−1)`.
    - `lemma_3_3` also states `best-eq^C(G) ≠ ∞`, so the ratio bound is not satisfied trivially.
    - The paper's "induction on `i`" is made precise: strong induction on the agent index, using
      that no agent buys an unneeded positive-cost edge (`not_isBayesEq_of_removable`).
    - The claim of Section 3 / the introduction that in this game "the worst Bayesian equilibrium
      achieves the expected cost of the globally optimal outcome" and "`opt^C(G) = worst-eq^P(G) = O(1)`"
      is proved for `k ≥ 3` (`ignorance_is_bliss`: `worst-eq^P = opt^C = 1 + ε`). For `k = 2` it fails
      (`opt^C = 1 + ε/2`), a degenerate case (R2) irrelevant to the asymptotic claim.
14. **Lemma 3.4** (`opt^P/opt^C = O(log n)` in undirected graphs, via FRT tree embeddings and Gupta's
    Steiner-point removal) is **not formalized** (FRT is not in Mathlib/CSLib).
15. **Lemma 3.5**: only the paper's reduction is formalized (`Lemma35.lemma_3_5`): for every
    distribution `q` over request sequences, `opt^P(G^q) ≥ α · opt^C(G^q)` whenever every deterministic
    online Steiner tree algorithm (valid on the support of `q`) pays at least `α · E_q[OPT]` in
    expectation. The cited distributional Imase–Waxman `Ω(log n)` lower bound on the diamond graph is a
    hypothesis (`hLB`), not proved. Request sequences are `Fin n → Option V` (holes allowed), a harmless
    generalization of `V^{≤n}`; the reduction holds for any network. We prove `opt^C(G^q) ≤ E_q[OPT]`,
    the direction the reduction needs. The remark after Lemma 3.5 (best-eq version on the diamond graph,
    Euclidean `Ω(log k / log log k)` via Alon–Azar) is not formalized.
16. **Lemmas 3.6 and 3.7** (`lemma_3_6`, `lemma_3_7`, `Lemma36.lean`): both proved, stated as
    `(k+1) · worst-eq^C ≤ 4 · worst-eq^P` with `0 < worst-eq^C`, `worst-eq^P ≠ ∞` (Ω(k)), resp.
    `(k+1) · worst-eq^P ≤ 4 · worst-eq^C` with `0 < worst-eq^P`, `worst-eq^C ≠ ∞` (O(1/k)), on the 3-vertex
    undirected triangle `G_worst`, with `k + 1` agents (`k ≥ 3`, resp. `k ≥ 2`; the paper states no range).
    - **The appendix proofs are swapped** (🛠️, statements true): the "proof of Lemma 3.6" gives
      `worst-eq^P = 3/2 + ε` and `worst-eq^C ≥ (k+2)/2`, i.e. ratio `O(1/k)` = Lemma 3.7
      (`worstConstructionA`); the "proof of Lemma 3.7" gives `worst-eq^P ≥ k + 2` and
      `(1−1/k)(1+ε) ≤ worst-eq^C ≤ (1−1/k)(1+ε) + (k+3+ε)/k`, i.e. ratio `Ω(k)` = Lemma 3.6
      (`worstConstructionB`). Each lemma is proved by the other's construction.
    - "Proof of 3.6": uniqueness of the Bayesian equilibrium is argued only against the profile where all
      agents route via `v`; mixed profiles must be excluded too (done in `triA_socialCost`). The
      equilibrium is unique on types of positive probability; off-support strategies are arbitrary.
    - "Proof of 3.7": the unique Nash equilibrium at destination `u` buys `(u, w)`, not "`(u, v)`"
      (typo); the agent cost is `1 + 2/k − 1/k²`, not `1 + 2/k − 2/k²` (arithmetic slip; the paper's
      range `2/k − 1/k² < ε` is exactly what the correct value needs, and `≤` suffices).
    - Directed variants ("a trivial modification") are not formalized.
17. **Lemma 3.8** (`lemma_3_8`): proved as stated. The paper's proof minimises the potential over all
    strategy profiles, whose minimiser is the empty profile (item 10); we minimise over feasible profiles,
    and handle unreachable destinations (then `opt^P = ∞`). Proof repair (🛠️), consequence of item 10.
18. **Table 1** universal bounds derived from the lemmas: `table_upper_k` (`opt^P/opt^C`,
    `best-eq^P/best-eq^C`, `worst-eq^P/worst-eq^C` are `≤ k`), `bestEqC_le_hnum_mul_bestEqP`
    (`best-eq^P/best-eq^C ≥ 1/H(k)`, via the price of stability `H(k)` of Anshelevich et al., which we
    re-derive as the point-mass case of Lemma 3.8: `bestNash_le_hnum_mul_opt`) and
    `worstEqC_le_card_mul_worstEqP` (`worst-eq^P/worst-eq^C ≥ 1/k`, via the point-mass case of Lemma 3.1,
    `worstNash_le_card_mul_opt`). The `O(min{k, log k log n})` entry needs Lemma 3.4 (not formalized).

## Section 4

19. **Proposition 4.1** (`proposition_4_1`): proved, together with the stronger pointwise statement
    `roeBound_iff_eorBound` (for every `r`, the RoE bound holds iff the EoR bound holds) via the bijection
    `p ↦ p·v/⟨p,v⟩` of the simplex. The appendix proof assumes that `sup_p min_i ratio` is attained
    ("by definition, there exists some `p` such that for all `i` the ratio is `≥ r*`"), true by
    compactness but not argued; and "`r*` is the minimum real such that …" presupposes that the minimum
    exists, which we prove (`exists_isLeast_eorBound`). Routine (✅-level) remarks. Nonempty index sets
    (and at least one agent) are assumed explicitly. Only `v > 0` is needed for the equivalence; `M > 0`
    is used for the existence of the minimum.
20. **`RoE(φ) = EoR(φ)`** (`CostTuple.roe_eq_eor`, `isRoE_iff_isEoR`): proved.
21. **Lemma 4.2** (`CostTuple.lemma_4_2`): proved, using Sion's minimax theorem from Mathlib in place of
    von Neumann's. The existence part only needs that the bound `r` holds, not that it is least. The
    remark that the conclusion also holds "in the limit" when some costs are 0 (with `0/0 = 1`) is not
    formalized.

## Verdict

**⚠️ Minor statement issues**, decided by item 10 (the explicit main-text claim that Rosenthal's `Q` is a
Bayesian potential of Bayesian NCS games is false under the paper's `∞`-cost definitions; excused under
**R4** because restricting to path-containing actions is the standard NCS convention). Borderline call recorded:
the sentence ("Observation 2.1 implies that the function `Q` … is a Bayesian potential function for that
Bayesian NCS game") is an explicit main-text claim of a result, not a step inside a proof, so it is a
statement under **R1** (hence ⚠️ rather than 🛠️); it is not ❌ because the intended reading (actions
restricted to connecting edge sets, as in the cited NCS literature) is the standard convention and no
numbered result depends on the literal version (R4). All numbered
statements checked (Observations 2.1–2.2, Lemmas 3.1, 3.2, 3.3, 3.5 (reduction), 3.6, 3.7, 3.8,
Proposition 4.1, Lemma 4.2) are true; proof repairs (🛠️): Lemma 3.8 (item 17), Lemma 3.3 (item 13),
Lemmas 3.6/3.7 swapped proofs (item 16); typo-level slips in the proofs of Lemmas 3.2 and 3.7.
