# Differences between the formalization and the paper

Paper: P. Berenbrink, R. Klasing, A. Kosowski, F. Mallmann-Trenn, P. Uznański, *Improved Analysis of
Deterministic Load-Balancing Schemes*, PODC 2015 (arXiv:1404.4344v4; the proceedings PDF has the same
text). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Errors in the paper (statement level)

1. **Observation 3.2, first claim, is false** (R1: a numbered observation; R3 does not excuse it,
   because the fix changes the constant `s`, which is the content of the claim; R5: secondary,
   hence ❌, not 🚨). "`SEND([x/d⁺])` is a good `(d⁺ − 2d)`-balancer for `d⁺ > 2d`."
   * Counterexample: `d = 1`, `d◦ = 4`, `x = 3`; `K₂` in Lean (the example after
     `observation_3_2_false`).
   * General refutation: `observation_3_2_false`, valid whenever `d ≥ 1` and `d◦ ≥ d + 2`.
   * Exact characterisation: `sendRound_isGood_iff` (good `s`-balancer ⇔ `1 ≤ s ≤ ⌈d⁺/2⌉ − d`, for
     `d < d◦`, `d ≥ 1`). It uses rounding of halves upward (the paper only says "nearest integer"); the counterexamples do
     not involve ties. With halves rounded down the claim would also hold for even `d⁺` and `d◦ = d + 2`;
     it fails for every `d◦ ≥ d + 2` with `d⁺` odd under any tie rule.
   * Downstream claims still hold, assuming Theorem 3.3: Table 1's "`SEND([x/d⁺])`, `d⁺ > 2d`" needs
     only `s ≥ 1`, and "`d⁺ ≥ 3d`" needs `s = Ω(d)`; `⌈d⁺/2⌉ − d ≥ ⌈(d◦ − d)/2⌉` gives both.
2. **Observations 3.6 and 3.8 as printed are false** (R3: typo with evident intent → ⚠️).
   * The printed bounds have `max{s, x_t(u) − cd⁺}` and `max{s, cd⁺ + s − x_t(u)}`; Appendix B.4
     uses them with `min` ("contributes `x_t(u) − cd⁺` … contributes exactly `s`").
   * Counterexamples: `observation_3_6_false` and `observation_3_8_false`. They use `K₂`, `d◦ = 2`,
     the good 2-balancer `k2Send` (= `SEND(⌊x/3⌋)`), and `c = 1`, loads `(4,0)` (for 3.6) and
     `c = 0`, loads `(1,3)` (for 3.8). The printed statements are `Observation36Printed` and
     `Observation38Printed` (in ℤ).
   * Observation 3.8 also prints `φ_t(c)` instead of `φ'_t(c)` on the right-hand side; we read
     `φ'` (R3).
   * Proved instead: `observation_3_6` and `observation_3_8`. They drop the hypotheses
     `x_t(u) ≥ cd⁺ + 1` (resp. `x_t(u) < cd⁺ + s`), which only weakens the assumptions.

## Proof gaps / repairs (statements true)

3. **Theorem 4.3 (C.3).**
   * The flow `f₀(v₁,v₂) = L` "if `b(v₁) ≥ ϕ` *or* `b(v₂) ≥ ϕ`" violates the claimed
     `|f_t(v,v₁) − f_t(v,v₂)| ≤ 1`: a layer-`(ϕ−1)` node sends `L ± 2` and `L`. So it is not a
     rotor-router execution, and for `ϕ = 1` it yields discrepancy 0. Fixed by "and", i.e. the
     truncated offset `ϕ − min(b v₁, b v₂)`.
   * "We can construct an odd length cycle `u ⇝ v₁ → v₂ ⇝ u`": it is an odd *closed walk*. We prove
     that every odd closed walk contains an odd cycle of at most the same length
     (`SimpleGraph.Walk.exists_odd_isCycle`).
   * We use `L = ϕ + 1` (the paper: "sufficiently large `L`") and any vertex `u`. The paper takes
     `u` on a shortest odd cycle; Lean picks such a vertex, but the proof does not use it.
   * The paper's constant is `c`; we get `c = 1`, i.e. discrepancy `≥ dϕ`.
4. **Theorem 4.2 (C.2).**
   * The clique `C` of size `⌊d/2⌋` with load `ℓ = |C| − 1` gives discrepancy `⌊d/2⌋ − 1`, which is
     `0` for `d ≤ 3`, so the proof fails for `d ∈ {1,2,3}`. We use the clique `{0,…,⌊d/2⌋}` (also a
     clique of the paper's circulant graph) with load `⌊d/2⌋`, and for `d = 1` one token in total
     (`n ∤ 1`). Constant `c = 1/3`.
   * "`(i, (i+k) mod d)`" should be "mod `|C|`".
   * The offset set `{n − ⌊d/2⌋, …, n−1, 0, 1, …, ⌊d/2⌋}` contains `0` (a self-loop).
5. **Theorem 4.1 (C.1).** On `K₂` (`d = diam = 1`) the steady flow is all-zero and the discrepancy
   is `0` (R2: degenerate). We handle the cases `diam ≤ 1, d ≤ 1` with one token in total. Elsewhere
   we prove the paper's construction gives discrepancy `≥ d·diam/2`, constant `c = 1/2`. The paper's
   "there exists a way to assign `⌈⌉`/`⌊⌋` values" is proved (`steady_fair`): self-loops carry
   `b(v) − 1` each.

## Modelling choices

6. **Self-loops.** Only their total (the kept tokens) enters the dynamics. Fairness and
   self-preference are stated through an explicit split `g : Fin dl → ℕ` of the kept tokens, which
   is equivalent to sending over individual self-loops. Proposition A.2's "remainder" is not
   modelled; it is only needed for Theorem 2.3.
7. **Universality of the fairness predicates.**
   * `RoundFair` and the step part of `IsGood` quantify over all local states and loads, which is
     stronger than "along executions". This makes Theorem 4.1 (existential in the balancer) and
     Observation 3.2's positive part stronger.
   * Lemma 3.5/3.7 are also proved under the step condition only (`lemma_3_5_of_goodStep`), without
     cumulative fairness.
   * `CumulativelyFair` quantifies over all executions (all initial loads and times).
8. **Indexing.** Time starts at `0` (the paper's `x₁` is our `load x₀ 0`); `cumFlow t` sums steps
   `0..t` (the paper's `F_t`).
9. **Graphs.**
   * Theorem 4.1 assumes `G` connected; the paper's `diam` is finite only then.
   * Theorems 4.3, Lemmas 3.5/3.7 and Observations 3.6/3.8 do not need connectivity.
   * Lemmas 3.5/3.7 and Observations 3.6/3.8 do not need regularity either: thresholds are
     `c·(deg v + dl)` per node.
   * Theorem 4.2 builds a graph on `Fin n` and assumes `d < n`, which is necessary for a `d`-regular
     simple graph on `n` nodes; the paper leaves it implicit.
10. **Theorem 4.1's balancer** is stateless but node-dependent (node `v` knows its distance to
   `u`), as in the paper's construction. For loads that never occur it follows a default
   round-fair rule (`exists_fair_rule`). We assume `d⁺ ≥ 1` (otherwise no round-fair balancer
   exists).
11. **Theorem 4.2's algorithm class** is *anonymous* stateless deterministic algorithms: one
   function `load ↦ (p◦, p₁, …, p_d)` used by every node, with the adversary choosing the port
   numbering. The paper's proof needs anonymity (with node-dependent `p`'s the clique loads are not
   preserved). The paper only says the output "depends solely on the current load of `u`", which
   we read as anonymity. With non-anonymous rules the theorem is not established.
12. **Theorem 4.3's rotor-router.**
   * Has no self-loops (`d⁺ = d`, as in the theorem).
   * The cyclic edge order is chosen together with the initial rotors and loads. The paper's proof
     chooses the order ("it is enough to select an ordering of edges"), although the statement
     mentions only "initial load distribution and direction of the rotors".
   * `[NeZero d]` is an explicit hypothesis; it follows from non-bipartiteness.
   * The odd girth is `SimpleGraph.oddGirth : ℕ∞` (shortest odd cycle; `⊤` iff bipartite,
     `oddGirth_ne_top_iff`), and the theorem assumes `G.oddGirth = 2ϕ + 1`.
13. **Observation 3.2.**
   * `[x/d⁺]` rounds halves up: `roundDiv x D = (2x + D)/(2D)`.
   * `SEND([x/d⁺])` keeps the remaining tokens on self-loops; we take the split that gives `⌈x/d⁺⌉`
     to as many self-loops as possible. The refutation holds for every split, since
     `IsGood` asks only for the existence of a good split.
   * Assumes `d < d◦` (the paper's `d⁺ > 2d`).
   * The ROTOR-ROUTER* claim of Observation 3.2 is not formalized.
14. **Observation 2.2.**
   * `SEND([x/d⁺])` is shown cumulatively 0-fair (inside `sendRound_isGood`).
   * The ROTOR-ROUTER is shown cumulatively 1-fair for the self-loop-free rotor-router
     (`rotorRouter_cumulativelyFair`).
   * `SEND(⌊x/d⁺⌋)` is covered on `K₂` only, by `k2Send_isGood`.
15. **Constants.** The paper's "for some constant `c > 0`" is made explicit: `1/2` (Theorem 4.1),
   `1/3` (Theorem 4.2) and `1` (Theorem 4.3).

## Not formalized

Theorem 2.3, Lemma 3.4, Proposition A.2 and Lemma A.1 (spectral / mixing arguments); Theorem 3.3 and
its phase argument (B.4); the remark in Section 1.1 that the class contains ROTOR-ROUTER*; Table 1.

## Borderline calls

* Observation 3.2 → ❌ rather than ⚠️: the evident fix (`s = ⌈d⁺/2⌉ − d`) is not recoverable from the
  paper and changes the claimed constant. The asymptotic uses survive, so no headline is affected.
* Observations 3.6/3.8 → ⚠️: Appendix B.4 shows the intended `min`.
* Theorem 4.2 for `d ≤ 3`: the statement is true (constant `c ≤ 1/3`), only the proof fails → 🛠️.
