# Differences between the formalization and the paper

Paper: Alistarh, Chatterjee, Karrabi, Lazarsfeld, *Game Dynamics and Equilibrium Computation in the
Population Protocol Model*, PODC 2024 (arXiv 2307.07297v3). Rules R1–R6 refer to the project's
verdict scale.

## Statement-level issues

1. **Theorem 2.5, upper bound — false (❌, R5: secondary result).** The theorem fixes any
   `a, b > 0` with `a + b ≤ 1` and claims `t_mix = O(min{k/|a−b|, k²}·m log m)` (`a ≠ b`) and
   `O(k² m log m)` (`a = b`), with the dependence on `a, b` shown explicitly. The text below the
   theorem stresses "the impact of more biased a and b". For `k = m = 2` and `b ≤ a`, every `t` with
   `d(t) ≤ 1/4` has `t ≥ 1/(2a)` (`isMixedAt_two_two`). So no constant `C` satisfies the bound for
   all `a = b` (`theorem_2_5_upper_false`), nor for all `a = 2b` (`theorem_2_5_upper_false_ne`).
   - *Why not R2/R4.* `a + b < 1` is explicitly allowed by Definition 2.3, and the paper's own
     application has `a + b = γ < 1`. Small `a + b` is a legitimate parameter range, not a
     degenerate corner.
   - *Why not 🚨 (R5).* The paper presents Theorem 2.5 as a tool for Theorem 2.7 that "may be of
     independent interest". The contribution list (§1.2) names Theorem 2.7, not Theorem 2.5. The
     headline mixing bound of Theorem 2.7 remains true after the fix (`a + b = γ`, `m = γn`), but we
     did not formalize it.
   - *Location of the error.* Proposition A.7. For `a = b`, `G_t = Z_t² − t` is not a martingale
     (`E[Z_{t+1}² − Z_t²] = a + b`), so `E[τ_absorb] = k²/(2a)`. The bound "RHS of (26) `≤ k²`"
     likewise tends to `k²/(a+b)`. The correct statement multiplies the `k²` terms by `1/(a+b)`.
   - *Reading of the `O`.* `theorem_2_5_upper_false*` refute the bound read uniformly in `a, b`
     (the reading the paper intends: it displays the dependence on `|a − b|`, and Theorem 2.7 plugs
     `a − b = γ(1 − 2β)` into it). If the `O` were allowed to hide constants depending on `a, b`, the
     displayed Theorem 2.5 would be true, but then the false statement is located in the numbered,
     constant-free lemmas below, so the label is ❌ under either reading (R1).
   - *Numbered lemmas behind it — false (❌, R1).* **Proposition A.7** (`E[τ_absorb] ≤ k²` for
     `a = b`; truth `k²/(2a)`, false for every `a < 1/2`), **Lemma A.5** (`E[τ_coal] ≤ min{k/|a−b|,
     k²}`, resp. `≤ k²`; for `k = 2`, `X_0 = 1`, `Y_0 = 2` the two walks coalesce at the first non-null
     step, so `E[τ_coal] = 1/(a+b)`, false for `a + b < 1/4`) and **Lemma A.8**
     (`Pr[τ_couple > 2Φ log(4m)] ≤ 1/4`). For Lemma A.8 we have a Lean refutation at fixed parameters
     (`lemma_A_8_false`). For `k = m = 2`, `a = 1/100`, `b = 1/200` (so `a > b`, as Lemma A.8
     requires) we have `Φ = 8` and `2Φ log₂(4m) = 48`, yet `d(t) > 1/4` for all `t ≤ 48`. By the
     coupling inequality (22) (`d(t) ≤ max_{x,y} Pr[τ_couple > t]`, a standard fact we did not
     formalize), some `x, y` violate Lemma A.8. Propositions A.7 and Lemma A.5 are checked by hand
     only (expected hitting times are not formalized).
2. **Theorem 2.7 / Section 2.2.1 — sampling convention (⚠️, R4; borderline with ❌).** The formula
   `p_j ∝ (1/β − 1)^{j−1}` is exact iff the responder is drawn uniformly from all `n` agents,
   independently of the initiator (`replKernel`; `theorem_2_7_stationary` proves the stationary part
   in that model). Under the standard PP scheduler (distinct ordered pair, `distinctKernel`), the
   count process is the `(k, γ(n−1−βn)/(n−1), γβn/(n−1), m)`-Ehrenfest process
   (`distinctKernel_counts`). Its stationary law has ratio `(1/β − 1) − 1/(βn)`.
   `distinct_counterexample` shows the claimed law is not stationary for one AD and two GTFT agents
   (`k = 2`).
   - *Why ⚠️.* The paper never names the scheduler, but its computation (5) uses the
     with-replacement probabilities `(z_j/n)(1−β)`, so the intended model can be recovered from the
     paper. The formula is exactly right there.
   - *Why borderline.* "Agents interact in pairs" normally means distinct pairs in the PP
     literature the paper cites, and a GTFT agent "meeting itself" is unusual.
   - The verdict does not depend on this call (item 1 is ❌).
3. **Proposition A.9 — "`D ≥ km`" (⚠️, R3).** The diameter of the transition graph is `(k−1)m`.
   For `k = m = 2` the graph is the path `(2,0) – (1,1) – (0,2)`, so `D = 2 < km = 4` (a hand check;
   not in Lean). The proposition's purpose, `t_mix = Ω(km)`, holds. We prove `t_mix ≥ (k−1)m/2`
   for all `a, b` and every distribution `π` (`theorem_2_5_lower`). The local fix `k → k−1` is
   recoverable, and the claim is asymptotic.
   - *Borderline (⚠️ vs ❌).* The proof also reasons with `km` ("at least `km` total transitions are
     needed"), which by R3 argues against the excuse. We keep ⚠️ because the proposition's stated
     purpose (`t_mix = Ω(km)`) is unaffected and `(k−1)m ≥ km/2` for `k ≥ 2`. The verdict does not
     depend on this call (item 1 is ❌).
4. **Theorem 2.7, lower bound `Ω(kn)` (not formalized; proof gap).** Theorem 2.5 gives
   `Ω(km) = Ω(kγn)`, which is `Ω(kn)` only for constant `γ`. The statement itself is plausible: the
   chain is lazy with rate `≤ γ`, which compensates. We did not formalize it, so it does not enter
   the verdict.

## Proof gaps (statements true)

- **Theorem 2.4, uniqueness.** A.3 checks detailed balance and concludes "π is the unique stationary
  distribution". Uniqueness needs irreducibility, which the paper argues only for `k = 2, 3` ("easy
  to see"). We prove irreducibility for all `k`: every state reaches `(m, 0, …, 0)`, and
  reversibility with a positive `π` makes steps symmetric (`ehrenfest_isIrreducible`). We also prove
  uniqueness for irreducible finite chains (`IsStationary.unique`).
- **Section 2.2.1, "`{z^t}` is exactly a `(k,a,b,m)`-Ehrenfest process".** The paper only lists the
  transition probabilities of `z`. We prove exact lumpability of the agent-level chain along
  `counts` for any uniform scheduler (`schedKernel_lump`) and the resulting `t`-step identity
  (`schedKernel_pow_counts`).
- **Proposition 2.8.** It uses `E[π_j] = m p_j` (the multinomial mean, stated as "known" in §2.1).
  We prove it (`sum_mul_multinomialPMF`) and verify the closed form via
  `(λ−1)² ∑_{i<k} iλ^i = (k−1)λ^{k+1} − kλ^k + λ` (`generosity_closed_form`). Both cases
  (`β ≠ 1/2`, `β = 1/2`) hold as stated.

## Modelling choices and changed definitions

- **Indices.** Urns / generosity levels are `Fin k = {0, …, k−1}`. The paper's `g_j`, `x_j`, `p_j`
  (`j ∈ [k]`) are our index `j − 1`, so `p_j ∝ λ^{j−1}` becomes `ehrParam k λ j = λ^j / ∑_i λ^i`, and
  `g_j = ĝ (j−1)/(k−1)` becomes `ĝ · j/(k−1)`.
- **Definition 2.3.** It is defined as an urn chain (`urnKernel`) with nearest-neighbour rates. The
  entrywise lemmas `ehrenfest_apply_up/down/self/other` show it is the matrix of Definition 2.3.
  The diagonal is given in "generator form", so row sums are `1` by construction.
- **Stationary distributions** are probability vectors with `π ᵥ* P = π`.
  `theorem_2_4` / `ehrenfest_stationary_unique` say: every stationary distribution equals the
  multinomial. `ehrenfest_isStationary` says: the multinomial is stationary.
- **Generality.** `ehrenfest_stationary_unique` and the corollaries hold for all `k ≥ 1`, `m ≥ 0`
  (the paper assumes `k, m ≥ 2`). `theorem_2_4` keeps the paper's hypotheses `k, m ≥ 2`.
- **Theorem 2.7, hypotheses.** We assume `numAD > 0` (`β > 0`; otherwise `1/β` is undefined) and at
  least one GTFT agent (`m > 0`). Together these give `0 < β < 1`, `0 < γ`, `a + b = γ ≤ 1`.
- **Theorem 2.7, "converges to π".** Not formalized: we prove the count process is the Ehrenfest
  process and identify its unique stationary distribution. Convergence would need aperiodicity
  (true here: `a + b = γ < 1` makes every state lazy) and the finite-chain convergence theorem,
  which is absent from Mathlib/CSLib.
- **Mixing time.** `t_mix ≤ T` is "∃ `t ≤ T` with `d(t) ≤ 1/4`" (`IsMixedAt`), and
  `d(t) = max_x ‖P^t(x,·) − π‖_TV`. The negations in `theorem_2_5_upper_false*` refute "∃ `C`, ∀
  admissible `a, b`, `t_mix ≤ C·f(k,a,b,m)`" for `k = m = 2` (`log` is the natural logarithm; any
  base works).
- **Population.** An `(α, β, γ)` population is a finite agent type `A` with a kind map
  `τ : A → Kind`. AC and AD agents never change (`igt` is one-way: only a GTFT initiator updates).
  The paper's `Inc/Dec` truncation is `inc`/`dec`. The configuration space `Cfg τ` contains the
  configurations consistent with `τ`.
- **Proposition 2.8.** `g̃` is stated as `(1/m) ∑_j g_j · ∑_x π(x) x_j` for *any* stationary
  distribution `π` of the count chain. By Theorem 2.7 this is the unique one.

## Not formalized

Proposition 2.2 (payoff monotonicity), Theorem 2.9 (ε-approximate distributional equilibrium),
Appendices B–D, the coupling upper bound of Theorem 2.5 (Lemmas A.5, A.8, Prop. A.6) in corrected
form, and the mixing-time and convergence parts of Theorem 2.7.
