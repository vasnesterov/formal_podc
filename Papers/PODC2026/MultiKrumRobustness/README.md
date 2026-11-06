# MultiKrum and an optimal notion of robustness — PODC 2026

Gilles Bareilles, Wassim Bouaziz, Julien Fageot, El Mahdi El Mhamdi. *Brief Announcement: Byzantine
Machine Learning, MultiKrum and an Optimal Notion of Robustness.* PODC 2026. DOI
[10.1145/3796701.3815914](https://doi.org/10.1145/3796701.3815914). Formalized version: arXiv
[2602.03899](https://arxiv.org/abs/2602.03899) v1 (full version); numbering follows it.

**Verdict: 🔧 Easy fix.** All bounds hold: MultiKrum is robust with the stated upper bound (Theorems 1, 5, 6), the
lower bounds hold for `n ≥ 2` (Proposition 1, Theorems 3, 4, Proposition B.1), and so does the asymptotics of the
transition point (Theorem 2). The proofs of Theorem 2 and Proposition B.1 and the score values in Theorem 4 need local
changes only. Display (1) of Theorem 1 prints `≥` for the upper bound, and the lower bounds fail for `n = 1` under the
paper's own convention `0/0 = −∞`; both are slips.

## Mistakes in the paper

### ✏️ Slips
- Theorem 1, display (1) reads `κ⋆_m ≥ (n−f)/(n−2f)·min((√2+1)², κ^>_2(m))`, which is false for `f = 0`, `m = n`
  (`theorem_1_as_written_false`): MultiKrum is then the plain mean, so `κ⋆ ≤ 0`, while the right-hand side is
  `min((√2+1)², 1) = 1`. The theorem is announced as an upper bound and its proof proves `≤`. We prove that, together
  with "MultiKrum is robust" (`theorem_1`).
- Proposition 1, Theorem 3 (odd `n`), Theorem 4 for `n = 1`: with the paper's own convention `0/0 = −∞`, Krum on a
  single input is robust with `κ⋆ = −∞`, so these lower bounds, which all equal 0 for `n = 1` (Proposition 1:
  `κ⋆ ≥ f/(n−2f)`), fail there (`kappaStar_eq_bot_of_n_eq_one`). They hold for `n ≥ 2`.
- Theorem 3 states no hypotheses. We prove it under Definition 2's standing assumption `f ≤ n/2` (for `n = 2f`,
  `κ⋆ = +∞`, while the printed score `s(0)` is negative). At `n = 2` the paper's set `S` has zero variance and the bound
  is 0. The construction works for `n ≥ 3`, `n > 2f` (`theorem_3_even`, `theorem_3_odd`).
- Proposition B.1 at `f = 0`: the formula `R(n,f,m)` divides by `f`, although `n − 3f > 0` allows `f = 0`, and the
  configuration has zero variance. The bound holds for `f ≥ 1` (`prop_B1`).
- Table 1's `(n−f)`-MultiKrum entry omits the `min` of Theorem 1. Without it the entry exceeds Krum's bound when
  `f/(n−f)` is near 1, e.g. `n = 19`, `f = 9` (6.54 > 5.83), against the claim that MultiKrum's bounds are never worse.
  With the `min`, which is Theorem 1 itself, the claim holds.
- The proof of Lemma 3 swaps `∪` and `∩`.
- The proof of Theorem 2 writes `Cx⁴ = (A + f/x)²` for `Cx² = …`.
- The proof of Lemma 2 says "averaging over the larger set `S`", but `S` has the same size `n−f` as `N(x_i)`.

### Typos
- "the κ^<_2 regime becomes active" should be `κ^>_2`.
- Section 2.1: `s^X : ℝⁿ → ℝ` should be `ℝ^d → ℝ`.
- Section 3.2 calls the bounds of Appendix B `κ†_m` instead of `κ⋆_m`.
- Section 5 cites Theorem 3 for Theorem 1, and says "upper bound" for the lower bound of Theorems 3 and 4 at `m = 1`.
- The proof of Proposition B.1 writes `(1 + ϵ)e` for `(1 − ε)e`.

## Proof gaps (statements true)

### 🔧 Proposition B.1 (bias computation)
The proof writes the bias as `(a·f/(n−f) + (m−a)(1−ε))/m`, scaling `f/(n−f)` by `a/m` instead of 1; the
correct bias is `f/(n−f) + (m−a)(1−ε)/m`.

**Impact.** Statement still true, since the stated `R(n,f,m)` is below the correct limit; but B.1 as stated
does not contain Theorem 4. Repaired (`prop_B1_corrected`, `prop_B1`, `prop_B1_paper_lt_theorem_4`).

**Details.** The barycentre of the reference set is `x̄_S = −f/(n−f)·e`. The stated `R(n,f,m)` is therefore
not the limit of the ratio. It is still a lower bound, because it is at most the correct limit
`R' = (n−f)²/(f(n−2f))·(f/(n−f) + (m−a)/m)²`. At `m = n−f`, B.1 as stated gives
`f(2n−3f)²/((n−2f)(n−f)²) < 4f/(n−2f)`.

**Repair.** We prove the corrected `R'` and derive both B.1 and Theorem 4 from it (`prop_B1_corrected`,
`prop_B1`, `prop_B1_paper_lt_theorem_4`).

### 🔧 Theorem 2 (asymptotics of the transition point)
The proof's upper bound `m† ≤ (A² + √(A⁴ + 2Cf²))/C` (with `A = √(n−2f) + √(2f)`, `C = (√2+1)²`) reduces to
`2n/C`, not to `n/C·(1+o(1))` as claimed: at `f = 0` it equals exactly `2n/C = 2m†`.

**Impact.** Statement true; proved by solving the quadratic exactly (`theorem_2`, `mDagger_mul_div`;
`paper_upper_not_asymp` shows the gap).

**Repair.** Solving the quadratic in `√m†` gives `m†·C/n = g(f/n)` for an explicit continuous `g` with
`g(0) = 1` (`theorem_2`, `mDagger_mul_div`).

### 🔧 Theorem 4 and Proposition B.1 (score values)
The proofs give scores `f/(n−f)` and `(1−ε)(n−2f)/(n−f)` where the exact values are `f(1−ε)²/(n−f)` and
`(1−ε)²(n−2f)/(n−f)`.

**Impact.** The ordering, which is all that matters, is right (`theorem_4`, `prop_B1_instance`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Not a distributed-execution model. Aggregation rules are functions `F : (Fin n → E) → E` on `n`
  vectors in an arbitrary real inner product space `E` (the paper uses `ℝ^d`). Lower bounds assume
  `E ≠ 0`.
* The adversary chooses all `n` inputs and the honest set `S` (`|S| = n−f`). It is worst-case and
  deterministic; there is no randomness.
* The robustness coefficient `κ⋆(F)` is an `EReal` supremum of `‖F(x) − x̄_S‖²/Σ_S`, with the paper's
  `0/0 = −∞` and with `a/0 = +∞` for `a > 0`. `kappaStar_le_iff` turns `κ⋆ ≤ c` into the pointwise
  `‖F(x) − x̄_S‖² ≤ c·Σ_S`.
* The score `s(y)` is the sum of the `n−f` smallest `‖y − x_j‖²` divided by `n−f`. Every choice of
  the paper's `N(y)` ("`n−f` closest points, ties arbitrary") attains it
  (`IsNearest.sum_eq_nearestSum`), so the score does not depend on tie-breaking.
* `IsMultiKrum f m F` means that `F` outputs the mean of *some* set of `m` indices with smallest
  scores, on every input. All bounds (upper and lower) hold for every tie-breaking rule. Such rules
  exist (`exists_isMultiKrum`).
* Theorem 2 is stated for real `n, f` (`0 ≤ f`, `2f < n`). The `o(1)` is in ε–δ form and in filter
  form.

**Main results in Lean** (namespace `Podc.MultiKrumRobustness`).

| Paper | Lean | File |
|---|---|---|
| Definitions 1, 2 (MultiKrum, `κ⋆`) | `IsMultiKrum`, `kappaStar`, `IsRobust` | `Defs.lean` |
| Lemma 1 (mean–variance) | `lemma_1`, `lemma_1_self` | `UpperBound.lean` |
| Lemma A.1, A.2 (Young, Jensen) | `young`, `norm_sum_sq_le` | `UpperBound.lean` |
| Lemma 2, Lemma 3 | `lemma_2`, `lemma_3` | `UpperBound.lean` |
| Theorem 5 | `theorem_5` | `UpperBound.lean` |
| Theorem 6 | `theorem_6` | `UpperBound.lean` |
| Theorem 1 (MultiKrum robust, upper bound) | `theorem_1` | `UpperBound.lean` |
| Theorem 1, display (1) as printed (`≥`) is false | `theorem_1_as_written_false` | `UpperBound.lean` |
| Theorem 2 (transition point) | `theorem_2`, `theorem_2_tendsto`, `exists_unique_transition`, `mDagger_mul_div` | `Transition.lean` |
| Theorem 2, proof's bounds and the gap | `transition_ge_paper`, `transition_le_paper`, `paper_upper_not_asymp` | `Transition.lean` |
| Proposition 1 (universal lower bound) | `prop_1` | `LowerBounds.lean` |
| Theorem 3 (Krum lower bound) | `theorem_3_even`, `theorem_3_odd` | `LowerBounds.lean` |
| Theorem 4 (`(n−f)`-MultiKrum lower bound) | `theorem_4` | `LowerBounds.lean` |
| Proposition B.1 (as stated / corrected) | `prop_B1`, `prop_B1_corrected` | `LowerBounds.lean` |
| B.1 does not give Theorem 4 | `prop_B1_paper_lt_theorem_4` | `LowerBounds.lean` |
| `n = 1` degenerate case | `kappaStar_eq_bot_of_n_eq_one`, `exists_isMultiKrum_kappaStar_eq_bot` | `LowerBounds.lean` |

`Config.lean` holds the 1-D configurations used by the lower bounds: `x_i = c_i·e`, index blocks,
and lemmas pinning down the selected set when scores are strictly separated.

**Not formalized.** Remark 1 (comparison with the original Krum score of [BEGS17]); the experiments
of Section 5; the remarks linking `κ⋆` to `(f,κ)`-robustness and to SGD convergence [AFG+23].

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: MultiKrum rules exist for every `m ≤ n` (`exists_isMultiKrum`), and every
lower bound is proved for *all* MultiKrum rules. Self-contained on Mathlib: no CSLib model is used.
CSLib candidates, marked `-- CSLib candidate`: the parallel-axis identity, Lemma 1, Young, Jensen in
inner product spaces (`UpperBound.lean`), and the "`k` nearest points minimise the sum" lemma
(`Defs.lean`).
