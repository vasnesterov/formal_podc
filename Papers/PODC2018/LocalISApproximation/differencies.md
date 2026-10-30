# Differences between the formalization and the paper

Paper: Boppana, Halldórsson, Rawitz, *Simple and Local Independent Set Approximation*, PODC 2018 (BA),
full version arXiv 1803.00786v1. Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Statement-level issues (decide the verdict)

1. **Theorem 2 is false as stated (❌, R3 not applicable, R5: secondary result).** "CaroWei has performance
   ratio at most `(d̄+2)/1.657`", i.e. `1.657·α ≤ (d̄+2)·CaroWei` for every graph. The proof derives
   `(d̄+2)/(4(√2−1))` and then writes `(d̄+2)/(4(√2−1)) ≤ (d̄+2)/1.657`, which is the wrong direction:
   `4(√2−1) = 1.65685… < 1.657` (`four_mul_sqrt_two_sub_one_lt`). The paper's own tightness family
   (bipartite with regular sides, `τ ≈ 1/√2`, large `d̄`) refutes the rounded constant:
   `K_{24000,10000}` has `α = 24000` but `(d̄+2)/1.657·CaroWei ≈ 23999.2` (`theorem2_false`; the smallest
   complete bipartite counterexample, by number of vertices, is `K_{13721,5683}`; found by exact rational
   search over all `K_{a,b}` with `a+b < 19404`; not part of the Lean development). The statement with
   the constant `4(√2−1)` is proved (`theorem2_corrected`).
   *Borderline call.* The intended constant is recoverable from the proof and the error is a rounding in the
   fourth significant digit, which argues for ⚠️ (R3). We chose ❌ because R3 explicitly excludes fixes
   that change "another constant … that is itself the claim" and the paper's proof itself asserts the
   wrong inequality. The result is in the introduction's contribution list, not the abstract, hence ❌ and
   not 🚨.
2. **Theorem 1 fails for `Δ = 0` (⚠️, R2).** With `Δ(G) = 0` the ratio `(Δ+1)/2 = 1/2 < 1` is impossible
   (`theorem1_false_zero`); the proof's step `O_i·(Δ+1)/(i+1) ≥ 2O_i` only covers `i ≥ 1`, and degree-0
   vertices need `Δ ≥ 1`. Formalized for every `Δ ≥ 1`. Similarly Theorem 3's ratio `(2Δ+1)²/(8Δ)` is
   undefined for `Δ = 0` (not formalized separately).
3. **Lemma 5 is false as stated (⚠️, R4).** It assumes only `a > b > 0` and `Z − Y ≥ X > 0`; without `Y > 0`
   the minimum need not be at `t = 1` (`lemma5_false`: `a=2, b=1, X=1, Y=−100, Z=−50`). The derivative
   argument needs `0 < Y + tX`. In the only use `Y = w(opt) > 0`; we prove Lemma 5 with `Y > 0`
   (and the weaker `a ≥ b ≥ 0`, `X ≥ 0`) (`lemma5`).
4. **Theorem 6's minimum is over `x ≤ 1` (⚠️, R3).** Over all `x ≤ 1` the expression
   `x²/(Δ+x) + 1/(xΔ+1)` takes negative values (`theorem6_min_unbounded`, at `x = −(Δ+1)`), so the formula
   is meaningless as written; the proof (`x = β = w(V′)/w(opt) ∈ [0,1)`) and the tightness example make
   clear that `0 ≤ x ≤ 1` is meant. Formalized with `x ∈ [0,1]`.
5. **Abstract: "For weighted graphs, it gives only a `Δ`-approximation" (⚠️, R3).** Read as a guarantee this
   is false: on `K_{Δ,Δ}` with weights `1` and `Q > Δ` the ratio exceeds `Δ`
   (`boppana_weighted_not_Delta`). Section 3 states and proves the correct `Δ+1`. Likewise the abstract's
   "0.529Δ" vs. the text's "0.529(Δ+1)" (same asymptotically). The PODC brief announcement's abstract
   already says `(Δ+1)` and `0.529(Δ+1)`, so this concerns the arXiv abstract only.
6. **"For `Δ = 2`, `1/ρ ∼ 0.593`, or `ρ ∼ 1.657 ∼ 0.562(Δ+1)`" (⚠️, R3).** `1/0.593 = 1.686 = 0.562·3`; the
   value `1.657` is a slip (it is the constant of Theorem 2). We prove `ρ(2) > 1.68` (`rho_two_gt`).
   ("20% smaller than `Δ`" is then about 16%.)

## Proof-level issues

7. **Theorem 4's indistinguishability argument (proof repaired, 🛠️).** The paper compares `G₁ = K_{Δ+1}`
   with an arbitrary `Δ`-regular bipartite `G₂`. But the model gives nodes knowledge of `n`, and
   `K_{Δ+1}` has fewer nodes than any `Δ`-regular bipartite graph, so the two are distinguishable in zero
   rounds. "Distributions over neighbourhoods are identical" also ignores the port numbers a node can
   learn (the port at the neighbour's end). Repair: `G₁` = `2k` disjoint copies of `K_{Δ+1}` and `G₂` =
   `k` copies of `K_{Δ+1,Δ+1}` minus a perfect matching, on the same node set
   `Fin k × ℤ/(Δ+1) × Bool`, with port `i` leading to `a+i+1` and the back port `Δ−1−i` in both
   graphs (`crown`). For each node `v` a permutation of the nodes fixing `v` maps its `G₁` view to its
   `G₂` view (`eval_crown_true`); averaging over labelings and random strings gives equal join
   probabilities (`joinWeight_crown`).
8. **Theorem 2's proof** uses the derivative of (5) in `t`; we replace it by an algebraic comparison with the
   `t = 1` point and absorb the "round up the lower order terms" step (`key_ineq`). For `α < n/2` it uses
   Turán's bound, as the paper does.
9. **Theorem 6's proof**: the paper applies Lemma 5 with `t = W/X`, undefined when `X = Δw(V′) = 0`
   (`V′ = ∅`); handled separately. Eq. (8) writes `w(Max)` for `E[w(Max)]`.

## Modelling choices

10. **Graphs**: finite simple graphs (`SimpleGraph` on a `Fintype`). "Performance ratio `f(Δ)`" is
    `HasPerformanceRatio B Δ ρ` (`α ≥ B ≥ α/ρ` for all `G` with `Δ(G) = Δ`, quantified over all finite
    vertex types in `Type`); tightness is `HasTightPerformanceRatio` (no smaller ratio holds). The upper bounds
    are also proved under the weaker hypothesis "all degrees `≤ Δ`".
11. **Boppana's algorithm** is formalized in its permutation form (2): a uniformly random bijection
    `σ : V ≃ Fin n` (counting measure on `n!` orderings), output = vertices preceding all neighbours;
    `E|B| = CaroWei` exactly (`expected_card_boppana`). The random-reals form (3) and the streaming/online
    remarks are not formalized. Caro–Wei `α ≥ CaroWei` is derived from this (`caroWei_le_indepNum`).
12. **Theorem 1 tightness**: the paper says "any regular bipartite graph"; we prove it for every
    `Δ`-regular bipartite graph (`regular_bipartite`: `CaroWei = n/(Δ+1)`, `α = n/2`) and use `K_{Δ,Δ}`.
13. **Theorem 3 tightness**: proved for every graph with `Δ(G) ≤ Δ`, `n = 4Δ`, `|E| = (2Δ−1)Δ` and an
    independent set of size `2Δ+1` (`tight_of_params`), instantiated with the paper's example (a circulant
    `Δ`-regular bipartite graph on `|A| = |B| = 2Δ−1` plus two isolated vertices, `exampleGraph`).
14. **Theorem 4 model** (stronger than or equal to the paper's): CSLib port-numbering `Algorithm` with local
    input (label `∈ Fin N`, random string `∈ R`), one synchronous round, unbounded messages/computation;
    `n`, `Δ`, `N` fixed (hence known). Randomness: i.i.d. strings from an arbitrary distribution `μ` on a
    **finite** set `R` (finite-precision randomness; the paper does not specify; continuous randomness is
    not covered). Labels: any `N ≥ n` (paper: `N ≥ Δn`). Correctness is required only on simple
    `Δ`-regular graphs with `n = 2k(Δ+1)` nodes and only with probability 1 (weaker hypothesis = stronger
    theorem). The lower bound holds for all `k ≥ 1`, i.e. for arbitrarily large `n`. Non-vacuity:
    Boppana's rule with random ranks and label tie-breaking is a correct algorithm in this model
    (`boppanaAlg_correct`). The proof bounds the expectation *averaged over all labelings*
    (`sum_expectedSize_eq`), so the lower bound holds both for adversarial labelings (`theorem4_ratio`,
    which assumes the ratio for every labeling) and for uniformly random ones.
15. **Weighted section**: weights are positive reals (paper: positive integers); the tightness example uses a
    real `β ∈ (0,1]`, as the paper's own example does. The upper bound for real weights covers integer ones;
    for integer weights the ratio is scale-invariant, so rational `β = p/q` (weights `q`, `p`) are realisable
    and, by continuity of `g_Δ`, the infimum is still approached (it may not be attained). `Max` uses `x_v ∈ [0,1]` uniform and `r_v = x_v^{1/w_v}` (`Real.rpow`); probability
    space `Measure.pi` of `volume.restrict [0,1]`. Lemma 2 and eq. (7) are proved measure-theoretically
    (`lemma2`, `expected_weight_max`). Theorem 6 is stated as: (upper) for every independent `I` there is
    `x ∈ [0,1]` with `w(I)·g_Δ(x) ≤ E[w(Max)]`; (tight) on `K_{Δ,Δ}` with weights `1, β`,
    `E[w(Max)] = w(opt)·g_Δ(β)`. Theorem 7: `ρ(Δ)/(Δ+1) → 2^{2/3}/3` with `ρ(Δ) = 1/inf_{[0,1]} g_Δ`.
16. The paper's formula `E[w(B)] = Σ_{v∈B} w(v)/(d(v)+1)` (§3) should sum over `v ∈ V`
    (`boppana_weighted`).

## Not formalized

- Theorem 5 (needs Alon's high-girth construction), the "(6) is tightest possible" claim in Theorem 2's proof,
  the Sakai et al. remark, Selkow's remark, the ε-min-wise/streaming remarks.
