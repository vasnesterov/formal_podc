# Differences between the formalization and the paper

Paper: Feinerman, Korman, Lotker, Sereni, *Collaborative Search on the Plane without Communication*, PODC 2012,
arXiv 1205.2170v2. Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Modelling choices

1. **Plane = grid `ℤ²`, distance = ℓ₁ (hop) distance** (as in §2). Source `s = (0,0)`.
2. **Agents in the lower bounds.** An agent is a probability law on trajectories `ℕ → ℤ²` (`Traj`); the `k`
   agents are independent (`Measure.pi`). The trajectory up to the find time cannot depend on the unknown `τ`, so
   a `τ`-independent law is no restriction. We do **not** require grid walks. Any motion with one node per time
   unit is allowed, so the lower bounds (Thm 4.1, 4.2, footnote 2's `D²/k` part) are *stronger* than stated.
   Only footnote 2's `Ω(D)` part assumes walks from the source (`IsWalk`).
3. **Expected running time.** `T(D,k)` is the expectation of the first time some agent is at `τ`, as a
   `lintegral` in `ℝ≥0∞` (`expectedTime`). `φ`-competitive (`IsCompetitive`, `IsCompetitiveAdvice`) means
   `T ≤ φ(k)(D + D²/k)` for all `k ≥ 1` and all `τ` with `D ≥ 1`. The paper says "for every integers `k` and `D`".
   The case `D = 0` only says that the agents start at `s`; dropping it makes the lower bounds stronger.
4. **Advice (§4.2).** Agent `a` with estimate `k̃ₐ` moves by the law `A k̃ₐ`. Competitiveness is required for all
   `k ≥ 1` and all assignments of valid estimates (`k̃ₐ^{1−ε(k̃ₐ)} ≤ k ≤ k̃ₐ`, real powers). The proof, as in the
   paper, uses only equal estimates.
5. **Upper bounds use the paper's navigation abstraction** (§2, footnote 1). The walk to `u` takes `d(u)`
   steps, and a spiral of length `t` takes `t` steps and ends within distance `t` of its start. A spiral of
   length `t` from `u` visits every `v` with `σ·d(u,v)² ≤ t`, and in Thm 5.1 it visits such a `v` within
   `σ·d(u,v)²` steps (prefix property of spirals). The paper takes `σ = 4` ("visits all nodes at distance
   `≤ √x/2`"); our theorems hold for every `σ ≥ 1`, with constants depending on `σ`. The primitives are not
   constructed in Lean.
6. **Upper-bound running time.** Phase "uniform `u ∈ B(R)`, spiral `t`, return" is bounded by `2R + 2t`.
   Block (stage / big stage) durations are bounded by the sum over the phases of the maximum over agents
   (`blockDur`). The running time is bounded by `∑_b dur(b) · 1[no agent succeeded in a block < b]`
   (`timeBound`), and its expectation is computed exactly (`lintegral_timeBound`). All random choices are
   independent (`Measure.infinitePi` over agents × phases). This bounds the paper's running time from above under
   assumption 5. The real search may end earlier, e.g. on the way to `u`.
6a. **Upper bounds for `D ≥ 1` only.** `theorem_3_1`, `corollary_3_2`, `theorem_3_3` and `theorem_5_1`
   assume `τ ≠ s`. For `D = 0` the treasure is at the source and is found at time `0` (degenerate, R2); our
   phase-based time bound does not model the immediate find at `s`. Thm 5.1 additionally takes `ε < 1`
   (for `ε ≥ 1` the claim is trivial); its proof needs only `D ≥ 1`, not the paper's implicit `D ≥ 2`.
7. **Integer lengths.** Spiral lengths and radii are rounded down: `⌊4^{i+1}/k⌋` (App. A, where the paper has
   `2^{2i+2}/k`), `⌊D_{i,j}⌋`, `⌊t_{i,j}⌋`, `⌊d(u)^{2+δ}⌋`. App. A indexes stages and phases from `1`; we use `0`.
8. **Footnote 2** is stated as: some `τ` with `d(τ) ≤ D` has `T ≥ (D + D²/k)/20` (any `k ≥ 1` agents, not
   necessarily identical). This is what the footnote's proof shows: it finds a node of `B_D`. For a fixed *exact*
   distance `D` the `D²/k` part is false in general: agents can go to distance `D` and walk around the sphere in
   time `O(D)`. Competitiveness quantifies over all `D`, so this is harmless.

## Statement-level differences

9. **Thm 3.3 / Algorithm 1: `j^{1+ε}` at `j = 0`.** The algorithm divides by `0^{1+ε} = 0` in every phase
   `j = 0`, and for `k = 1` the proof uses exactly that phase. We use `(j+1)^{1+ε}`.
   Rule: **R3** (typo with evident intent, local fix) → ⚠️.
10. **Thm 3.3: `O(log^{1+ε} k)` at `k = 1`.** Read literally, the bound is `0` at `k = 1`. We prove
    `T ≤ C·(1 + log₂ k)^{1+ε}·(D + D²/k)` for all `k ≥ 1`, `D ≥ 1`. Rule: **R2** (degenerate) → ⚠️ at most.
11. **Algorithm 2 (Thm 5.1): `p(s) = c/0`.** The distribution is undefined at the source; we set `p(s) = 0`
    (`hWeight`, `harmonicPMF`). Rule: **R3** → ⚠️.
12. **Thm 5.1's wording.** "With probability at least `1 − ε`, the expected running time is `O(…)`" is
    meaningless as written. The proof's first paragraph states the intended claim, which we prove: with
    probability `≥ 1 − ε` the running time is at most `C(D + D^{2+δ}/k)` (`theorem_5_1`). Rule: **R3** → ⚠️.
13. **Thm 5.1: `δ ∈ (0, 0.8]`.** The proof uses `δ ≤ 0.8` only for `(5/4)^{2+δ} ≤ 2`. We prove the theorem for
    every `δ > 0`, which is more general.
14. **Thm 4.1** is stated as `¬ φ =O[atTop] log` for any `φ` for which the uniform algorithm is
    `φ`-competitive. We also prove the stronger intermediate claim `∑ᵢ 1/φ(2ⁱ) ≤ 320` for every `φ`.
15. **Thm 4.2** is stated as `(k ↦ ε(k) log k) =O[atTop] φ`, plus the explicit bound
    `φ(k) ≥ ε(k) ln k / (64 ln 4)` for all `k ≥ 1`. Hypotheses as in the paper: `0 < ε ≤ 1`, `φ` non-decreasing.
16. **Thm 3.1 / Cor 3.2.** As stated, with explicit `C` depending only on `σ` (resp. `σ, ρ`). The estimates
    `k_a` in Cor 3.2 may be real numbers. A general form for heterogeneous parameters `κ_a ∈ [k/λ, k]` is
    `akTime_le`.

## Proof-level differences

17. **Thm 4.1: shells need not be nested (proof gap).** "`|Sᵢ|/kᵢ = Ω(T/φ(kᵢ))` … follows from
    `φ(kᵢ) = O(i)`" needs `Dᵢ > Dᵢ₋₁`, i.e. `φ(2ⁱ) < 2φ(2ⁱ⁻¹)`, quantitatively. This does not follow from
    `φ = O(log k)`. Repair: running maxima of the radii plus Abel summation (`abel_shell`). The claim is now proved
    for arbitrary `φ`. Rule: **R1** (wrong step inside a proof of a true theorem) → 🛠️.
18. **Thm 4.1: the source.** The node `s` (distance `0`) is excluded from competitiveness (item 3). In the
    counting it gets the trivial weight `1`.
19. **Thm 4.2: empty range of `i`.** If `ε(k̃) log k̃ < 2`, the set of `i` with `k̃^{1−ε} ≤ 4ⁱ ≤ k̃` may be empty.
    Then `Ω(ε log k)` needs `φ = Ω(1)`, which the proof does not mention. We prove `φ(k) ≥ 1/32` with the same
    shell argument for `k = k̃` (`one_div_le_of_competitive`). Our shells are shifted by one index
    (`2^{j₀+i} < d ≤ 2^{j₀+i+1}`), and `W = 4^{j₀}` with `j₀ ≥ log₄ k̃`, which is implicit in the paper. Rule: R1 → 🛠️
    (minor).
20. **Thm 5.1: constants.** `α = 12β/c` gives `λ < D/3`, not `λ < D/4`, so `√(λD) < D/2` and
    `3D/4 < d(u) < 5D/4` do not follow. "At least `λD/2` nodes in `B_λ`" is false for small radii (radius `1.9`:
    5 nodes vs `7.2`). We use the radius `r = ⌊√(γ D^{2+δ}/k)⌋`, `|B(τ,r)| ≥ (r+1)(r+2)/2`, `α = 16σγ`,
    `γ = 2·(5/4)^{2+δ}·Z·ln(1/ε)` with `Z = 1/c`, and `C = 2 + σγ`. Rule: R1 → 🛠️.
21. **Thm 3.3: "at least half of the ball … is contained in `B(D_{i,j})`"** is imprecise. The fraction can be
    `< 1/2`, and the radius should be `√t/2` under the paper's spiral convention. We prove a constant fraction
    (`card_near_ge`: `≥ (r/2+1)(r/2+2)/2` nodes of `B(R) ∩ B(τ, r)` when `d(τ) ≤ R`, `r ≤ R`). The success
    probability is then `≥ min(1/32, Y/(72σX))` (`uniformBall_succ_ge'`). Routine.
22. **Thm 3.3: reduction `k > D` → `D` agents.** We do not reduce. The good phase index is
    `j* = ⌊log₂ min(k, D)⌋`, which handles both cases at once. The stage threshold `s` satisfies
    `2^s ≥ D²(j*+1)^{1+ε}/2^{j*}` and `s ≥ j*`. Equivalent to the paper.
23. **Thm 3.1: success probability.** For `i ≥ ⌈log₂ D⌉` we prove `≥ 1/(18(σ+1)k)` per agent and phase
    (`ak_succ_ge`). This covers also the case `4^{i+1} < k` (spiral length `0`, only `u = τ` succeeds), which the
    paper's "`Ω(|B(τ, √tᵢ/2)|/|Bᵢ|)`" glosses over. Routine.
24. **Sums of tails.** The paper's `O(∑_ℓ 2^{s+ℓ}/γ^{ℓ²/2}) = O(2^s)` is proved in the form
    `∑_b (A 2^b + B 4^b) e^{−β m(m+1)/2} ≤ (A 2^s + B 4^s)(1 + ∑_ℓ 4^ℓ e^{−βℓ(ℓ+1)/2})` (`tsum_le_of_gauss`).

## Borderline calls

* Items 9, 11, 12 are scored ⚠️ (R3), not 🛠️. Algorithms and theorem statements are statements (R1), and as
  written they are undefined or meaningless. The intended versions are evident from the paper's prose and
  proofs, and the fixes are local. No checked statement is false under its evident reading, so the verdict is
  not ❌.
