# Collaborative Search on the Plane without Communication — PODC 2012

Ofer Feinerman, Amos Korman, Zvi Lotker, Jean-Sébastien Sereni. *Collaborative Search on the Plane without
Communication.* PODC 2012. DOI [10.1145/2332432.2332444](https://doi.org/10.1145/2332432.2332444).
Formalized version: arXiv [1205.2170](https://arxiv.org/abs/1205.2170) v2 (Jan 2017); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** Every result of the paper holds: the upper bounds `O(D + D²/k)` (Thm 3.1, Cor 3.2) and
`O(log^{1+ε} k)` (Thm 3.3), both lower bounds (Thm 4.1: no uniform `O(log k)`-competitive algorithm; Thm 4.2:
`Ω(ε(k) log k)` with `k^ε`-advice), the harmonic algorithm (Thm 5.1) and footnote 2's `Ω(D + D²/k)`. The wrong steps in
the proofs of Thm 3.3, Thm 4.1 and Thm 5.1 are closed by local patches and changed constants, and everything else is a
slip.

## Mistakes in the paper

### ✏️ Slips
- **Algorithm 1 and Thm 3.3 (phase `j = 0`, `k = 1`).** Algorithm 1 is undefined in every phase `j = 0`, which uses
  `D_{i,0} = √(2^i/0^{1+ε})` and `t_{i,0} = 2^{i+2}/0^{1+ε}`, and for `k = 1` the proof uses exactly this phase. Also,
  "`O(log^{1+ε} k)`-competitive" literally means a bound `0` for `k = 1`. We use `(j+1)^{1+ε}` and prove Thm 3.3 as
  `C (1 + log₂ k)^{1+ε} (D + D²/k)` (`theorem_3_3`); the `1 +` handles `k = 1`.
- **Algorithm 2 (Thm 5.1, distribution at the source).** `p(u) = c/d(u)^{2+δ}` is infinite at the source `s`. We set
  `p(s) = 0` (`harmonicPMF`).
- **Thm 5.1 (wording).** "With probability at least `1 − ε`, the *expected* running time is `O(…)`" is meaningless as
  written. The proof shows the intended claim, that with probability `≥ 1 − ε` the running time is
  `O(D + D^{2+δ}/k)`, and this is what we prove (`theorem_5_1`).
- **Footnote 2.** The bound `Ω(D + D²/k)` is stated for the distance `D`, but the footnote's argument finds a treasure
  at distance at most `D`, which is what we prove (`footnote_2`); see below.
- **Thm 4.2 (empty range).** The proof bounds `φ(k̃)` by the number of admissible `i` in
  `[⌈(1−ε)/2 · log k̃⌉, ⌊½ log k̃⌋]`. This range may be empty when `ε(k̃) log k̃ < 2`. Then `Ω(ε log k)` needs the
  trivial bound `φ = Ω(1)` (footnote 2). We add it (`one_div_le_of_competitive`).

## Proof gaps (statements true)

### 🔧 Thm 4.1 (the shells need not be nested)
The proof's claim `|Sᵢ|/kᵢ = Ω(T/φ(kᵢ))` "since `φ(kᵢ) = O(i)`" needs `Dᵢ > Dᵢ₋₁`, i.e.
`φ(2ⁱ) < 2φ(2ⁱ⁻¹)`, which does not follow from `φ(k) = O(log k)`.

**Impact.** The theorem stands, and the paper's intermediate claim is proved for *every* `φ`
(`theorem_4_1`, `sum_inv_le_of_isCompetitive`).

**Details.** The proof takes `kᵢ = 2ⁱ`, `Dᵢ = √(T kᵢ/φ(kᵢ))` and the shells
`Sᵢ = B(Dᵢ) \ B(Dᵢ₋₁)`. Even `Dᵢ > Dᵢ₋₁` is not enough; it needs a quantitative version of it. An
`O(log k)` function may jump by a factor 4 at some `i`, and then `Sᵢ = ∅`. (For `O(log k)` alone, the
paper's proof can also be saved by running it with `φ` replaced by its bound `c·log k`, for which the
radii do increase.)

**Repair.** Replace the radii by their running maxima `R'ᵢ = max_{j≤i} Rⱼ`. A node within distance
`Rⱼ`, `j ≤ i`, is still visited with probability `≥ 1/(2·2ⁱ)`. The shells are then combined by Abel
summation. This proves the paper's intermediate claim for *every* `φ`: if a uniform algorithm is
`φ`-competitive, then `∑ᵢ 1/φ(2ⁱ) ≤ 320` (`sum_inv_le_of_isCompetitive`,
`summable_inv_of_isCompetitive`). Thm 4.1 follows (`theorem_4_1`). The bound also excludes, e.g.,
`φ = O(log k · log log k)`, since `∑ 1/(i log i)` diverges (this remark is not formalized).

### 🔧 Thm 5.1 (constants in the proof)
With `α = 12β/c` and `λ = 4βD^{1+δ}/(ck)`, the hypothesis `k > αD^δ` gives only `λ < D/3`, not the
claimed `λ < D/4`, so "`√(λD) < D/2`, hence `3D/4 < d(u) < 5D/4`" does not follow.

**Impact.** The theorem stands; both errors only change constants (`theorem_5_1`).

**Details.** Also, "there are at least `λD/2` nodes in `B_λ`" is false for small radii. For example,
radius `√(λD)/2 = 1.9` gives `λD/2 ≈ 7.2`, but the ball has 5 nodes.

**Repair.** We prove the theorem with `α = 16σγ`, `γ = 2·(5/4)^{2+δ}·ln(1/ε)/c` (`theorem_5_1`). The
restriction `δ ≤ 0.8` is not needed.

### 🔧 Thm 3.3 ("half of the ball")
The proof says "at least half of the ball of radius `√t_{i,j}` around the treasure is contained in `B(D_{i,j})`", but
the fraction can be less than `1/2`.

**Impact.** The theorem stands: a constant fraction suffices (`card_near_ge`).

**Details.** The proof also uses radius `√t` where its own spiral convention gives `√t/2`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Grid `ℤ²`, source `s = (0,0)`, `d` = hop (ℓ₁) distance. The search is synchronous: one node per time unit, and
  all agents start together. The treasure `τ` is chosen adversarially; we quantify over all `τ`. Agents are
  probabilistic and identical, and they do not communicate.
* *Lower bounds (§4, footnote 2).* An agent is a probability law on trajectories `ℕ → ℤ²`. The `k` agents are
  independent (`Measure.pi`). The running time is the first time some agent is at `τ`; `T(D,k)` is its
  expectation (`expectedTime`). A trajectory up to the find time cannot depend on `τ`, so a `τ`-independent law
  is no restriction.
  *Uniform* means one law for every `k`. With *advice*, agent `a` uses the law `A k̃ₐ` of its own estimate.
  `φ`-competitive means `T ≤ φ(k)(D + D²/k)` for all `k ≥ 1` and all `τ ≠ s`.
  The lower bounds do **not** assume grid walks: an agent may move arbitrarily (one node per time unit), which
  makes them stronger. Footnote 2's `Ω(D)` part assumes walks from the source (`IsWalk`).
* *Upper bounds (§3, §5).* We use the paper's atomic navigation procedures (§2, footnote 1). Walking to `u`
  takes `d(u)` steps, returning from the end of a spiral of length `t` takes `≤ d(u) + t` steps, and a spiral of
  length `t` from `u` visits every `v` with `σ·d(u,v)² ≤ t`. The paper's convention is `σ = 4`; we keep any
  `σ ≥ 1` as a parameter. A phase "uniform `u ∈ B(R)`, spiral `t`, return" thus lasts `≤ 2R + 2t`. An agent
  whose `u` satisfies the spiral condition has found `τ` by the end of the phase.
  All random choices of all agents in all phases are independent (`Measure.infinitePi`). The running time
  bound is `∑_b dur(b) · 1[not found before block b]`, where block `b` is a stage or big stage and `dur(b)`
  bounds every agent's block duration (`phasedTime`). Its expectation is computed exactly
  (`lintegral_timeBound`). For the harmonic algorithm, the time of an agent that picked `u` is
  `d(u) + σ d(u,τ)²` when the spiral reaches `τ` (`harmonicBound`).
  The navigation procedures themselves are not constructed in Lean, matching the paper's abstraction.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 3.1 | `theorem_3_1` (general: `akTime_le`) | `Theorem31.lean` |
| Cor 3.2 | `corollary_3_2` | `Theorem31.lean` |
| Thm 3.3 | `theorem_3_3` | `Theorem33.lean` |
| Thm 4.1 | `theorem_4_1` | `Theorem41.lean` |
| Thm 4.1, "`∑ 1/φ(2ⁱ)` converges" | `summable_inv_of_isCompetitive`, `sum_inv_le_of_isCompetitive` | `Theorem41.lean` |
| Thm 4.2 | `theorem_4_2` (`=O` form), `theorem_4_2_explicit` (`φ(k) ≥ ε(k) log k/(64 log 4)`) | `Theorem42.lean` |
| Thm 5.1 | `theorem_5_1` | `Theorem51.lean` |
| §2, footnote 2: `T = Ω(D + D²/k)` | `footnote_2` (counting part `sq_div_le`) | `Footnote.lean` |
| Markov + one-node-per-step counting | `half_le_sum_visit`, `sum_visit_le` | `Basic.lean` |

Footnote 2 bounds the worst case over treasures at distance *at most* `D`. For a fixed exact distance the
`D²/k` bound is false in general, but competitiveness quantifies over all `D`, so this is harmless.

**Not formalized.** The construction of the navigation primitives (walks, spirals) for the upper bounds. The
memory remarks of §6 and the biological discussion.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity of the competitiveness hypotheses of Thm 4.1/4.2: a deterministic agent enumerating `ℤ²` via
`Nat.pair` is `9k`-competitive, with or without advice (`isCompetitive_enum`, `isCompetitiveAdvice_enum`,
`NonVacuity.lean`). It teleports, which the lower-bound model allows. (For grid walks, the algorithms of §3 show non-vacuity on
paper; our `theorem_3_3` is stated in the phase model, not as a trajectory law, so this link is not formal.)
Everything is built from Mathlib (product measures `Measure.pi`, `Measure.infinitePi`, `PMF`). CSLib candidates
(`-- CSLib candidate`): `sum_visit_le`, `half_le_sum_visit` (`Basic.lean`), `lintegral_timeBound`
(`Phases.lean`), `tsum_le_of_gauss`, `prod_le_gauss` (`Summation.lean`).
