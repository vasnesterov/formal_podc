# Differences between the formalization and the paper

Paper: Ben-Basat, Even, Kawarabayashi, Schwartzman, *Optimal Distributed Covering Algorithms*,
PODC 2019, arXiv 1902.09377v2.

## Model and definitions

1. **Global-state iteration instead of messages.** One iteration (steps 3a–3f) is the function `step`.
   The messages ("covered", "raise"/"stuck", deals) are replaced by reading the corresponding values.
   Every step only uses information of the vertices of an edge or of the edges of a vertex, so this is
   the paper's synchronous execution. CONGEST message sizes (Appendix B) are not modelled.
2. **Hypergraph representation.** `inc : E → Finset V` with an arbitrary finite edge type, so parallel
   edges are allowed (the set-cover reading `e_x = {u_i : x ∈ U_i}` produces them). Edges must be
   nonempty: the paper implicitly assumes this, since `min_{v ∈ e}` in iteration 0 needs it.
3. **Weights.** Positive reals instead of `ℕ⁺`. Assumptions (i)–(iii) of Section 3.1 (polynomial
   weights/degrees, `Δ ≥ 3`) are only needed for CONGEST and asymptotics. They are not assumed,
   except `Δ ≥ 3` in `theorem_4_9`.
4. **`f` and `Δ` are bounds, not exact values.** Every theorem takes `f` with `rank ≤ f` and `f ≥ 1`
   (the parameter `P.f` used in `β`), and `Δ` with `deg ≤ Δ`. This is more general.
5. **Parameters.** `ε > 0` (the paper: `ε ∈ (0,1]`; Claim A.1: `ε ∈ (0,1)`) and `α > 1` (the paper:
   `α ≥ 2`). `α ≥ 2` is used only in `iterBound_le` / `mwhvc_main` to bound `log_α 2 ≤ 1`.
6. **One proof for Section 3 and Appendix C.** The dual increment is `δ(e) += κ·deal(e)`, with
   `κ = 1` for Section 3 and `κ = 1/2` for Appendix C. All invariants are proved for every
   `κ ∈ (0,1]`. The initial deal is `c₀ · min_{v∈e} w(v)/|E(v)|` with `c₀ ∈ (0,1/2]`. Section 3 uses
   `c₀ = 1/2`, Appendix B uses `c₀ = β` (an inconsistency in the paper; both are covered).
   Lemma 4.6 is stated for `c₀ = 1/2` as in the paper (`lemma_4_6`) and in general with the bound
   `log_α(Δ·2^{fz}/(2c₀))` (`lemma_4_6_general`).
7. **Step 3a** lets every `v ∉ C` join, as written. A vertex that has already terminated with
   `E'(v) = ∅` can never become `β`-tight later, so this agrees with "terminated vertices do
   nothing".
8. **Step 3d (`while` loop)** is `lvlUp`: the least `ℓ' ≥ ℓ` with `∑_{E(v)} δ ≤ w(1 − 2^{-(ℓ'+1)})`.
   If no such level exists the level is unchanged. This never happens for active vertices
   (`lvlUp_upper`), because they are not `β`-tight. The `k` halvings of a deal (one per level
   increment of a vertex of the edge) are applied as a single factor `2^{-k}`.
9. **Covered edges.** Covered edges are terminated: their `δ` and `deal` are frozen. This matches the
   paper's convention "`δ_i(e) = δ_{j-1}(e)`".
10. **Termination** is "every edge is covered" (`Terminated`). Then every vertex has terminated as
    well (`v ∈ C`, or `E'(v) = ∅`).
11. **`opt`.** Corollary 4.3 and Claim A.1 are proved against every fractional vertex cover `x`, i.e.
    `w(C) ≤ (f+ε)·∑ w x`. This avoids talking about the existence of an LP optimum and implies the
    paper's statement and the bound against every integral cover (`corollary_4_3_integral`).
12. **Definition 4.5.** `RaiseIter e i` and `StuckIter v i` refer to iteration `i ≥ 1`. A `v`-stuck
    iteration requires `v` to be active in iteration `i`, i.e. to send a message.

## Statements

13. **Claim 4.2, Eq. (1)** is proved for vertices *active* in iteration `i` (`claim_4_2`). The paper
    states it for every `v ∉ C`, which is false for vertices that terminated without joining `C`
    (`Eq1.claim_4_2_eq1_false`). The proof only needs active vertices. Feasibility (`IsPacking`) is
    proved for all iterations `i ≥ 0` (the paper: `δ_{i-1}` for `i ≥ 1`, the same thing).
14. **Lemma 4.7 / Lemma C.2** are proved in the corrected form `#stuck(v, ℓ) < α/κ + 1`, i.e.
    `≤ ⌈α/κ⌉` (`lemma_4_7`, `lemma_4_7_ceil`). The paper's `≤ α` (`≤ 2α`) holds for integral `α`
    (`lemma_4_7_of_nat`, `lemma_C_2_of_nat`) and fails otherwise (`Stuck.lemma_4_7_false`,
    `α = 29/10`, three stuck iterations). The count is over iterations `1..n` for every `n`.
15. **Lemma 4.6** is stated as a bound on the number of `e`-raise iterations among `1..n`, for every
    `n`, in real numbers (`≤ log_α(Δ·2^{fz})`). The proof is the paper's. Additionally the deal is
    tracked exactly: `deal_n(e) = deal_0(e)·α^{#raises}·2^{-∑_{v∈e} ℓ_n(v)}` (`deal_formula`).
16. **Theorem 4.8.** Explicit bound: every edge is covered by the end of iteration
    `⌊log_α(Δ·2^{fz}/(2c₀))⌋ + f·z·⌈α/κ⌉ + 1` (`theorem_4_8`). For `c₀ = 1/2`, `α ≥ 2`, this is
    `≤ log_α Δ + f z (α/κ + 2) + 1` (`iterBound_le`). Also `z ≤ log₂((f+ε)/ε) + 1` (`z_le`). The
    proof's "number of e-stuck iterations" is a typo for "e-raise".
17. **Theorem 4.9.** Asymptotic statements are made explicit: for every `γ > 0` there is an explicit
    constant `C49 γ` such that, for every instance with `Δ ≥ 3`,
    `T ≤ C49 γ · (F + log Δ/log log Δ + min{log Δ, F·(log Δ)^γ})` with `F = f·z`. Logarithms are
    natural, `L = log Δ`. `F = f·z` replaces the paper's `f·log(f/ε)`, which is `0` for
    `f = ε = 1` (division by zero in the definition of `α`). `F = Θ(f log(f/ε))` for `f/ε ≥ 2`. The
    case analysis is the paper's, including the case `L^{γ/2} ≤ x < 2` where `Δ` is bounded.
18. **Corollaries 4.10–4.12** are not formalized as round bounds. Corollary 4.10's approximation
    claim with `ε = 1/(nW)` is refuted (`Cor410.corollary_4_10_false`). The run is certified for
    `α = 2`. No vertex ever sends "raise" there, so the run is the same for every `α > 1`. The
    instance uses three parallel edges (to have `Δ = 3`); the refutation follows the definition
    `W = max w / min w` given just before Corollary 4.10, not the introduction's `w : V → {1,…,W}`.

## Section 5

19. **Covering ILPs** are indexed by finite row/column types. "Optimal value" statements are replaced
    by cost-preserving maps between feasible solutions in both directions (`claim_5_6`). This is
    equivalent and avoids existence of optima.
20. **Lemma 5.2.** The hyperedge set is the paper's: `{σᵢ \ S | i, S ⊆ [n], Aᵢ·I_S < bᵢ}` as a
    `Finset` (duplicates merged). Proved: covers ↔ feasible zero-one solutions (needs `A ≥ 0`),
    nonempty edges (needs feasibility), rank `≤ f(A)`, degree `≤ 2^{f(A)-1}·Δ(A) < 2^{f(A)}·Δ(A)` (the
    strict form needs `f(A), Δ(A) ≥ 1`). The stated rank `< f(A)` is refuted
    (`lemma_5_2_rank_false`).
21. **Definition 5.4** is the predicate `IsM A b M` ("`M` is the maximum of `bᵢ/Aᵢⱼ` over nonzero
    entries"). The repaired results only use `bᵢ ≤ Aᵢⱼ·M` for nonzero entries.
22. **Proposition 5.5** is false for non-integral `M` (`prop_5_5_false`). It is proved with the box
    `[0, ⌈M⌉]ⁿ` (`prop_5_5_ceil`).
23. **Claim 5.6.** The statement is false for `M < 1` (`claim_5_6_false`), and the proof's
    `B = ⌈log₂ M⌉` bits are too few (`claim_5_6_proof_false`). Proved: for any `B` with
    `⌈M⌉ < 2^B` the binary expansion solves the ILP (`claim_5_6`). `B = ⌈log₂ M + 1⌉` satisfies this
    for `M ≥ 1` (`claim_5_6_bits`). `f(A') = f(A)·B` and `Δ(A') = Δ(A)` (`fA_binExp`, `ΔA_binExp`).
24. **Claim 5.3** (distributed simulation over `N(ILP)`) and the running-time part of Claim 5.7 are
    not formalized. The approximation claim of Claim 5.7 with `f = f(A)` is refuted
    (`ILPCex.claim_5_7_false`). The true ratio of the reduction is `f(A)·B + ε`, which follows from
    Corollary 4.3 and `fA_binExp`. The degree parameter `2^{f(A)}·M·Δ(A)` of Claim 5.7 is refuted
    (`Degree57.claim_5_7_degree_false`).

## Not formalized

25. Appendix B (CONGEST encoding), the local-`Δ(e)` variant of `α`, Corollaries 4.10–4.12 as round
    bounds, the final asymptotic simplification of Section 5.
