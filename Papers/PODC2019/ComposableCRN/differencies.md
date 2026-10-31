# Differences between the formalization and the paper

Paper: E. E. Severson, D. Haley, D. Doty, *Composable computation in discrete chemical reaction
networks*, PODC 2019 (arXiv:1903.02637v2, the version formalized; numbering follows it).

## Errors in the paper

None found in the formalized part. All checked statements hold as written (see the README table).
The only imprecisions are listed below; none of them changes a statement.

## Model and definitions

1. **Inputs indexed by a finite type.** `ℕ^d` is `ι → ℕ` for any finite `ι` (`Fin d` in the paper).
   This is a harmless generalization.
2. **Species distinctness.** The paper names input species `X₁, …, X_d`, an output `Y` and a leader
   `L` without saying they are distinct. `FunCRN` requires `X` injective, `Y ≠ Xᵢ`, `L ≠ Xᵢ`,
   `L ≠ Y` (standard reading). The impossibility results (`Impossibility.lean`) never use these
   fields, so they hold even without distinctness.
3. **Leader as an option.** `FunCRN.L : Option S`; `ObliviouslyComputable` requires a leader (the
   paper's model, §2.2), `LeaderlessObliviouslyComputable` requires none (§9). `StablyComputable`
   (only used to state the cited Lemma 2.7 as a hypothesis) allows both. The class is the same
   either way (the semilinear functions, [10, 17]), so the hypothesis remains a true theorem.
4. **Semilinear functions.** We define "`f` semilinear" as "the graph of `f` is a semilinear set"
   with Mathlib's `IsSemilinearSet` (finite union of linear sets `a + ⟨t⟩`). The paper says this is
   the concise definition and then works with Definition 2.6 (a disjoint union of affine partial
   functions on Boolean combinations of threshold and mod sets, Definition 2.5). The definitions are
   equivalent by classical results (Ginsburg–Spanier; [10, Lemma 4.3]); Mathlib proves
   semilinear = Presburger-definable (`definable_iff_isSemilinearSet`). Our proof of Theorem 3.1
   "⇐" uses the linear-set form directly, so it does not depend on the equivalence.
5. **Quilt-affine (Definition 5.1)** is formalized literally: nondecreasing `g : ℕ^ι → ℤ` with
   `g x = ∇g · x + B(x mod p)`, `p > 0`, `∇g ∈ ℚ^ι_{≥0}`, `B : (ℤ/pℤ)^ι → ℚ`.
6. **Condition (ii) of Theorem 5.2** (`EventuallyMin`) uses `m + 1` functions `g₀, …, g_m`, i.e.
   at least one; "the minimum of zero functions" is meaningless in the paper as well.
7. **Fixed-input restriction** `f[x(i)→j]` is `fixInput f i j x = f (Function.update x i j)`, with
   domain `ℕ^d` as in the paper's footnote 11.

## Statements

8. **Lemma 2.7** ([10], cited) is not proved; its "⇒" half (stably computable ⇒ semilinear) is the
   hypothesis `StablyComputableImpliesSemilinear` of `theorem_3_1` (and of `theorem_9_2`).
   The "⇐" directions of Theorems 3.1 and 9.2 need no hypothesis.
9. **Theorem 7.1** (necessity of condition (ii); §7, recession cones and a hyperplane-arrangement
   argument in `ℝ^d`) is not formalized. `theorem_5_2` takes it as the hypothesis `Theorem71`; the
   "⇐" direction (`lemma_6_2`) and the parts (i), (iii) of "⇒" (Observations 2.1, 5.3) are proved
   unconditionally.
10. **Lemma 4.1.** The paper asks the sequence `(aᵢ)` to be increasing; the proof never uses it, and
    `not_obliviouslyComputable_of_seq` drops the assumption (stronger statement). Differences are
    taken in `ℤ`, as in the paper.
11. **Observation 2.2 (composition).** The paper composes by *renaming* `C_f`'s output to `C_g`'s
    input, plus a reaction `L → L_f + L_g`, for one upstream module `g : ℕ → ℕ`, and remarks that
    any number of upstream modules works. We prove the general remark
    (`ObliviouslyComputable.comp`, `StablyComputable.comp_oblivious`: `κ` upstream modules, fan-out
    reactions `X_i → Σ_k X^{(k)}_i`, one leader split `L → Σ_k L_k + L_g`). Instead of renaming we
    use a *transfer* reaction `Y^{(k)} → X^{(g)}_k`; this only delays the hand-over. The semantic
    content used by Lemma 6.2 (closure under composition) is the same; the renaming construction
    itself is not formalized. As in the paper, the downstream CRN need not be output-oblivious.
12. **Observation 5.3** is derived from composition (`f` composed with the constant `j` and the
    projections) instead of the paper's direct "hard-coding" CRN `L → j X_i' + L'`. Same statement.
13. **Lemma 6.2.** Same identity (1) and the same pieces. Two harmless changes: `n ∈ ℕ^d` is
    replaced by the scalar `N = maxᵢ nᵢ` (the paper's own "without loss of generality"). The module
    for `(x − n)⁺` is our leader-automaton CRN rather than `(n+1)Xᵢ → nXᵢ + Yᵢ` (same function).
    The other gadgets are the paper's CRNs literally: `X₁ + … + X_k → Y` for `min` and
    `A → Y`, `(j+1)W + B → (j+1)W + Y` for `c(a, b, w)`.
14. **Theorem 3.1 / Lemma 6.1 constructions.** Both are instances of one generic leader-automaton
    construction (`obliviouslyComputable_of_automaton`), proved correct once. For Theorem 3.1 the
    leader states are `0, …, N+P−1` with `x ↦ x` below `N + P` and `x ↦ N + (x − N) mod P` above.
    These are the paper's `L_0, …, L_{n−1}, P_0, …, P_{p−1}` up to renaming (the paper's `P` states
    start at `n mod p`; `pdftotext` drops the overbars `P_{\bar n}`, `\bar a` that mean "mod p").
15. **Proof of Theorem 3.1 "⇐".** The paper's argument (threshold/mod decomposition, "the
    periodically repeated affine pieces must have the same slope since f is nondecreasing") is
    replaced by an argument on linear sets: every linear set `a + ⟨t⟩` inside the graph with a
    period `u = (u₁, u₂)`, `u₁ > 0`, gives `f(x + P) − f(x) = (P/u₁)·u₂` on its projection, which
    is closed under `+P`. Hence `f(x+2P) + f(x) = 2f(x+P)` beyond a threshold. Monotonicity then
    makes `f(x + P) − f(x)` constant (`eventually_affine_of_semilinear_of_monotone`), the same
    "same slope" step as in the paper. No gap in the paper; just a different route.

16. **Theorem 9.2 construction.** We use the paper's leaderless CRN without the leader-automaton
    reactions it inherits from Theorem 3.1 (the paper itself notes they are unnecessary): `X → f(1)Y +
    T_{red 1}` and merge reactions `T_a + T_b → (f(a+b) − f(a) − f(b))Y + T_{red(a+b)}`. Tokens
    are labelled by the same reduction `red` as in Theorem 3.1, so the paper's WLOG `p | n` is not
    needed. The correctness invariant tracks a multiset of consumed input blocks.

## Not formalized

17. Lemma 2.3 (composable ⇒ output-oblivious; splicing argument) and Observation 2.4
    (output-monotonic = output-oblivious); Theorem 5.4; all of §7 (Theorem 7.1, Lemmas 7.3–7.20);
    §8 (Theorem 8.2, scaling limits); footnote 2 (equivalence of the "reachable stable
    configuration" definition with fair-execution and probability-1 semantics). We read the proofs
    of Lemma 2.3 and Observation 2.4 and found them sound (Lemma 2.3: the splicing terminates
    because each splice moves at least one `W` to the never-consumed `Y`, whose count is bounded by
    `f(x)`).

## Verdict notes

18. **Verdict ✅ (R6, checked statements only).** The checked statements are Observations 2.1, 2.2
    (in the generalized closure form), 5.3, 9.1, Lemmas 4.1, 6.1, 6.2, the `⇐` directions of Theorems
    3.1, 5.2, 9.2, and the `⇒` directions of 3.1/9.2 modulo the cited Lemma 2.7. The headline
    Theorem 5.2 is only half checked: the necessity of condition (ii) (Theorem 7.1, §7) is a
    hypothesis, so nothing is claimed about it. Borderline point considered: Lemma 6.2 uses the
    multi-input form of Observation 2.2, which the paper only asserts in a remark ("more
    generally, …") without proof. The extension is routine (fan-out plus the same additivity
    argument), so we count it as a routine detail rather than a proof repair.
19. **Hypotheses are the paper's own claims in the paper's model.** `StablyComputableImpliesSemilinear`
    and `Theorem71` are stated for our `FunCRN`, which, like the paper (`(R, P) ∈ ℕ^S × ℕ^S`), allows
    any reactions, including ones with no reactants. They are the paper's Lemma 2.7 ([10]) and
    Theorem 7.1 for exactly the paper's model, so they are not vacuous by a modelling artefact.
