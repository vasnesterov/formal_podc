# Differences between the formalization and the paper

Paper: Jérôme Leroux, *State Complexity of Protocols With Leaders*, PODC 2022, arXiv 2109.15171 **v2** (the version
formalized; numbering follows it).

## Model and definitions

1. Configurations are functions `P → ℕ` (the paper's `ℕ^P`). For `Q ⊆ P`, the paper's `Q`-configurations are the
   `P`-configurations vanishing outside `Q`: `res Q ρ` is `ρ|_Q`, `Trans.res Q t` is `t|_Q`, `resNet Q T` is `T|_Q`.
   The paper allows `Q ⊄ P`, which is never used. Components and their cardinals are the same under this
   identification.
2. `Protocol` stores the additive preorder `R` (`→*`) with reflexivity, transitivity and additivity as fields.
   Initial states are a `Finset I`. `ℕ^I` is represented by the `P`-configurations vanishing outside `I`
   (`Protocol.IsInput`), so `ρ|_P = ρ`. Predicates are `Config P → Bool`. `S₀`, `S₁`, `γ(ρ)` and "stably computes"
   are transcribed literally, including `ρ = 0` as an input.
3. `StablyComputesGe i n` means `I = {i}` and the protocol stably computes `φ_{i≥n}`. The paper requires `n > 0`; our
   Theorem 4.3 does not need it (for `n = 0` the bound is trivial).
4. Interaction-width: `HasWidthLE R m` means that every pair of `R` is realised by a word of transitions of `R` of
   width `≤ m`. `width R : ℕ∞` is the infimum, i.e. the paper's `width`, with `ω = ⊤`. Theorem 4.3 is stated for any
   `m` with `HasWidthLE R m` (`theorem_4_3`, slightly stronger) and for `width R ≠ ⊤` (`theorem_4_3'`).
5. Section 3's net `{t ∈ R | |t| ≤ width(R)}` is `widthNet R m`, a `Finset`, because all its transitions lie in a
   finite box. `Protocol.reach_iff` is the claim "R is the reachability relation of this net". `hasWidthLE_reach` is
   "the reachability relation of `T` has width `≤ max |t|`". We do not formalize that the class of finite-width
   additive preorders *equals* the class of Petri-net reachability relations beyond these two directions.
6. Lemma 5.2 is proved in a per-place form (`run_lift`): the requirement `α(p) ≥ |σ|·‖T‖∞` is replaced by
   `α(p) ≥ |σ|·M(p)`, where `M(p)` bounds what the transitions of `σ` consume from `p`. The paper's statement is
   `lemma_5_2`. The per-place form is needed for nets that never touch some places (see 8).
7. Lemma 5.3 (Rackoff) is proved, not assumed. We prove Rackoff's recursive bound
   (`Podc/Computability/PetriNets/Rackoff.lean`) and show it is `< (‖ρ‖∞+‖T‖∞)^(k^k)` when both norms are `≥ 1`
   (`rackoffBound_lt`). The degenerate cases `‖T‖∞ = 0` and `‖ρ‖∞ = 0` are handled directly; there the covering word
   is empty.

## Section 6

8. Lemma 6.2 and Theorem 6.1 are proved relative to a set `U` of active places (`NetOn U T`, `ρ` vanishing outside
   `U`, `d = |U \ Q|` resp. `d = |U|`, `Q ⊆ U`). The paper's Theorem 6.1 is the case `U = P` (`theorem_6_1`). Section 8
   applies Theorem 6.1 to `T|_{P'}` with `P' = P \ {i}`, which is the relative form with `U = P'`.
9. **Gap in Lemma 6.2 (repaired).** In the case where every configuration reachable from `ρ_n` has `β(p) < λ_{n+1}`
   on `R_n`, the bound on the `T|_{Q'}`-reachability set of `ρ_n|_{Q'}` is not justified. The restricted net does not
   constrain `p_1, …, p_n`. Repair: a shortest path argument followed by Lemma 5.2 (`lemma_6_2_step`); see the README.
10. The third case of Lemma 6.2 takes a shortest `T|_{Q∪R_n}`-path and lifts it, instead of a `T`-shortest
    `σ_{n+1}`. The bounds are the same. We use `|w| ≤ s` where the paper has `|w| < s`; the bounds still hold.
11. Theorem 6.1's induction uses `(1+‖T‖∞)·a^(h^i) ≤ a^(h^(i+1))`, which the paper uses without stating it; it holds.

## Section 7

12. Petri nets with control-states are abstracted as finite sets of labelled edges `(s, t, s')` over arbitrary vertex
    and label types, with a displacement `δ : L → ℤ^P` (`ControlStates.lean`). A path is a list of edges, a cycle is a
    closed path, a multicycle is a `Multiset` of cycles. Its Parikh image is the multiset of its edges, and its length
    is the total number of edges.
13. Lemma 7.1 (Euler) and Lemma 7.2 are proved as stated. In Lemma 7.1 the cycle may be chosen through any given
    control-state; the paper does this by "rotation" in Section 8.
14. "Elementary path" in Section 8 is replaced by "path of length `< |S|`" (`exists_decomp`); cycles of the
    decomposition have length `≤ |S|`. This is what the estimates use.
15. **Lemma 7.3 is proved with a different constant.** The paper's proof has a gap (see the README): the variables of
    system (1) are indexed by displacements, but the proof uses them as edge counts, and the length bound misses a
    factor `|S|`. We index the variables by the cycles occurring in `Θ`. We use the weak Pottier bound
    `Cslib.exists_small_decomposition` (`ℓ₁`-norm `≤ (2M')^(2^d−1)` for parts of a sign-conformal decomposition,
    independent of the number of variables), with `M' = |S|·M`. The statement becomes: for `M ≥ 1` bounding all label
    displacements, `K = (2|S|M)^(2^d−1)` and `k > ‖Δ(Θ)|_Q‖₁·|S|·M·K`, there is `Θ'` with the paper's sign, zero and
    edge conditions and `|Θ'| ≤ (|E|+d)·|S|·K`. The paper's hypothesis `‖T‖∞ > 0` becomes `M ≥ 1`. Whether the paper's
    constant `(1+2|S|‖T‖∞)^(d(d+1))` is correct is left open. Rule: unverified statement (not counted in the
    verdict); the gap is a proof gap (🛠️).

## Section 8 (Theorem 4.3)

16. Our constants differ from the paper's because of item 15. We use `M = ‖T‖∞`, `B ≥ b` (Theorem 6.1's constant for
    `d−1` places, bounded by `(4+4M+2‖ρ_L‖∞)^(E₁(d))`), `h = d(1+M)B`, `a = h^(2d+3)` (paper's `a`),
    `ℓ = h^(2^d+2d+4)` (paper: `h^(5d²)`), `k = d·h^(2^d+1)` (paper: `d·h^(d²+d+1)`), and the contradiction threshold
    `n > h^(2d+5)·ℓ` (paper: `h^(2d+4)·ℓ`). The extra factor `h` absorbs a factor 2 in the word-length estimate. The
    final estimate is `h^(2^d+4d+9) ≤ (4+4M+2‖ρ_L‖∞)^(d^((d+2)²))` (`Arith.final`), using
    `2E₁(d)(2^d+4d+9) ≤ d^((d+2)²)`. So the statement of Theorem 4.3 is exactly the paper's.
17. Lemma 7.3 is applied with `M = 1 + ‖T‖∞`. The paper silently needs `‖T‖∞ > 0`; for `‖T‖∞ = 0` the net is
    trivial.
18. Slips repaired (see the README):
    * `#Θ(e) ≥ ℓ` should be `≥ ℓ − |S|`.
    * `d‖α‖∞ ≤ b` should be `(d−1)‖α‖∞ ≤ b`.
    * `μ(p) − η'(p) − Δ(π)(p)` should be `μ(p) − α'(p) − Δ(π)(p)`.
    * The sign of `Δ(σ)(i)` is wrong.
    * `r ≤ d^(d²+d+3)` should be `d^(d²+d+5)`.
19. The path in the control-state net is built as the concatenation of the path of `w^(aℓ)`, the `ℓ`-th power of the
    total cycle `θ_E`, and the path of `σ'`. This makes `#π(e) ≥ ℓ` immediate, since paths are determined by their
    labels.
20. The case `d = 1` ("then `n = 1`", stated without proof in the paper) is proved for any protocol, without a width
    assumption (`n_le_one_of_card_le_one`). The paper says `n = 1`; we prove `n ≤ 1`, and `n = 0` is excluded only by
    the paper's convention `n > 0`.

## Section 4 (examples and corollary)

21. Example 4.1 is proved for `n ≥ 1`: `width = n` (`Ex41.width_eq`), stably computes, conservative, 2 states,
    leaderless. For `n = 0` the width is 1, not 0; the paper assumes `n` positive.
22. Example 4.2 is proved as stated (6 states, `n` leaders, conservative, width `≤ 2`, stably computes `φ_{i≥n}` for
    `n ≥ 1`). The paper's "last time `t` is executed" argument is replaced by a reachability invariant.
23. Corollary 4.4: `Ω` is made explicit as "`∃ c > 0, ∃ N, ∀ n ≥ N`, every protocol with width `≤ m` and at most `m`
    leaders computing `(i ≥ n)` has `|P| ≥ c (log log n)^h`", with `c` and `N` depending on `h` and `m`. The proof
    uses `log d ≤ (d+2)^ε/ε` instead of `d ≤ 2^((d+2)^ε)`. All `h < 1/2` are covered, including `h ≤ 0`.

## Not formalized

24. Pottier's sharp bound, hence Lemma 7.3 with the paper's constant; Remark 1; the cited upper bound of
    Blondin–Esparza–Jaax.
