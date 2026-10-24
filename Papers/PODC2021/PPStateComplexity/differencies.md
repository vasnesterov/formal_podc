# Differences between the formalization and the paper

Paper: Czerner, Esparza (and Leroux in v3), *Lower Bounds on the State Complexity of Population Protocols*,
PODC 2021, arXiv 2102.11619 **v3** (the version formalized; numbering follows v3).

## Version

1. The PODC paper (= arXiv v2) proves `BB(n) ≤ 2^{2^{2^{O(n)}}}` (Ω(log log log η)) via rejection certificates
   and a weighting argument (§5 of v2). v3 replaces that with the double-exponential bound via Pottier's
   theorem. We formalize v3 (the local PDF). The v2 proof of §5 is not formalized.

## Model and definitions

2. Configurations are `Multiset Q` (the paper uses `ℕ^Q`; equivalent). Transitions are ordered quadruples
   `⟨p, q, p', q'⟩` with multiset pre/post (`Cslib.PopulationProtocol.Transition`); `T` is a set of them,
   total on pairs (paper: "at least one transition for every multiset `⦃p,q⦄`").
3. One input variable `x` (`X = {x}`, as in Sections 4–5); the input state `I(x)` is the field `Protocol.x`.
   Inputs are `i ≥ 2` (paper: `|m| ≥ 2`).
4. Fairness = CSLib `Run.GloballyFair` (if `C` occurs infinitely often and `C → C'` then `C'` occurs infinitely
   often). This is equivalent, for finitely many reachable configurations, to the paper's "reachable infinitely
   often ⇒ visited infinitely often". The output of an execution is "eventually all configurations are
   consensus configurations with output `b`", exactly as in the paper.
5. `SC_b` (`Protocol.Stable b`) is defined on all multisets, including those with fewer than two agents (the
   paper restricts configurations to `|C| ≥ 2`). This only enlarges the sets. Every use is on configurations
   reachable from inputs, which have `≥ 2` agents.
6. Basis elements: `IsBasisElem X B S` means `B + ℕ^S ⊆ X`; `InCone B S C` means `C ∈ B + ℕ^S`. The small basis is
   the set of all truncations: pairs with `B(q) = β` for `q ∈ S` and `B(q) ≤ β` otherwise, that are basis
   elements. This is the paper's construction (`B(i) := 2β` with the proof's `β`, i.e. the Definition-3
   constant `β = 2^{2(2n+1)!+1}`).
7. The busy beaver sets `BBSet n`, `BBLSet n` quantify over state types `Q : Type` with `card Q ≤ n`. `BB n` is
   their `sSup`. `BB_L` is not defined as a function because the set is unbounded (see 11).

## Section 3

8. Lemma 3.2 uses Rackoff's theorem. The paper cites it with the bound `|σ| ≤ 2^{2(2n+1)!}` ("Theorem 3.12.11 in
   [18]"). We prove it (`Cslib.PetriNet.exists_short_cover`, Rackoff's induction on the number of constrained
   places, bound `g(k+1) = (2g(k)+2)^{k+1} + g(k)`, then `g(n) ≤ 2^{2(2n+1)!}`).
9. In the proof of Lemma 3.2, the covered state `q` with `O(q) ≠ b` lies outside `S`. The paper does not say
   this, but it is needed: if `q ∈ S`, the bound `|σ| ≤ β` would only give `≥ 0` agents in `q` from `B`. It
   holds because states in `S` are populated in the `b`-stable `C`. Our `firesSeq_of_add` makes the "a
   transition moves at most two agents out of a state" argument precise.
10. Counting: `(2β+2)^n ≤ ϑ(n) = 2^{(2n+2)!}` is proved (`beta_add_two_pow_le`). The basis of `SC` is taken
    directly, rather than as the union of the bases of `SC_0` and `SC_1`, so the bound `ϑ` holds for it too.

## Section 4

11. **`BB_L` is under-specified** (Definition 1 with leaders). `majority4 η` (4 states, `η` leaders) computes
    `x ≥ η` for every `η` (`majority4_computesGe`), so `BBLSet 4` is unbounded (`not_bddAbove_BBLSet`). Read
    literally, the claims about `BB_L(n)` and the state complexity with leaders (abstract, §1, §4 intro, §4.1,
    §6) are false. The evident intent is a fixed number `ℓ` of leaders (Theorem 4.5's bound depends on `ℓ`; the
    cited Blondin et al. construction and the follow-up by Leroux, PODC 2022, use a fixed number of leaders).
    With `ℓ` fixed the claims follow from Theorem 4.5, which we prove. We do not define `BB_L` as a function.
12. **Lemma 4.1** needs `b ≥ 1`. In the paper this is implicit: `D_b` is a "configuration", hence has
    `≥ 2` agents, so `b ≥ 2`. Since our configurations are arbitrary multisets (item 5), we add `b ≥ 1`;
    without it the lemma fails (`lemma_4_1_b_zero_false`).
13. **Theorem 4.5's proof** applies Lemma 4.1 without establishing condition 2 (`b·x →* D_b`). We prove the
    variant `lemma_4_1'`, with condition 2 replaced by `B + D_a + b·x →* B + D_a + D_b`, which Lemma 4.2 provides.
14. Lemma 4.4 is a cited result (Figueira–Figueira–Schmitz–Schnoebelen). We state its conclusion as the property
    `CtrlChainProp δ g F` (sequences `v : ℕ → ℕ^d` with `|v_i| ≤ i + δ` have chains of `g(d)+1` elements with
    indices `≤ F(d)`). Theorem 4.5 is proved for every such `F`. Existence of such `F` (the least one,
    `Cslib.ctrlChainBound`) is proved by compactness and Dickson's lemma. **Not formalized:** that `F` can be
    chosen at level `F_ω` of the fast-growing hierarchy.
15. Theorem 4.5 indexing: the sequence of Lemma 4.2 starts at `C_2`, while Lemma 4.4 starts at `v_0`. We set
    `v_0 = v_1 = 0` and use chains of `ϑ(n) + 3` elements (`g = ϑ + 2`), so at least `ϑ + 1` chain elements are
    real `C_i`. The result is `η < F(n)` with `F` for `δ = ℓ`, `g = ϑ + 2` (paper: `g = ϑ`). The paper's
    proof ends with `η ≤ i_k ≤ F` although the statement is `η < F`; our proof gives the strict inequality
    since `i_k < i_ℓ ≤ F`.
16. Lemma 4.2 is formalized as `exists_seq`: a function `C : ℕ → Multiset Q` with properties for `i ≥ 2`.
    The paper's "for every `2 ≤ i ≤ k`" is a typo.

## Section 5

17. **Lemma 5.2** needs `b ≥ 1` (implicit in the paper, as for Lemma 4.1: `D_b` is a configuration). With
    arbitrary multisets and `b = 0` it fails (`lemma_5_2_b_zero_false`, Example 2.1 with `k = 2`).
    Our version requires saturation only on the pre-states of transitions in the support of `π`, not on
    all states. This is a weaker hypothesis, so the lemma is stronger.
18. **Lemma 5.1(ii)**: stated directly as `C =π⇒ C'` plus saturation on relevant pre-states ⇒ `C →* C'`. The
    paper's statement "for any `σ` with Parikh mapping `π`" is not formalized; we only need some `σ`. Lemma
    5.1(i) is the existing `FiresSeq.flowEq`.
19. **Hidden assumption (§5.3)**: "Recall our assumption that every state is coverable" is never stated in the
    paper. We do not assume it. `Protocol.Coverable` is the set of coverable states. Lemma 5.3 is stated for
    supports strictly inside the coverable states. Lemma 5.4 gives a configuration reachable from `IC(3^n)` that
    populates every coverable state. Saturation in Lemma 5.2 is only needed on coverable states.
20. Lemma 5.4's bound `|σ| ≤ 3^n` on the sequence length is not formalized (it is unused).
21. **Pottier's theorem (Thm 5.6) is not formalized.** Corollary 5.7 is replaced by our weak Pottier theorem
    `Cslib.exists_small_decomposition`: for `e` rows with entries `|a_ij| ≤ M`, every solution of `Ay ≥ 0` is a
    sum of solutions of `ℓ₁`-norm `≤ (2M)^{2^e − 1}`. We apply it to the `|Q|` inequalities
    `Σ_t π(t)Δ_t(q) + [q = x]·i ≥ 0` in the `|T| + 1` variables `(π, i)`, with `M = 2`. So our Pottier constant
    is `ξ(n) = 4^{2^n − 1}` (`Protocol.xi`) instead of `2(2|T|+1)^{|Q|}`. The paper's system ("`|Q|−1`
    equations on `|T|` variables") cannot decompose `i` and `C` alongside `π`, as the proof of Lemma 5.8
    requires.
22. **Lemma 5.8**: the hypothesis is the strict `ξ·C(Q\S) < i` (the paper's non-strict `1/ξ`-concentration
    does not suffice for its proof). The proof's `C(S)` should be `C(Q\S)`. The case "`x ∉ S`, θ empty" is
    corrected to "`x ∈ S`: `j = 1`, `θ = 0`, `C' = x`". We also return `θ ≤ π` (pointwise), used for saturation,
    and `|θ| ≤ ξ`, `0 < j ≤ ξ`.
23. Lemma 5.5 is not a separate lemma; its content (`|B| ≤ nβ`, concentration) is inlined in
    `theorem_5_9_le`.
24. **Theorem 5.9**: `theorem_5_9_le` proves `η ≤ ξ n β 3^n` with our `ξ`. `theorem_5_9` proves
    `η ≤ 2^{(2n+2)!}` exactly as stated. The arithmetic (`xi_mul_le`) differs from the paper's chain (which uses
    `|T| ≤ n^4` and Pottier's `ξ`).

## Other

25. Example 2.1: transitions not listed in the paper are taken to be identities. `P'_k` has `k+2` states
    (`0, 2^0, …, 2^k`), not `k+1`. We prove that `P'_k` computes `x ≥ 2^k` for every `k`
    (`exampleP'_computesGe`), hence `2^k ≤ BB(k+2)` (`le_BB`).
26. Theorem 2.2 (cited lower bounds of Blondin et al.) and Section 4.1 (discussion) are not formalized.
