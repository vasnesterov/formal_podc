# Differences between the formalization and the paper

Paper: P. Floréen, P. Kaski, V. Polishchuk, J. Suomela, *Almost Stable Matchings in Constant Time*,
arXiv:0812.4893v1 (full version of the PODC 2010 brief announcement).

## Errors in the paper

1. **Lemma 6 is false as stated for `Δ = 1`.** The hypothesis `i ≥ 1 + (Δ-1)/γ` allows `i = 1`
   when `Δ = 1`. Then `w_1(B) = 0`, since nothing is matched after round 1, while
   `f_1(R) = Σ_r w(r, first(C(r))) > 0`. Counterexample: `K₂` with unit weights, every `γ > 0`
   (`lemma_6_false_at_one`, `Counterexample.lean`). For `Δ ≥ 2` the hypothesis forces `i ≥ 2`, and
   the lemma is true. We prove Lemma 6 with the extra hypothesis `i ≥ 2` (`Bicoloured.lemma_6`).
   *Rule.* R3 (with R2 as support) ⇒ ⚠️. The missing `i ≥ 2` is recoverable from the paper:
   the proof is "By Lemma 4 and Lemma 5", both stated for `i ≥ 2`, so the paper's proof reasons
   with the intended version. The fix is local (one hypothesis) and changes no constant of
   Theorems 1–3. Borderline aspect (recorded per R6): `K₂` by itself is not a degenerate instance
   for a distributed algorithm, but the failure needs `Δ = 1`, where every node has a single
   acceptable partner and the unique stable matching is all of `E`; and it occurs only at `i = 1`,
   when no proposal has been answered yet. The failure exists for no `Δ ≥ 2`.
   *Consequence for the proofs of Theorems 1 and 2.* Both choose an integer `i` with
   `1 + Δ(Δ-1)/ε ≤ i < 2 + Δ²/ε` (resp. `1 + (Δ-1)/ε ≤ i < 2 + Δ/ε`). For `Δ = 1`, `i = 1` is
   allowed and wrong: `M_1 = ∅` while every edge is unstable. Choosing `i = max(2, ⌈…⌉)` repairs
   this with the same bound on `T = 2i` (`rounds1`, `rounds2`, `rounds1_bound`, `rounds2_bound`).
   This is a proof repair; the theorem statements are true.
2. **Proof of Lemma 5:** "`w({r,b}) < w_j(b)`" should be `≤`, since weights respect the
   preferences only weakly (`w ≡ 1` gives equality). Typo inside a proof; only `≤` is used.

## Statements: what is proved, compared with the paper

* **Lemma 1** is proved for every `i ≥ 0`.
* **Lemmas 2, 3** are proved for `i ≥ 2`, as in the paper.
* **Lemmas 4, 5** are proved for `i ≥ 1` (paper: `i ≥ 2`), which is stronger.
* **Lemma 6** needs the extra hypothesis `i ≥ 2` (see above).
* `Δ - 1` is natural-number subtraction (`(Δ - 1 : ℕ)`). It differs from the paper only for
  `Δ = 0`, the empty graph.
* Weights are nonnegative reals (paper: positive integers). They must *respect the preferences*:
  `v` prefers `x` over `y` ⇒ `w{v,x} ≥ w{v,y}` (`RespectsPrefs`). For Theorem 2 the preferences
  are derived from the weights. A node ranks its ports by decreasing weight, ties broken by port
  number (`wrank`), and this ranking respects the weights.
* **Theorem 1** (`theorem_1`, `theorem_1_ties`) is stated in CSLib's port-numbering model:
  `∃ A T, T ≤ 4 + 2Δ²/ε ∧ ∀ V G red, …`. The algorithm is uniform in the graph. The output is
  the partner's port. It is consistent (`IsMatching` of the decoded partner function), and the
  number of unstable edges is at most `ε |M|`. Isolated nodes are allowed, a generalization.
  "Δ is the maximum degree" is replaced by "all degrees `≤ Δ`".
  *Ties.* The paper gives no formal model of ties. We take a weak preference `pref : V → V → ℕ`
  with which the port numbering is compatible (`i < j` ⇒ `pref(port i) ≤ pref(port j)`). An edge
  is unstable if both endpoints *strictly* prefer each other to their partners, the paper's §1.1
  definition with weak preferences. Ports are numbered "according to `v`'s preferences" (§1.2), so
  a tie-respecting port numbering is the natural reading.
* **Theorem 2** (`theorem_2`): for every matching `M*` (any partner function forming a matching),
  `w(M*) ≤ (2+ε) w(M)`, with `T ≤ 4 + 2Δ/ε`. Each node's input is its colour and the weights of
  its incident edges per port (`fun i => w (G.edge v i)`), so the weights are consistent.
* **Theorem 3.**
  - The randomness is uniform on `(Fin N → V) × (Fin K → V)` with the paper's `j`, `N`, `K`
    (`j3`, `N3`, `K3`; `N = ⌈N₀⌉`, `j = ⌈1 + (2Δ-2)/ε⌉`). The algorithm knows `n` (§6.3 assumes
    this too). The estimator is `estimate` (`none` = failure).
  - The statement is `1 - δ ≤ Pr[no failure ∧ |m̂ - |M_∞|| ≤ ε|M_∞|]`. Here `M_∞` is the stable
    matching computed by Gale–Shapley (`Minf`, §5.1); the paper writes "a stable matching `M`" but
    proves the claim for `M_∞`. That all stable matchings have the same size (rural hospitals) is
    not formalized.
  - We assume `V` is nonempty, which excludes a degenerate case.
  - The oracle is not modelled as an interactive query process. The query bound is split into
    three facts. (i) Locality (`run_congr_of_agree`): `(run j).p r` depends only on
    `N`, `rank`, `red` of the nodes within distance `2j` of `r` in the graph. (ii) Such a ball has
    `< 3(Δ-1)^{2j}` nodes (`ncard_closedBall_lt`). The agreement hypothesis `AgreeAt` asks for
    equal numeric ranks, while the oracle reveals only the order of the neighbours. This is
    harmless: the oracle's list positions are themselves valid ranks, and the algorithm uses
    ranks only through `best` (the minimum), but the invariance of the run under order-preserving
    re-ranking is not stated in Lean. (iii) The arithmetic
    `N + 2(Δ+1)N + 3(Δ-1)^{2j}N ≤ 25000 ε⁻² (Δ-1)^{3+4Δ/ε} ln δ⁻¹` (`queries_le`). The paper
    states `<`; we prove `≤`, which suffices for "at most". We prove `N ≤ 6250 (Δ-1)³ ε⁻² ln δ⁻¹`
    (paper: `N₀ < 6195(…)`, then "we can select … `N ≤ 6250(…)`"), using `ln 6 ≤ 2.6 ln 2` instead
    of the exact ratio.
  - Chernoff bound (1) (Janson et al., Cor. 2.3) is proved, not assumed:
    `Podc/Probability/Finite/MultiplicativeChernoff.lean`, counting form, with the same constants
    `2 exp(-β²μ/3)`, `0 ≤ β ≤ 1`.
  - The paper bounds the probability that `Y` deviates by treating `Y` as `Bin(N, |M_j|/|R|)`. It
    does not say that this holds only conditionally on finding `N` red nodes among the `K` samples.
    We prove the bound
    `Pr[Z ≥ N ∧ |Y - qN| ≥ βqN] ≤ 2 exp(-β²qN/3)` directly
    (`card_firstHits_abs_sub_ge_le`), by a martingale argument. This is a proof clarification, not
    an error.
* **§5.1** ("there is `z` with `L_z = L_{z-1}`, and `M_z` is stable"): `exists_stable` proves that
  some round `z ≥ 1` is quiet, `M_z` is stable, and the run is constant from `z` on.
* **§2.2**: the path from the figure (11 nodes; every node prefers its left neighbour; the
  transposition swaps the two preferences of node `1`). Each instance has a unique stable matching
  (`pathPG_unique_stable`), and the two are edge-disjoint (`stable_matchings_disjoint`). The claim
  that "the number of communication steps is linear in the diameter" is informal and not
  formalized.
* **§2.4**: every matching of the rotational triangle has at least one unstable edge and at least
  as many unstable edges as matching edges. Hence there is no `ε`-stable matching for `ε < 1`
  (`triangle_not_epsStable`).
* **§2.5**: formalized as "for every `ε > 0` and every matching `M` of the path `P₄` there are
  `α > 1` and a matching `M*` with `(2-ε) w_α(M) < w_α(M*)`" (`no_order_based_two_sub_eps`). An
  algorithm that sees only the order of the weights `1, α, 1` outputs the same `M` for every
  `α > 1`.

## Modelling choices

* **Algorithm of §4.** The centralised transition reads the post-blue-turn states of the neighbours
  instead of explicit messages. 'propose' to `b` ↔ `c(r) = b`; 'accept' ↔ `b` now points to `r`;
  'reject' or 'break' ↔ `b` now points elsewhere. Under the invariants (consistency of `p`) this
  is exactly the message semantics of §4. Turn by turn the transitions are the paper's: blue
  steps 1–5, red steps 1–3.
  `C(r)` is a set ordered by `rank r`, and "first element" is the `rank`-minimal element (`best`).
* **Port-numbering implementation.** `gsAlg` is built from CSLib's `Algorithm.ofLocal`
  (full-information messages plus a round counter). Even rounds are blue turns and odd rounds red
  turns, so after `T = 2i` rounds the output is `M_i` (`dec_localRun`). In the paper's model a
  step is "receive, compute, send"; the CSLib round is "send, receive, compute". The two
  correspond because round 1's blue turn receives nothing.
* **Preferences.** Strict ranks `rank v u ∈ ℕ`, injective on the neighbours of `v`. In the
  port-numbering model, `rank v u` is the (input) rank of the port leading to `u`. For Theorem 1
  it is the port number (`portPrefGraph`).
* **Unstable edges** are counted as unordered edges `Sym2 V`. `|M|` is the number of edges
  `{u, p(u)}`.
