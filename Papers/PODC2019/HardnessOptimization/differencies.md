# Differences between the formalization and the paper

Paper: N. Bachrach, K. Censor-Hillel, M. Dory, Y. Efron, D. Leitersdorf, A. Paz, *Hardness of
Distributed Optimization*, PODC 2019 (arXiv:1905.10284v1; numbering follows it).

Classification used: **false statement** / **false only in a degenerate case** / **proof gap (statement
true)** / **under-specified definition** / **typo**.

## Framework (Section 1.3–1.4, Theorem 1.1)

1. **Model made explicit.** CONGEST = synchronous, deterministic (or with private random strings, see 4),
   fixed vertex set `V` whose names are the IDs, every node knows its neighbourhood (and, for directed /
   weighted problems, the directions / weights of its incident edges), exactly `B` bits per edge, direction
   and round (`Cslib/Computability/Distributed/Congest/LowerBound.lean`). The algorithm may depend on `V` (it may even "know" it runs on
   the lower-bound family), which only strengthens the lower bounds. Decision convention: *all nodes accept
   iff the predicate holds* (the weakest usual convention).
2. **Theorem 1.1 (deterministic) is proved, with explicit constants**: `CC(f) ≤ T · 2|E_cut| · B + 2`
   (`LBFamily.lowerBound`). The deterministic bound `CC(DISJ_K) ≥ K` is *proved* by a fooling set
   (`Protocol.disj_lowerBound`), so the deterministic theorems of this folder are unconditional.
3. **Definition 1.1, item 4, vs. the constructions (imprecision).** Item 4 demands "`G_{x,y}` satisfies `P`
   iff `f(x,y) = TRUE`" with `f = DISJ`, but every construction of the paper has `P ⟺ DISJ = FALSE`.
   Harmless (complementing the output costs nothing); we use `not_disj_lowerBound`.
4. **Randomized half of Theorem 1.1**: the simulation is proved (`LBFamily.rand_simulation`,
   `rand_lowerBound`, private coins: Alice draws the strings of `V_A`, Bob those of `V_B`); the bound
   `CC^R(DISJ_K) = Ω(K)` is *not* formalized and enters as a hypothesis (`theorem_2_1_randomized`); the hypothesis `hCC` quantifies only over protocols with *nonempty*
   coin spaces (with an empty coin space the error count is `0`, so `hCC` would force `c = 0`;
   `hCC_without_nonempty_degenerate`).
   Randomized versions are stated only for MDS.
5. Only the **decision versions** are formalized. "Computing a minimum dominating set / Steiner tree / max
   cut" (reduction via `O(D)` extra rounds) is not formalized.

## Section 2.1 — MDS (Lemma 2.1, Theorem 2.1)

6. **`bin` / `bin̄` (typo only).** Rows are adjacent to `bin(s^i) = {f^h | i_h = 0} ∪ {t^h | i_h = 1}`;
   the `⇐` direction of Lemma 2.1 puts the complementary sets `bin̄(a^i_1), bin̄(a^j_2), bin̄(b^i_1),
   bin̄(b^j_2)` into `D`, which is correct (`canonDS`, `dsKind`). The only slip is `t^j_S` for `t^h_S` in the
   definition of `bin̄`.
7. **Lemma 2.1, case "`4 log k + 1` gadget vertices and one row vertex" (proof gap, statement true).** "Hence,
   for at least one `S ∈ {B₁, B₂}`, `F_S ∪ T_S ∪ U_S` contains exactly `log k` vertices of `D`" does not
   follow from the counts given (e.g. `|D ∩ A₁-gadgets| = log k − 1`, `B₁` and `B₂` gadgets `log k + 1`
   each is consistent with them). One must also use that the rows of `A₁` other than the one in `D` have to
   be dominated by gadget vertices, which forces `≥ log k` gadget vertices of `D` on `A₁`.
8. **Lemma 2.1, case "two row vertices" (proof gap, statement true; an intermediate claim is false).** The
   claim "`D` contains exactly one of every pair `f^h_S, t^h_S`" is false: for `k = 2`, `x = y =` "column
   `p` all ones", `D = {a^p_2, b^p_2, u^0_{A₁}, u^0_{B₁}, t^0_{A₂}, t^0_{B₂}}` is a dominating set of size
   `4 log k + 2` with neither `f^0_{A₁}` nor `t^0_{A₁}` (`paper_intermediate_claim_false`). The argument
   "if `f_A ∈ D` then `f_B` must be in `D` to dominate `u_A`" overlooks `u_A ∈ D`. Our proof: every cycle
   holds exactly two vertices of `D`, `D` has exactly one row per side, and a case analysis of the 9
   two-element patterns of a 6-cycle (checked by `decide`, `MDSLocal.lean`); the layer without rows may use
   the pattern `{u_A, u_B}`.
9. **Disconnected graphs (under-specified model, harmless).** `G_{0,0}` is disconnected (the two layers are
   joined only by input edges, `mdsGraph_zero_not_connected`), whereas CONGEST networks are usually
   connected. `G_{x,y}` is connected whenever `x ≠ 0` or `y ≠ 0` (`mdsGraph_connected`), and the fooling-set
   argument never uses `(0,0)`, so the bound holds for algorithms that are only correct on connected graphs
   (`theorem_2_1_connected`, via `not_disj_lowerBound_of_ne_zero`).
10. **Statement.** We prove the predicate "dominating set of size `≤ 4 log k + 2`" and also "exactly
    `4 log k + 2`" (`lemma_2_1`); every dominating set has size `≥ 4 log k + 2` (`four_mul_add_two_le_card`).
    Theorem 2.1 is stated as `k² ≤ 8 T B log k + 2` and, in terms of `n = 4k + 12 log k`,
    `n² ≤ 256 (8 T B log₂ n + 2)` (`theorem_2_1_n`). Lemma 2.1 holds for all `k = 2^L`, including `k = 1`.
11. Typo: "`i ∈ [n]`" in the definition of `bin` should be `i ∈ [k]`.

## Section 2.3 — Steiner tree (Theorem 2.6, Claim 2.8, Theorem 2.7)

12. **Claim 2.8, `⇐` direction (proof gap, statement true).** The proof takes an *arbitrary* dominating set
    `C` of size `4 log k + 2` and uses "`C` contains exactly either `f⁰_{A₁}, f⁰_{B₁}` or `t⁰_{A₁}, t⁰_{B₁}`"
    to join the two cliques by a crossing edge. This is false for some minimum dominating sets (item 8:
    the first-layer cycles may meet `C` in `{u_A, u_B}`). Fix: use the canonical dominating set of the
    intersecting index (`steiner_of_not_disj`).
13. **Degenerate case `k = 1` (false only in a degenerate case).** There is no bit `h = 0`, hence no crossing
    edge, `G'` is disconnected and there is no Steiner tree at all, while `DISJ_1` can be FALSE. We assume
    `log k ≥ 1` (`[NeZero L]`).
14. Typo: the proof of Claim 2.8 speaks of "three crossing edges"; the construction has two.
    `|E'_cut| ≤ 8 log k + 2` (`card_stCut`).
15. Theorem 2.6 (reductions between families) is not stated separately; it is applied directly
    (`stFamily`). The leaf-normalization step in Claim 2.8 (`T''`) is unnecessary: in any Steiner tree every
    terminal has a non-terminal tree neighbour because terminals are pairwise non-adjacent.
16. "Steiner tree of size `M`" is read as "a tree with `≤ M` edges on a vertex set containing all terminals,
    using edges of `G'`" (`HasSteinerTreeLE`).

## Section 2.4.1 — weighted max-cut (Claims 2.9–2.12, Lemma 2.4, Theorem 2.8)

17. **Claim 2.9 (proof gap, statement true).** The proof needs the total weight of the non-`k⁴` edges to be
    `< k⁴`; this weight is exactly `16k³ log k − 4k³ + 2k² + |x| + |y|`, which is `< k⁴` only for `k ≥ 128`.
    Claim 2.9 nevertheless holds for every `k ≥ 2` (`claim_2_9`), and so does Lemma 2.4 (`lemma_2_4`): we
    replace the exchange arguments of Claims 2.9–2.12 by a single counting inequality valid for every cut
    (`main_ineq`: `w(σ) + k⁴U + … ≤ M + k³U`, `U` = number of uncut heavy edges), and the paper's cut has
    weight exactly `M − 2·(input edges between the chosen rows)` (`cutσ_star`). Also "`O(k²)` edges of
    weight 1" ignores that the `N`-edges weigh up to `k` (harmless).
18. **`E_cut` (imprecision, minor).** With the paper's partition, `C̄_A – C_B` also crosses the cut:
    `|E_cut| = 4 log k + 1`, not only the T/F edges.
19. Claim 2.10's proof says the edges from `a^j_1` to `A₂ ∪ {N_A}` "have weight 1"; the `N_A` edge weighs
    `Σ_j x_{i,j}` (only the total `≤ k` is used, which is correct).
20. Degenerate case `k = 1`: the weight `2k² log k − k² = −1` is negative; we assume `log k ≥ 1`.
21. Predicate: "a cut of weight `M`" — we prove it for "`≥ M`" and for "`= M`" (`lemma_2_4_eq`), since every
    cut weighs `≤ M` (`cutWeight_le_M`). Weight-0 edges (`Σ_j x_{i,j} = 0`) are omitted from the network;
    node inputs are the incident weights.
22. Typos: "`b^{j_i}_z`" should be `b^{j_z}_z`; "`N_a`"; "`z^j_i ∈ B₁ ∪ B₂`".

## Section 2.2 — Hamiltonian path / cycle

23. **Missing arcs `r_c → ℓ^{c,k−1}_q` (under-specified definition).** The textual construction defines no
    out-arcs of `r_c`, yet the proof of Claim 2.1 uses them and Figure 2 draws them. Taken literally, `r_0`
    and `end` have out-degree 0 and no `D_{x,y}` has a Hamiltonian path (`paperArc_not_hamPath`; also found
    by brute force for `k = 2`). We add these arcs; then `hamPath_iff` (Claims 2.1 + 2.2) holds for all
    `k = 2^L ≥ 2`.
24. **Claims 2.3–2.5 (proof gaps, statements true).** Claim 2.4's base case ("move into a wheel from its
    row copy") is unintelligible as worded. Part 2 assumes, without proof, that `g_{c+1}` is visited before
    `r_c`. Claim 2.5's "by Claim 2.3, this happens after `s¹₁`" needs an unproved lemma, and one out-arc of
    `β` (to `ℓ^{d−1}`) is ignored. Our proof of Claim 2.2 uses path positions (`Fin n ≃ V`). It classifies
    each block `(c, q, d)` as left forward or backward and shows that in every box one line runs forward from
    `g_c` and the other backward from `r_c` without wheel detours.
25. **Partition and cut not given (under-specified).** Only "`|E_cut| = O(log k)`" is stated. We take
    `V_A` = start, `s¹₁`, `s²₁`, the A-rows, all `g_c`, `r_c`, and the line vertices at positions `d < k/2`;
    then `|E_cut| ≤ 24 log k + 1` (`+1` for the cycle version).
26. **Wheel indexing (under-specified, harmless).** The "`d`-th index whose `c`-th bit is 1" is ambiguous
    (0/1-based, range of `c`). We use any bijection that puts A-rows in the first half of each line
    (`HamPathWheel.lean`, via `Fin.insertNth`). The claims are proved for every wheel satisfying the
    membership property.
27. **Typos.** "log(k) ≤ s ≤ log(k) − 1" should be `≤ 2 log k − 1`. `r_{log k − 1}` (twice in Claim 2.1)
    should be `r_{2 log k − 1}`, and `choose_s` for `s ≥ log k` tests bit `s − log k` of `j`. Claim 2.5 writes
    "`0 < c < 2 log k − 1`", which excludes the last box.
28. **Lemma 2.3 (typo; false as written).** `E' = {(u,w) | u, w ∈ V∖{v}}` is missing "`(u,w) ∈ E`".
    Lemmas 2.2/2.3 infer "`T(n) = O(n²)` ⇒ `2T(3n) = O(T(n))`", which does not follow, but the lower bound
    transfers by substitution anyway. Not formalized.
29. **Claim 2.7 omits "spanning" (false as stated).** `K₄` plus two pendant vertices has a 2-edge-connected
    subgraph with `n` edges and no Hamiltonian cycle. True for spanning subgraphs. Not formalized.
30. Network and inputs: the CONGEST network is the underlying undirected graph, and every node knows its in-
    and out-arcs. The theorems are stated for `k = 2^(L+1)`.
31. Not formalized: Theorems 2.4–2.5 (undirected Hamiltonian path/cycle, 2-ECSS) and the "finding" versions.

## Not formalized

Section 2.4.2 (the `(1−ε)`-approximation algorithm for max-cut, which rests on a cited sampling theorem);
Section 3 (bounded-degree lower bounds via max-2SAT and expanders); Section 4 (hardness of approximation:
codes / probabilistic constructions); Section 5 (limitations of the framework, nondeterministic protocols,
proof labeling schemes).
