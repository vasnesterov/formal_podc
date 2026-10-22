# Differences between the formalization and the paper

Paper: Chakaravarthy, Roy, Sabharwal, *Distributed algorithms for scheduling on line and tree networks*,
PODC 2012; formalized from arXiv:1205.1924v2.

## Model and problem statement

1. **Reformulated problem only.** We work with the reformulation of Section 2: demand instances `D`, the owning
   demand `dem d`, and the edge set `path d`; edges of different networks are distinct elements of `E`.
   Feasible solutions:
   - unit heights: independent sets of instances (`Inst.IsIndep`);
   - arbitrary heights: one instance per demand and capacity `≤ 1` per edge (`Inst.IsHFeasible`).

   `TreeInput.overlap_iff` shows that, for tree networks, overlap means "same tree, paths share an edge". So the
   equivalence with the original formulation ("select demands, schedule on accessible networks, edge-disjoint
   paths") is immediate. The original formulation is not stated separately.
2. **Profits per instance.** The abstract results allow an arbitrary profit `p(d)` per instance; the paper has
   `p(d) = p(a_d)`. This is more general. The concrete tree and line instances use `p(a_d)`.
3. **Positive profits, known bounds.** Profits must satisfy `0 < p_min ≤ p(d) ≤ p_max`, and the number `K` of
   steps per stage must satisfy `p_max < 2^K p_min`. The paper assumes `p_max, p_min` are known in its
   distributed implementation and says the assumption can be bypassed. That bypass is not formalized.
4. **Heights.** We assume `h_min ≤ h ≤ 1`, `0 < h_min ≤ 1/2` and equal heights for all instances of a demand, as
   in the paper. Narrow means `h ≤ 1/2` and wide means `h > 1/2`.
5. **Line networks.**
   - The timeline is finite: timeslots `0, …, n-1`, with every deadline `< n`. An instance occupies
     `[s, s+ρ-1]` on one resource.
   - The paper's `n` (number of timeslots) and its use of `n` for the number of demands in §7 are not
     reproduced.
   - `L_min ≤ ρ ≤ L_max` may be any bounds with `L_min ≥ 1`; they need not be the actual extremes.

## Distributed algorithm

6. **Steps instead of rounds.** The synchronous message-passing implementation is abstracted. A run of the first
   phase is a sequence of steps, and each step raises a maximal independent set of the candidate set `U`.
   - An arbitrary step-indexed MIS oracle provides that set (`Inst.IsMIS`), so all MIS algorithms (randomized
     or deterministic) are covered.
   - `Time(MIS)`, message sizes, local stacks and the communication graph are not modelled.
   - Round complexity is stated as the number of steps `ℓ·b·K`.
7. **Fixed stage length.** The pseudocode (Fig. 7) runs each stage "while `U ≠ ∅`". We run exactly `K` steps per
   stage with `p_max < 2^K p_min`, as in the paper's own distributed implementation ("`c log(p_max/p_min)`
   iterations"). Lemma 5.1 (`lemma_5_1`, `stage_complete`) proves that `U = ∅` after `K` steps, so the two
   coincide. The steps after `U = ∅` raise the empty set.
8. **Simultaneous raises / tests.** All raises of one step use the dual values from the start of the step. The
   paper's sets are independent, so its raises do not interact either.

   In the second phase all members of a popped set are tested against the solution built before the pop
   (`phase2`). For independent sets this equals the paper's one-by-one test: members do not conflict, and in the
   height case they do not share edges.
9. **Indexing.**
   - Groups and stages are 0-based: group `0` is the paper's `G₁`, and stage `j` is the paper's stage `j+1`, with
     threshold `1 - ξ^{j+1}`.
   - The progress factors are `ξ = 2(Δ+1)/(2(Δ+1)+1)` for unit heights (`14/15`, `8/9`) and
     `ξ = (1+Δ²)/((1+Δ²)+h_min)` for narrow instances. The paper only says "`c/(c+h_min)` for a suitable
     constant `c`"; we use `c = 37` for trees and `c = 10` for lines.
   - The number of stages `b` is any value with `ξ^b ≤ ε`. `exists_stages` gives `b = ⌈log_ξ ε⌉`, which is
     `O(log(1/ε))` for unit heights and `O(log(1/ε)/h_min)` for narrow instances. That `O(·)` bound itself is not
     formalized.
10. **Claim 5.2, general form.** `claim_5_2` holds for any rule in which a raise of `d₁` adds at least `κ δ(d₁)`
    to the constraint of a conflicting instance of the same group, with denominators `≤ M` and
    `2M(1-ξ) ≤ κξ`. It gives the strict inequality `p(d₂) > 2p(d₁)`.

    The unit case has `κ = 1` and `M = Δ+1`. The narrow case has `κ = 2h_min` and `M = 1+Δ²`. This makes the
    paper's "arguments similar to Lemma 5.1" for Lemma 6.2 explicit.

## Approximation statements

11. **Form of the ratios.** We prove `(1-ε)·p(O) ≤ c·p(S)` for every feasible `O`, i.e. ratio `c/(1-ε)`. The paper
    writes `c + ε′`, which corresponds to `ε = ε′/(c+ε′)`.
    - Lemmas 3.1 and 6.1 and the unit and narrow algorithms are proved against every feasible LP solution, which
      is stronger than against `Opt`.
    - The slackness parameter `λ` is any number with all constraints `λ`-satisfied; the paper takes the largest
      such number.
12. **Lemma 6.1, pigeonhole step.** We do not pick an edge `ẽ ∈ π(d′)` carrying more than `1/(2|π(d′)|)`.
    Instead we use the double count `∑_{d ∈ X} h(d)|π(d′) ∩ path(d)| ≥ ∑_{d∈X} h(d) > 1/2` (interference gives
    `|π(d′) ∩ path(d)| ≥ 1`). This gives the same bound.
13. **Theorem 6.3 / 7.2 combination.** On each network we keep `S₁` (wide) when its profit there is at least that
    of `S₂` (narrow); ties go to `S₁`.
    - The two algorithms run on the restricted sub-instances (`Inst.restrict`) with their own MIS oracles and
      stage counts `bw`, `bn`.
    - `p(Opt) ≤ p(Opt_wide) + p(Opt_narrow)` is proved, including that wide parts of feasible solutions are
      independent.
14. **Appendix A.** The sequential algorithm is run for `|D|` iterations, and we prove that afterwards all
    constraints are satisfied (`λ = 1`).
    - The order is lexicographic: networks are taken in the order of an enumeration of `Q`, and inside a network
      by decreasing depth of `µ(d)`. Ties are broken by an arbitrary `pick`.
    - Always picking the earliest unsatisfied instance in this order is the paper's round-by-round processing.
    - The ratio-2 remark for a single network is not formalized.

## Tree decompositions (Section 4)

15. **Rooted trees.** A rooted tree `H` on `V` is represented by the sets `C(z) = sub z` (z and its descendants)
    with laminar axioms. Its depth is `#{z | x ∈ C(z)}` (root depth 1, as in the paper), and LCA is the deepest
    common ancestor-or-self.
16. **TD property (i) for all pairs.** Property (i) (the LCA lies on the path) is required for paths between
    *all* pairs of vertices, not only demand paths. All decompositions of the paper satisfy this. Property (ii)
    ("`C(z)` induces a connected subtree") is stated as geodesic convexity, which is equivalent in a tree.
17. **Path geometry.** Path geometry is distance-based: `Btw T a w b` (from `TreeAA.TreeGeom`), and `pathEdges`
    lists the tree edges with both endpoints between `a` and `b`. `mem_pathEdges_iff_edges` shows that these are
    exactly the edges of the unique path. `TreeGeom` is imported from another paper's folder
    (`Papers/PODC2026/TreeAA/`); it should be staged in `Podc/` or upstreamed.

    The bending point `bend` is defined as the gate; `bend_spec'` proves the paper's definition. `capture` (`µ`)
    is the node of `path(d)` whose subtree contains the path; `depth_capture_le` and `eq_capture_of_depth_le`
    show that it is the paper's unique node of least depth.
18. **Depth bounds.**
    - Lemma 4.1 is proved with depth `≤ 2⌊log₂ n⌋ + 1` instead of `2⌈log n⌉`. The paper's bound is false for
      `n = 1`. Its intermediate claim `2⌈log|C|⌉` for BuildIdealTD fails for `|C| = 1`.
    - For `n ≥ 2` the paper's `2⌈log n⌉` is true (argued on paper, not formalized) and sometimes smaller than
      ours (`4` vs `5` for `n = 4`). Lemma 4.1 itself only claims `O(log n)`, which is all that is used.
    - Lemma 4.3 has length `2⌊log₂ n⌋ + 1`.
    - The paper's top level ("balancer g, then BuildIdealTD on each component") is realised by running
      BuildIdealTD on `C = V` (with `Γ[V] = ∅`). This is the same construction.
19. **BuildIdealTD degenerate cases.** These are handled uniformly:
    - `u′ᵢ = z`;
    - `u′₁ = u′₂`;
    - `j ∈ {u′₁, u′₂}`;
    - `z` adjacent to `j`, so `C′₁ = ∅`.

    The junction is the median of `u′₁, u′₂, z`, which is the same vertex as the paper's median of `u₁, u₂, z`.
    `Γ(·) = {…}` is replaced by `⊆` and `|Γ| ≤ 2`. Balancers are centroids (`exists_balancer`, by minimizing the
    sum of distances).
20. **Lemma 4.2.** It is proved for every TD, but the proof does not use property (ii); the paper appeals to it
    unnecessarily. Groups are `ℓ − depth(µ(d))` (0-based reversed depth).
21. **Observation A.1.** It is stated as "µ(d₂) lies on the path from the root `g` to `µ(d₁)`", which covers both
    sentences (ancestor, or the same node).
22. **Not formalized from Section 4.** The balancing decomposition. Its stated depth `⌈log n⌉` is off by one: the
    path on 4 vertices has depth 3.

## Line networks (Section 7)

23. **Groups.** Groups are `⌊log₂(len/L_min)⌋` (half-open classes `[2^i L_min, 2^{i+1} L_min)`), and
    `ℓ = ⌊log₂(L_max/L_min)⌋ + 1`. The paper's classes `[2^{i-1}L_min, 2^i L_min]` overlap at the boundaries and
    are not a partition. Its `ℓ = ⌈log(L_max/L_min)⌉` is `0` when all lengths are equal.
24. **Layering property.** The paper says it is "not difficult to argue". It is proved via `interval_hits`
    (`len₁ ≤ 2len₂+1` suffices) and `len(d₁) < 2 len(d₂)` for `grp d₁ ≤ grp d₂`.
25. **Theorem 7.2 typos.** The statement says "tree-networks" and its round bound has `log n`. We state it for
    line networks; the step count is `ℓ·(bw or bn)·K` with `ℓ = ⌊log₂(L_max/L_min)⌋+1`.

## Typos / stale text (no formal counterpart)

26. The Section 6 introduction announces `(20+ε)` and `(13+ε)` (conference values). Lemma 6.2 and Theorem 6.3
    give `73` and `80`.
27. §4.2: "the path between x and z" should be "x and y". §4.4: "inference property" should be "interference
    property".
