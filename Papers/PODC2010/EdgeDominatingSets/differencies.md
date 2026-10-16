# Differences between the formalization and the paper

Paper: J. Suomela, *Distributed algorithms for edge dominating sets*, PODC 2010 (author's version,
10 pages, same numbering as the proceedings).

No statement of the paper turned out to be false. All items below are modelling choices, strengthenings,
or small imprecisions/typos.

## Model

1. **Port numbers start at 0** (`0, …, deg v - 1`) instead of `1, …, d`. The paper's port `2i-1`/`2i`
   pairs become `2j`/`2j+1`; "port 1" in Theorem 3 is port `0`. Pure renaming.
2. **Running time.** An algorithm is run for a fixed number `T` of rounds and every node outputs after
   round `T` (`Algorithm.eval G T`). The paper lets nodes stop at different times; a node that stops
   early can be simulated by one that idles until `T`, so the two models are equivalent for finite graphs.
   Lower bounds quantify over all `T`.
3. **Outputs.** A node outputs a set `X v ⊆ ℕ` of ports; ports `≥ deg v` are ignored. The computed edge
   set is `outEdges G X` (union of the selected edges). The paper's consistency requirement (§2.2) is
   the separate predicate `Consistent`; our upper-bound algorithms satisfy it, the lower bounds do not
   assume it (see 6).
4. **Covering maps** need not be surjective (`IsCovering`); surjectivity is irrelevant for the lifting
   argument (§2.3).
5. **Algorithms with a parameter.** `alg4 d` (Theorem 4) and `alg5 Δ` (Theorem 5) take the degree bound as
   a parameter, as in the paper's family `A(Δ)`. In a `d`-regular graph every node knows `d` anyway.

## Lower bounds (Theorems 1, 2, Corollary 1)

6. **Stronger than the paper.** `theorem_1`/`theorem_2` hold for every deterministic algorithm, with any
   running time, that outputs an edge dominating set *on the single graph `G`* (the paper assumes
   correctness on all `d`-regular graphs), and **without the consistency assumption**. Without consistency,
   two steps of the paper's argument need a small extra case (proof gap only for the stronger statement,
   not for the paper's):
   * §3.4: "a node outputs `2i-1` and another outputs `2i`" — we only know some node selects some port `q`;
     since `q` is not a half-loop of the quotient `M`, the `|V|` edges behind port `q` are pairwise
     distinct anyway (`card_fibre_le`, `card_le_of_fibre`).
   * §4.4: "`a_{ℓ,i}` is incident to an edge of `D`, hence `X(a_{ℓ,i}) ≠ ∅`" — without consistency, that
     edge may be selected only by an outer node through its port `ℓ`; then all `2d-1` edges between the
     outer nodes and `H(ℓ)` are selected (`card_filter_copy` handles both cases).
7. **Petersen's 2-factor theorem is not used.** The 2-factorisations of the lower-bound graphs are given
   in closed form (`Gadget.gp`): factor `j` is the bipartite circulant with differences `{s+2j, s+2j+1}`
   with node `b_0` removed and its two neighbours joined. `s = 0`, `m = 2k` gives the graph of §3.1
   (`K_{2k,2k-1}` plus a perfect matching on `A`), `s = 1`, `m = 2k+1` gives `H(ℓ)` of §4.1 with `c_ℓ = a_0`.
   The port numbering is a valid one in the sense of §3.2 / §4.1; the paper allows any.
8. **Outer connections in §4.1** use a different but equivalent bijection between `P ∪ Q` and `V(H(ℓ))`
   (`c_ℓ ↔ P_ℓ`, `a_x ↔ Q_x`, `b_y ↔ P_{y+ℓ}`). The paper's exact assignment is irrelevant for the proof;
   only `c_ℓ ↔ p_ℓ` and `Q ↔ A(ℓ)` matter for `D*`.
9. **Optimality of `S` and `D*`** (§3.1, §4.2) is proved via `|E| ≤ (2Δ-1)γ'` (`card_edgeFinset_add_le`),
   which is the paper's argument for `S`; for `D*` the paper only says "each edge not in `D*` is adjacent to
   exactly one edge in `D*`", which is the same counting. We prove `edgeDomNum G = k` resp. `(k+1)d`.
10. **`d = 1` in Theorem 2** (`k = 0`) is handled separately (ratio `1`, trivial).
11. **Corollary 1**: only the lower-bound content `α ≥ 4 - 1/k` for every `Δ ≥ 2k` is stated (for a single
    algorithm with a single running time; the family version follows pointwise). `α(1) ≥ 1` is trivial
    and not stated separately.

## Upper bounds (Theorems 3, 4, 5)

12. **Theorem 4: no forest argument needed.** The paper argues that phase I builds a spanning forest and
    phase II leaves "no path of length 3", hence a forest of stars with `≤ d` edges each. We prove directly
    that after phase II every edge has an endpoint covered by no other edge (`private_phase2`) and count
    `(d+1)|D| ≤ d|V|` by a charging argument (`card_mul_le`). Same bound, acyclicity is not used.
13. **Lemma 2 does not need simplicity** (`M_matching` holds in any port-numbered multigraph).
14. **Phase II of §7.1 (proposals in `B_i`) — a variant, not the same algorithm.** The paper cites a generic
    `O(i)`-round maximal matching algorithm ("black nodes propose to their *white* neighbours in the order of
    increasing port numbers until accepted; white nodes accept the first proposal, ties by port number"). We use
    two rounds per pair `(i, q)`, `i ≤ Δ`, `q < Δ`: every unmatched node of degree `i` proposes along its port `q`
    *whether or not the neighbour there is white* (an ineligible neighbour simply ignores it, so the step is
    wasted instead of skipped); every unmatched white node accepts the proposal at its smallest port; both
    endpoints then record the edge. The resulting matching `M` may differ from the paper's, but the variant
    preserves what the analysis uses: `M` stays a matching and is maximal on each `B_i` (property (c)).
    `2(Δ+1)Δ` rounds, still `O(Δ²)` in total. (Modelling choice.)
15. **Phase III of §7.1 (2-matching `P`) — a variant.** The paper uses the bipartite-double-cover matching of
    [21] (proposals on odd, accepts on even rounds, skipping to the next neighbour). We use two rounds per port
    `q < Δ`: a node without an accepted proposal proposes along port `q` (if the neighbour is not covered by `M`;
    otherwise the step is wasted); a node that has not accepted yet accepts the proposal at its smallest port.
    `P` may differ from the paper's, but the variant preserves the properties used: `P ⊆ H`, every node is in
    `≤ 2` edges of `P`, and every edge of `H` has an endpoint covered by `P` (the paper's §7.2 argument).
    (Modelling choice.)
16. **Running time** of `alg5 Δ` is `T5 Δ = 2 + Δ² + 2(Δ+1)Δ + 2Δ = O(Δ²)`; of `alg4 d` it is `2 + 2d²`;
    of `alg3` it is `1`.
17. **`D*` in §7.4–7.8 is an arbitrary edge dominating set** instead of a minimum maximal matching. The
    analysis only needs that every edge has an internal endpoint and `|I| ≤ 2|D*|` (the paper has
    equality for a matching). This avoids the theorem of Yannakakis–Gavril / Allan–Laskar quoted in §1.1
    (a minimum maximal matching is a minimum edge dominating set), which is not formalized.
18. **The weights/costs of §7.5–7.7** are organized per internal node in integer form:
    `(Δ-1)·2c(v) + w(v) ≤ 4Δ - 6` for every internal `v` (`node_bound`), where `w(v)` only sums over
    neighbours that are external `P`-nodes. The edge set `C` of §7.4 is not needed (property (b) is used
    directly). The final inequality is the integer form `2k|D| ≤ (8k-2)|D*|`, which also covers the
    degenerate case `|D*| = 0` where the paper's ratio is `0/0`.

## Small imprecisions and typos in the paper (all harmless)

19. §7.7, case `c(v) = 3/2`, sub-case `d_G(v) ≤ Δ - 1`: "`d_G(v) - 2` other nodes `x1, x2` in addition to
    `v`" should read "in addition to `s` and `t`". (Typo.)
20. §7.7, case `c(v) = 3/2`, sub-case `d_G(v) = Δ`: the paper's `w(v) ≤ 2 - Δ + 2(Δ - 3) < Δ - 3` is correct
    (the left side equals `Δ - 4`); listed only for completeness, not a mistake.
21. §7.7: two facts are used without being stated: in case `c(v) = 1`, `w({v,s}) = 2 - d(v) ≤ 0` needs
    `d(v) ≥ 2` (true: `v` has the distinct neighbours `s` and its `D*`-partner); in case `c(v) = 2` the
    `D*`-partner `u` differs from `s, t` (true: `u` is internal, `s, t` are external). (Proof gap with true
    statement, trivial.)
22. §7.8 divides by `|D*|`, which is `0` for an edgeless graph. (Degenerate case.)
