# Differences between the formalization and [Hirvonen–Suomela, PODC'12]

Paper: Juho Hirvonen, Jukka Suomela, *Distributed Maximal Matching: Greedy is Optimal*, PODC 2012,
DOI 10.1145/2332432.2332464. Formalized version: arXiv 1110.0367 v1 (the only arXiv version);
numbering follows it.

**Verdict.** No error affects the results. Lemma 1, Theorem 2, Corollary 3, Lemma 5, Theorem 6
and all intermediate lemmas (4, 7, 8, 10–16) are proved. The only gap is the passage from the
paper's formal model (possibly infinite trees) to finite graphs. We close it.

## Gaps and imprecisions in the paper

1. **Finite graphs (proof gap with true statement, minor).** Theorem 2 and Corollary 3 speak of
   "anonymous `k`-edge-coloured graphs", but the formal model of §2.3 only covers colour systems,
   i.e. edge-coloured *trees*, which may be infinite. All lower-bound instances are infinite: each
   realisation, and also the final `U` and `V`, is a `d`-regular tree with `d ≥ 2`. Read with the
   usual meaning of "graph" (finite), the lower bound needs one more step. Every finite ball of a
   `d`-regular colour system must occur as the view of a node in a finite, simple, `d`-regular,
   properly `k`-edge-coloured graph. We construct such a graph (`MPAlgorithm.completion`): `2^k`
   copies of the ball; a boundary node lacking its colour-`c` edge is joined to its twin in the
   copy with coordinate `c` flipped. With it the lower bound transfers to finite graphs
   (`MPAlgorithm.findsMaximalMatching_of_finite`). So `theorem2_lower_messagePassing`,
   `theorem6_messagePassing` and `corollary3_messagePassing` hold for finite simple (and, for
   Theorem 6 / Corollary 3, regular) graphs.
2. **Operational model vs. view model (under-specified, harmless).** §1.2 describes synchronous
   message passing; §2.3 replaces it by "the output is a function of `(v̄V)[r+1]`" and justifies
   this in one sentence. We formalize both models and prove both directions.
   (a) An `r`-round message-passing algorithm on any edge-coloured graph depends only on the
   radius-`(r+1)` view (`MPAlgorithm.state_eq_of_view`), so it is a §2.3 algorithm with running
   time `r` (`hasRunningTime_toAlgorithm`).
   (b) Conversely, a full-information protocol computes any §2.3 algorithm in `r` rounds on every
   graph (`out_ofView`).
   (c) Outputs on the universal cover give a maximal matching on every graph, including graphs
   with cycles (`isMaximalMatching_view`).
3. **Typo.** In the proof of Lemma 8, "by symmetry, `w ∈ ȳY` implies `w ∈ x̄X`" should read
   `w ∈ ȳX`.

## Modelling choices and changed definitions

4. **The group `G_k`** is implemented as reduced words over `Fin k`, stored in reverse
   (`FreeCox k`), with a hand-built group structure. Colours are `0, …, k-1` instead of `1, …, k`;
   the greedy algorithm processes them in increasing order. `|x|` is `len x`. `head(x) = c` is
   `startsWith c x` (`|c x| < |x|`). `pred` and `tail` are expressed through `len (x * gen c) < len x`.
5. **Colour systems** (`IsColourSystem`): `e ∈ V` and closure under moving to the parent. This is
   the paper's prefix-closedness. `C(V, v)` is defined as `{c | v c ∈ V}` (`colours`), which the
   paper notes equals the edge-based definition. Lemma 4 is `IsColourSystem.inv_smul` plus
   `colours_inv_smul` (the colour-preserving isomorphism).
6. **Algorithms** are total functions `Set (FreeCox k) → FreeCox k → Option (Fin k)` (`⊥` =
   `none`). The running-time condition and (M1)–(M3) are imposed only for colour systems and
   nodes in them, as in the paper. Theorem 6 assumes that `A` has *some* running time `r`; this is
   part of the paper's definition of a distributed algorithm.
7. **Templates** (`Template`): the forbidden colour `τ` is a total function on `G_k`. Values
   outside `T` are irrelevant. (C2) `σ[h-1] = τ[h-1]` is agreement on `S ∩ {|s| ≤ h-1}`
   (`Compatible`).
8. **Realisations and `A(T, τ, t)`.** The paper builds the realisation `(V, p) = real(T, τ)` and
   sets `A(T, τ, t) = A(V, v)` for any `v ∈ p⁻¹(t)` (well defined by Corollary 10). We define
   `real T t` as the view from `t` of the graph "tree edges of `T` + half-loops of all colours
   `≠ τ(t)`", i.e. the `v̄`-translate of the paper's realisation. We set
   `out A T t = A (real T t) e`. Corollary 10 becomes `Good.apply_real`: every node of the
   realisation that maps to `b` outputs `out A T b`.
9. **Extensions** are built through Remark 1 (unfolding half-loops / universal covers), not through
   the recursive relation `⇝` of §3.3. Only 1-colour pickers are needed (`Template.extend`). The
   realisation is the `(d-h)`-picker case, handled separately.
   * Lemma 7 is `isTemplate_extend` (for `b = 1`) and `isRegular_real` (for the realisation).
   * Lemma 8 is proved for arbitrary edge-coloured graphs (`ColouredGraph.view_inv_smul`,
     `Template.extend_symm`).
   * **Lemma 9 (commutation of extensions) is not formalized.** It is only used to derive
     Corollary 11, which we prove directly with a covering-map argument (`Template.real_extend`).
10. **Lemma 15** is proved with the same distant/near split as the paper: `K₃` and `L₃` are the
    matched pairs whose two endpoints are both at distance `> r+1` from `e`. The parity count is
    organized differently. `N = X \ (K₃ ∪ L₃)` is finite. It carries three fixed-point-free
    involutions: `M(X, ξ)` on `N` (under the contradiction hypothesis), `M(K, κ)` on `N ∩ K₁`, and
    `M(L, λ)` on `N ∩ L₁ - χ`. This gives `|N|` both even and odd. We only conclude `y ∈ X`; the
    paper's extra `y ∈ K₂ ∪ L₂` is not needed.
11. **Observation (c) of §3.9** (compatibility of the `χ̄`-translates) is not used and is not
    formalized. Observations (a), (d) and (e) are `isTemplate_glue`, `compatible_glue_left` and
    `compatible_glue_right`. Observations (a)–(h) before them are bundled in `StepHyp` and proved in
    `stepHyp_of_critical`.
12. **Corollary 3** is formalized as the paper derives it: with `k = Δ + 1` colours, an algorithm
    correct on `Δ`-regular instances (in particular, on graphs of maximum degree `Δ`) needs `Δ`
    rounds. The `O(Δ + log* k)` upper bound and Linial's `Ω(log* k)` lower bound (§1.3) are cited
    results and are not formalized.
13. **Message-passing model details.** A node outputs after exactly `r` rounds instead of "stops
    after some round". This is equivalent: a stopped node can idle. Edge colours serve as port
    numbers, and the incoming messages are indexed by colour. A `ColouredGraph` may contain
    half-loops and parallel edges of different colours. Lower bounds assume only correctness on
    *simple* graphs (no half-loops, at most one edge between two nodes), which is the stronger
    statement; the upper bound (greedy) holds on all of them.
14. **Lemma 1, implementation.** In the message-passing model greedy runs as a full-information
    protocol (`ofView greedy`). The paper's remark that greedy needs only small messages and little
    memory is not formalized.
15. **Not formalized.** The informal remarks of §1.3–1.4: the case `d = k` is trivial, and the
    result also covers the port-numbering and broadcast models.
