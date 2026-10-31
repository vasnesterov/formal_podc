# Differences between the formalization and the paper

Paper: BA (PODC 2025) + full version arXiv:2502.13854v1 (cited by the BA as [23]); v3 (Feb 2026)
consulted for the corrected statements. Rule references (R1–R6) are to the project's verdict scale.

## Model

1. **One round only.** All results are for `r = 1` (radius-1 views). The paper's Theorem 4.2 is
   stated for every `r ≥ 1`; a counterexample at `r = 1` refutes it. The `r`-round model (views of
   radius `r`, Lemmas 5.1–5.5) is not formalized.
2. **Views are richer than the paper's.** Our view = `N`, own id, label, degree, and the multiset of
   records `(port here, port there, id, label, degree)` of the neighbours. The paper's radius-1 view
   `(G¹ᵥ, prt|N(v), Id|N(v), I|N(v))` is contained in it (the degree of a neighbour may or may not be
   included in `prt|N(v)`; we include it). Richer views make extraction algorithms stronger, so all
   our hiding results are at least as strong as the paper's; the decoders we analyse use only
   information the paper's view has.
3. **Ports are `0, …, deg − 1`** (paper: `1, …, deg`). Decoder rules mentioning ports were shifted
   accordingly (Lemma 4.2, Theorem 4.4).
4. **`N`.** Every instance carries `N` with injective identifiers `< N`; admissible instances have
   `N = bound n` for an arbitrary global `bound : ℕ → ℕ` (paper: `N = poly(n)`). All results hold
   for every `bound`; hiding results assume only `n ≤ bound n` at the size of the hard instance.
5. **Extraction algorithms are arbitrary functions** of the view (paper: computable maps). This makes
   "hiding" stronger and "not hiding" weaker; Lemma 3.2 holds in both versions (the paper's proof
   adds computability via Lemma 3.1, which we do not formalize).
6. **Certificate sizes** are modelled by a set `sz n` of admissible certificates on `n`-node
   instances. Soundness/strong soundness are proved for *all* labellings (stronger). Constant size =
   finite certificate type (`L1` has 4 values; Lemma 4.2's certificates have ports in `{0,1}` on
   cycles). The counter LCP's honest certificates are `< 5(2N+1)`, i.e. `O(log n)` bits.
7. **Graph classes** are predicates on `(V, G)`. Theorem 4.1's `H₁` ("δ(G) = 1") contains
   non-bipartite graphs; the paper's promise problems need `H ⊆ G(2-col)` (v1 §2.5), so we use
   `H41 = bipartite ∩ (H₁ ∪ H₂)`. Even cycles: graphs isomorphic to `C_{2n}`, `n ≥ 2`.
8. **`k-col`** is defined in v1 with colours `{0,…,k}` (k+1 colours) — a typo; we use `Fin k`
   (R3, not a statement-level issue for the formalized results).
9. **Strong soundness** is the paper's *strong promise soundness* (`StronglySound`, only on
   non-bipartite graphs). All our positive results prove the stronger `StronglySoundAll` (every graph,
   every labelling).

## Lemma 3.2

10. Formalized for any view projection retaining `N` (identity: id-aware algorithms; `View.anon`:
    anonymous). `V(D,n)` is represented by its edge relation `Compat` (yes-instance compatibility in
    instances of `H` with `≤ n` nodes); a pair `μ, μ` is a loop, which makes `V(D,n)` non-colourable
    (the paper explicitly allows loops). No discrepancy with the statement. The paper's proof sketch
    has a slip ("proper 2-coloring" for `k`-coloring).

## Theorem 4.1 / Lemma 4.1 (δ = 1)

11. **Rule 2(b) ambiguity.** "For all `w ∈ N(v) \ {u}`, `ℓ(w) = β ∈ {0,1}`": we read `β` as one
    colour for all such `w` (the completeness part suggests this). With the literal per-neighbour
    reading the decoder is not even sound (`literalLCP_not_sound`: 5-cycle plus pendant). Rule R3:
    intent recoverable → ⚠️-level at most; the theorem holds with the uniform reading.
12. **Proof gap (strong soundness).** "Since C is odd, then u ∈ V(C)" is not an argument. Repaired by
    an explicit 2-colouring of the accepting nodes (`pot`). → 🛠️.
13. **Hiding instances.** Fig. 4's 5-cycle in `V(D,4)` contains an edge between the views of node 3
    in `I₁` and node 4 in `I₂`, which is realisable only with a triangle (`fig4_edge_not_compatible`).
    We use three labellings of `P₆ ⊔ K₂` (8 nodes, all of minimum degree 1). → 🛠️ (figure inside a
    proof).
14. **Theorem 4.1 is proved with the Lemma 4.1 LCP alone**: it is complete on *all* bipartite graphs
    (including even cycles), strongly sound everywhere, and hiding through `P₆ ⊔ K₂ ∈ H₁`. The paper
    combines two strategies; since hiding needs one hard instance, one suffices.

## Lemma 4.2 (even cycles; v1, informal in the BA)

15. **Decoder format.** Entry `i` of a certificate is `(here = i, there, colour)`; a node accepts iff
    degree 2, its entries describe its two edges (`here`, `there` = the actual remote port), the
    colours differ, and each neighbour's entry for the shared edge is `(there, here, same colour)`.
    The paper's "ℓ(v₁) contains edge p₁p₂ and colour c₁" is made precise in this (strict) way.
16. **Hiding.** The paper's odd cycle (Fig. 6) mixes views of a `C₄` and a `C₆`; in its own model the
    views contain `N = poly(n)`, which differs between the two. We use one `C₄` with
    reflection-symmetric ports: adjacent nodes 0 and 1 have equal anonymous views. → 🛠️.
17. **Strong soundness** proved via "odd closed walk ⇒ odd cycle" (`exists_odd_cycle`) and colour
    alternation along a cycle (the paper's argument, made precise).

## Theorem 4.2 (false) — decides the verdict

18. **Statement formalized** (`BATheorem42`) for `r = 1`, with the hypotheses on the special graph
    *strengthened* (strictly increasing distances in "forgetful", connected (v1 adds this), not
    2-regular-connected instead of "not an even cycle", `minDegree ≠ 1`), so the formal statement is
    implied by the paper's and its refutation refutes the paper's. Hiding in the statement is against
    all (id-aware) algorithms; the refuting LCP is anonymous, so the anonymous reading is refuted too.
19. **Counterexample** (`baTheorem42_false`): `H` = all bipartite graphs; the counter LCP. It also
    refutes v1 Theorem 1.5 (order-invariant; an anonymous decoder is order-invariant) and v3's
    corrected Theorems 2(1), 3(1), 4 (`v3Theorem4_false`, class `{θ(5,5,5)}`; v3 Definition 22 of
    forgetfulness checked). Not a modelling artefact: the counterexample only uses that nodes know
    `N ≥ n` (the paper's model; the paper's own Lemma 3.2 needs it), certificates of `O(log n)` bits,
    and hiding against every algorithm. Robust to stricter readings of "hiding": the hard instance is
    `θ(5,5,5)` itself (so it works for the class `{θ(5,5,5)}`, and under a per-graph reading), and
    against anonymous extractors the shift argument works with *fixed* ports and identifiers, since
    the anonymous views of node 2 at `t` and node 1 at `t+1` coincide. → R5: headline, 🚨.
20. **Where the proof fails.** (a) v1 §5.2 restricts `H` to its forgetful members "without
    restriction"; false for hiding (`baTheorem42Anon_false`, constant-size anonymous LCP of Lemma
    4.1). (b) Lemma 5.3 (v3 Lemma 21) needs `|V(W)| ≤ √(N/Δʳ)`; the proof of Theorem 1.5 never
    checks it, and for the counter LCP every odd cycle of `V(D,n)` has length `≥ M > 2N`.
21. **Definition of `r`-forgetful (BA/v1).** As written ("for every `w ∈ Nʳ(u)`, `dist(vᵢ, w)` is
    increasing") it is unsatisfiable for `r ≥ 2` in any graph with an edge (take `w = v₁`)
    (`not_isForgetful_of_two_le`). Typo-level (R3, v3 Definition 22 fixes it). For `r = 1` both
    definitions are satisfied by `θ(5,5,5)`. (v3 Definition 22 itself has a slip: it writes
    `dist(vᵢ, u) = d + i + 1`, which fails already at `i = 0` for a neighbour `w` of `u` with
    `d = 1`; `IsForgetfulV3` uses the evident intent `dist(vᵢ, w) = d + i + 1`. In that reading the
    1-forgetful condition only asks for a neighbour `v₁ ≠ u` of `v` not adjacent to `u`, which
    `θ(5,5,5)` has.)
22. **v1 Theorem 6.3** (constant-size certificates, non-anonymous, bounded degree) is not addressed:
    our counter LCP has logarithmic certificates and we prove hiding of the constant-size Lemma 4.1
    LCP only against anonymous algorithms. Its proof relies on Theorem 1.5, so it is unestablished.

## Theorem 4.3 (shatter points)

23. **Decoder formalized** (`shatterRule`) with rules 1, 2(a–c), 3(a–c); out-of-range component
    numbers make the colour check fail (stricter than the paper, harmless for the counterexample).
24. **The decoder is not strongly sound** (`shatterLCP_not_stronglySound`): 6-node graph, accepted
    5-cycle. Statement-level for the paper's protocol claim (R1: correctness claim about the paper's
    protocol), but the theorem is existential and true (R5) → ❌-level for this item.
25. **Statement proved** (`theorem_4_3`) with the counter LCP (hiding on `P₆`, which has a shatter
    point; `O(log n) ⊆ O(min{Δ²,n} + log n)`) and, anonymously with constant size, the Lemma 4.1 LCP.
    Shatter point = `∃ v`, two vertices outside `N[v]` not connected in `G − N[v]`.

## Theorem 4.4 (watermelons)

26. **Decoder formalized** (`watermelonRule`) with format checks (`id₁ < id₂`, `c₁ ≠ c₂`), rules 1,
    2(a–d), 3(a–c). Rule 2(b)'s garbled index ("p^w_{i2}") read as "some entry `i` of `w` records
    `prt(u,{u,w})`"; 2(d) "singleton" as "all matching colours equal" (non-emptiness follows from
    2(b) here).
27. **The decoder is not sound** (`watermelonLCP_not_sound`): all nodes of a 5-cycle accept. → ❌-level
    item (protocol claim), statement true. The rule refuted is the printed one ("`p^w_i = prt(u,{u,w})`
    for some `i`", rendered from v1 p. 28); binding the endpoint to the entry `i = prt(w,{u,w})` (which
    it sees) looks like the intended repair, but we did not verify it. Borderline R3; it does not
    affect the verdict, which Theorem 4.2 decides.
28. **Statement proved** (`theorem_4_4`) for every class of bipartite graphs containing `θ(5,5,5)`
    (a watermelon with three paths of length 5); the watermelon class itself is not defined formally.

## Other

29. **v3 Theorem 1** ("for any class `G` of bipartite graphs with `G ∩ H ≠ ∅`") is false for
    `G = {P₃}` (`v3Theorem1_false`). Not a BA statement; recorded for completeness.
30. Theorem 4.1's "constant-size certificates" for the cycle part rely on ports being in `{0,1}`;
    our Lemma 4.2 certificates are pairs of `(ℕ, ℕ, Bool)` entries whose accepted values are bounded.

## Verdict calibration

Worst item: Theorem 4.2 false (items 18–20), a headline result (abstract: "we prove that there are
no strong and hiding LCPs for 2-coloring in general, regardless of certificate size"), without R2–R4
excuses: the counterexample satisfies the paper's model (nodes know `N`), the hypotheses (even the
strengthened ones and v3's corrected class conditions), and uses no degenerate instance → 🚨.
