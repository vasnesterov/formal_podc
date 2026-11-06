# Differences between the formalization and the paper

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012
(10-page proceedings version; the "full version" with the deferred proofs was not available).

## Statement-level issues

1. **Theorem 13 (`Uₙ(h)`) is wrong for `n ≢ h (mod 2)`.** The paper states
   `Uₙ(h) = C(n,3) − ((n−h)/2)·h² + 1` for `h ≤ n/3` (also in the introduction). Claim 14 minimises
   `abc` over *integers* `a, b, c ≥ h` with `a + b + c ≥ (n + 3h)/2`; its proof treats only
   `n ≡ h (mod 2)` ("the second case is proved similarly"). For `n ≢ h` the minimum is
   `h²·⌈(n−h)/2⌉`, so the correct value is `C(n,3) − h²⌈(n−h)/2⌉ + 1` (`theorem_13`), which is
   smaller than the displayed one by `h²/2` (`theorem_13_false`). Example: `U₄(1) = 3`, while the
   formula gives `3.5` (`U_four_one`). For odd `h` the displayed value is not even an integer,
   although `Uₙ(h)` is defined as a minimum integer.
   🔧. The intended version follows from the paper's own Claim 14, which is about integers with
   `a + b + c ≥ (n+3h)/2`, and the fix is a rounding symbol. The abstract only claims asymptotically
   tight bounds; `Uₙ` is "our final result" of the introduction. The paper's proof does not compute the
   ceiling: it explicitly restricts to `n ≡ h (mod 2)` and defers the other parity as "proved
   similarly". Carrying out that case with the paper's own argument (integer `c ≥ (n+3h)/2 − 2h`)
   gives exactly `c = ⌈(n−h)/2⌉`, with the same extremal configuration (two classes of size `h`,
   the third as small as allowed). The displayed value is not an integer for odd `h` and odd `n − h`,
   while `Uₙ(h)` is defined as an integer. So the statement is wrong only in the parity case the proof
   sets aside; the extremal structure and every asymptotic consequence are unchanged.
2. **Theorem 2 fails for `n = 0`.** With no vertices there are no `S ≠ T`, so every hypergraph is
   `f`-tolerant, but no hypergraph is `(−2f)`-disjoint (`theorem_2_card_zero`). Degenerate (✏️);
   we assume `n ≥ 1`.
3. **Theorem 2 for `f ≥ n/2`.** Then `h = n − 2f ≤ 0`. We use natural-number subtraction
   (`h = 0` when `2f ≥ n`). Both sides are false for every `n ≥ 1` in this range, with the paper's
   integer `h` as with ours (`not_fTolerant_of_le_two_mul`, `not_hDisjoint_zero`; for negative `h`
   the colouring `A = B = ∅`, `C = V` is valid as well), so the equivalence is unaffected.

## Proof-level issues (statements true)

4. **Proposition 15, second bullet, is false** (claim inside the proof of Claim 14, inside the
   proof of Theorem 13; 🔧). It says the minimum of
   `g(a,b) = ab((n+3h)/2 − a − b)` along the faces of the triangle `P` is `(n+h)²h/16`. Along
   each face `g` is a concave quadratic, and `(n+h)²h/16` is its *maximum* there; the minimum along
   a face is attained at its endpoints and equals `h²(n−h)/2`. Counterexample `n = 4, h = 1,
   (a,b) = (1,1)`: `g = 3/2 < 25/16` (`prop_15_face_false`). The final answer of Claim 14 is still
   right because the vertex values are also compared ("Comparison"); we replace the real-variable
   argument by the two-line integer inequality `abc ≥ h²(a+b+c−2h)` for `a,b,c ≥ h`
   (`mul_mul_ge`, `card_crossing_ge`).
5. **Theorem 2: proof deferred to the full version.** We supply one (`theorem_2`): (⇐) is the
   paper's Figure 1 (`A = S \ Z`, `B = T \ Z`, `C = S ∩ T`) and holds for every `f`; (⇒) shrinks
   a valid colouring to sizes `p, q, c ≥ h` with `p + q + c = 2n − 3f` and pads with fresh faulty
   vertices; this is where `f ≥ n/3` is used (`3h ≤ 2n − 3f ⇔ n ≤ 3f`).
6. **Lemma 4: proof deferred.** Supplied (`lemma_4`), via components and a sub-sum lemma; it holds
   also for odd `|U|` (bisection = parts `⌊|U|/2⌋`, `⌈|U|/2⌉`).
7. **Theorem 3 assumes `3 ∣ n` silently** (uses `|C| = n/3` and a sum over `C(n, n/3)`; the text
   says `|C| ≤ n/3` but uses equality). We prove the exact bound for `n = 3k`
   (`theorem_3`, `theorem_3'`: `|E| ≥ (n−1)(n−2)/(4n/3−2)`) and, for every `n` and `h ≤ n/3`,
   `|E| ≥ 3n/4 − 2` (`theorem_3_asymptotic`) as the precise form of `(3/4)n(1 − o(1))`.
   The statement of Theorem 3 (for every `h` with `h ≤ n/3`) is therefore true for every `n`; only
   the proof is restricted to `3 ∣ n`. This is a proof-level gap (repaired, 🔧), not a statement issue.
8. **Lemma 6 / Theorem 5: parity** (🔧). Lemma 6 uses `n/2`-sets (needs `n` even), and Theorem 5 applies
   it with `n' = n − h` and `|B| = n'/2`, not an integer when `n − h` is odd. We prove a general
   Lemma 6 for `(i, b)`-crossing graphs (`lemma_6_general`), the paper's form for even `n`
   (`lemma_6`), and Theorem 5 with `b = ⌈n'/2⌉`, in the explicit form
   `n(n−1)(n−2) ≤ 24h²|E|` for `1 ≤ h ≤ n/6` (`theorem_5`, `theorem_5_T`); the paper's
   arithmetic gives the slightly weaker `|E| ≥ 25n⁴/(864h²(n−2))`. Theorem 5 needs `h ≥ 1`
   (implicit in the paper).
9. **Theorem 7 (upper bound `Tₙ(h) = O(n³/h²)`): gap in the existence of the expanders** (🛠️).
   The paper builds `L(G)` from a near-Ramanujan graph `G` of degree `d = Θ(n/h)`. It asserts the
   existence of Ramanujan graphs "for every `n` and `d`" via Friedman's theorem, but Friedman's theorem
   is about *fixed* `d` as `n → ∞`, while here `d` grows with `n` unless `h = Θ(n)` (spectral bounds
   for random regular graphs of growing degree came later). Moreover the required degree
   `d > 6n/(k²h) ≈ 210·n/h` (`k = (√2−1)/√6`) exceeds `n − 1` for `h ≲ 210`, so for such `h` no such
   graph exists (the bound is then trivially true, as the complete hypergraph has `≤ n³/6` edges).
   The theorem is true: we prove `Tₙ(h)·h² ≤ n³` for all `1 ≤ h ≤ n/3` by the counting argument the
   paper mentions but does not give (a greedy hitting set for the `≤ 4ⁿ` crossing families, each
   of size `≥ h²n/3`; `theorem_7`, `T_le`). The paper's own route is formalized conditionally:
   Lemmas 8 and 9 and Claim 10 hold under the *conclusion of the expander mixing lemma*, taken as a
   hypothesis `MixingBound G d λ` (the EML itself and the spectral definition of an
   `(n,d,λ)`-expander are not formalized), giving `HDisjoint (lift G) h` (`hDisjoint_lift`) and
   `Tₙ(h) ≤ n·C(d,2)` for a `d`-regular such `G` (`T_le_of_expander`). Small differences: Lemma 8
   needs `T ≠ ∅`; Lemma 9 needs `A, B ≠ ∅` and pairwise disjointness, but not `a ≤ b ≤ c` (the
   ordering is used only in Claim 10); Claim 10 holds with `a + b + c ≥ (n+3h)/2` (the paper writes
   `=`). The algebra of Lemmas 8, 9 and Claim 10 is correct. Non-vacuity: the complete graph
   satisfies `MixingBound` with `d = n − 1`, `λ = 1` (`mixingBound_top`).

## Modelling choices

- A 3-uniform hypergraph is a `Finset (Finset V)` of 3-sets over a `Fintype V` (`n = |V|`); the
  paper's ordered triple `(x, y, z) ∈ E` is the set `{x, y, z}` (its vertices are distinct
  wherever the paper uses it). The sufficiency number `Uₙ(h)` and `Tₙ(h)` are defined on `Fin n`.
- Definitions 1 and 2 are transcribed literally: `|A|+|B|+|C| ≥ (n+3h)/2` as
  `n + 3h ≤ 2(|A|+|B|+|C|)`, `|S| ≥ n − f` as `n ≤ |S| + f`, `Z ⊂ S ∪ T` strict. The paper writes
  `S, T, Z ⊂ V` and `A, B, C ⊂ V`; we allow all subsets. For `h ≥ 1` this makes no difference:
  the sets built in our proof of (⇒) have `|S|, |T| = n − f < n` and `|Z| ≤ f < n`, and (⇐) is
  only easier with fewer triples `S, T, Z`.
- `h` and `f` are natural numbers (see item 3).
- **Byzantine agreement is not modelled.** The paper's Theorem 2 is the purely combinatorial
  equivalence of `f`-tolerance and `(n−2f)`-disjointness; the statement "Byzantine agreement is
  possible in `H` iff `H` is `f`-tolerant (given `(2f+1)`-connectivity)" is cited from Ravikant et
  al. [38] (synchronous model) and Bracha–Toueg [9] (asynchronous), and is not formalized here.
  Accordingly Theorem 1 is formalized as the correctness of the reduction from balanced bipartite
  independent set (`theorem_1_reduction`, and through Theorem 2 `theorem_1_reduction_fTolerant`);
  NP-completeness of BBIS [3], co-NP membership and polynomial running time are not formalized.
  The reduction is proved for any `1 ≤ t ≤ |X|, |Y|` (the paper has `|X| = |Y| = n/2`).
- Asymptotic statements (`Θ`, `Ω`, `O`, `o(1)`) are replaced by explicit inequalities with
  explicit constants valid for all `n` (or all `n` divisible by 3, as indicated).

## Not formalized

- Theorem 11 (explicit construction for infinitely many `n`, via Cioabă–Murty expanders; its proof
  is a sketch: a fixed-degree sequence `nᵢ` must be matched with the degree `Θ(nᵢ/h(nᵢ))`), the
  expander mixing lemma itself, the existence of (near-)Ramanujan graphs, and the comparison
  statements of Section 2.1 (`Tₙ(1) ≥ f(n,3)`, `Tₙ(n/3) ≤ f(n,3)` with `f(n,3) = n(n−2)/3` from the
  literature), Section 1.2 (applications to other models).
