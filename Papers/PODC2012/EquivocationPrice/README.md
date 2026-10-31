# The Price of Equivocation in Byzantine Agreement — PODC 2012

Alexander Jaffe, Thomas Moscibroda, Siddhartha Sen. *On the Price of Equivocation in Byzantine Agreement.*
PODC 2012. DOI [10.1145/2332432.2332491](https://doi.org/10.1145/2332432.2332491). Formalized version: the
10-page proceedings version (no arXiv version; the "full version" with the deferred proofs was not available).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main results hold. These are the equivalence of `f`-tolerance and
`(n−2f)`-disjointness (Theorem 2), the reduction behind co-NP-hardness (Theorem 1) and the tight bounds
`Tₙ(h) = Θ(n³/h²)` (Theorems 3, 5, 7). The exact formula of Theorem 13 for `Uₙ(h)` lacks a ceiling and is wrong
when `n − h` is odd. Theorem 2 fails only for `n = 0`. Several proofs are missing or need repair.

## Mistakes in the paper

* **Theorem 13 is off by `h²/2` when `n ≢ h (mod 2)`.** The paper claims `Uₙ(h) = C(n,3) − ((n−h)/2)·h² + 1`.
  Its proof minimises `abc` over integers `a, b, c ≥ h` with `a + b + c ≥ (n+3h)/2`. It only treats
  `n ≡ h (mod 2)` and says the other case "is proved similarly". When `n − h` is odd, `c` must be at least
  `⌈(n−h)/2⌉`, so the correct value is `C(n,3) − h²⌈(n−h)/2⌉ + 1`. That is `h²/2` below the paper's formula,
  which for odd `h` is not even an integer. Example: `U₄(1) = 3` (any three of the four triples on 4 vertices
  form a 1-disjoint hypergraph, two do not), while the formula gives `3.5`. We prove the corrected formula for
  all `h ≤ n/3`. We count this as a missing rounding with evident intent; it is a borderline call, see
  [differencies.md](differencies.md). (`theorem_13`, `theorem_13_false`, `U_four_one`)
* **Proposition 15 (inside the proof of Theorem 13) misidentifies a maximum as a minimum.** Its second bullet
  says the minimum of `g(a,b) = ab((n+3h)/2 − a − b)` along each face of the triangle is `(n+h)²h/16`. Along a
  face, `g` is a concave quadratic, so that value is the face *maximum*; the face minimum is at the endpoints.
  Example: `n = 4`, `h = 1`, `(a,b) = (1,1)` gives `g = 3/2 < 25/16`. The final answer survives because the
  vertices are compared too. We replace the calculus by `abc ≥ h²(a+b+c−2h)` for `a, b, c ≥ h`, a two-line
  integer argument. (`prop_15_face_false`, `mul_mul_ge`)
* **Theorem 7's proof needs expanders that are not known to exist (statement true).** The proof uses
  Ramanujan graphs of degree `d = Θ(n/h)` for every `n`. It justifies them by Friedman's theorem, which is
  about fixed `d` as `n → ∞`; here `d` grows unless `h = Θ(n)`. The degree the proof requires,
  `d > 6n/(k²h) ≈ 210·n/h`, also exceeds `n − 1` when `h ≲ 210`. The bound itself is true. We prove
  `Tₙ(h)·h² ≤ n³` for all `1 ≤ h ≤ n/3` by the counting argument the paper mentions but does not give. The
  expander route (Lemmas 8, 9, Claim 10, all algebraically correct) is formalized with the expander mixing
  lemma as a hypothesis. (`theorem_7`, `T_le`, `hDisjoint_lift`)
* **Missing proofs, supplied here.**
  * Theorem 2 (deferred to the full version). The (⇐) direction is the paper's Figure 1 and needs no hypothesis
    on `f`. The (⇒) direction shrinks a valid colouring to sizes `p, q, c ≥ h` with `p + q + c = 2n − 3f` and
    pads it with fresh faulty vertices. This is exactly where `f ≥ n/3` is needed. The theorem fails only for
    `n = 0`, where `f`-tolerance holds vacuously. (`theorem_2`, `theorem_2_card_zero`)
  * Lemma 4 (deferred). It also holds for odd `n`. (`lemma_4`)
* **Imprecisions.**
  * The proof of Theorem 3 silently assumes `3 ∣ n`. The statement is true for every `n`: we prove the exact bound
    for `n = 3k`, and `|E| ≥ 3n/4 − 2` for all `n` and all `h ≤ n/3`.
  * Lemma 6 needs `n` even. Theorem 5 applies it with `|B| = (n−h)/2`, which need not be an integer. We use
    `⌈(n−h)/2⌉` and get `n(n−1)(n−2) ≤ 24h²|E|` for `1 ≤ h ≤ n/6`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Purely combinatorial, like the paper's own results. A system of `n` processors with 3-party partial broadcast
  channels is a 3-uniform hypergraph `E : Finset (Finset V)` on a finite type `V`.
* `FTolerant E f` (Definition 1) and `HDisjoint E h` (Definition 2) are transcribed literally, with `h, f ∈ ℕ`.
* `Tₙ(h)` and `Uₙ(h)` (Definitions 3 and 7) are defined as `sInf` over hypergraphs on `Fin n`.
* The paper's setting is Byzantine agreement among `n = 2f + h` processors, at most `f` of them Byzantine;
  for [38] a synchronous, `(2f+1)`-connected network; the asynchronous and
  partially synchronous models are discussed through [9], [11]. None of this is modelled:
  Byzantine agreement itself is not formalized. The paper takes "BA is possible in `H` iff `H` is `f`-tolerant
  (with `(2f+1)`-connectivity)" from Ravikant et al. [38], and this is not formalized. Theorem 1 is therefore
  formalized as the correctness of the reduction from balanced bipartite independent set. Via Theorem 2 it is
  stated both for `t`-disjointness and for `f`-tolerance with `n' = 2f + t`.
* Asymptotic statements become explicit inequalities valid for all `n`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1, 2, 3, 7 | `FTolerant`, `HDisjoint`, `T`, `U` | `Defs.lean` |
| Theorem 2 | `theorem_2` (`n ≥ 1`), `theorem_2_card_zero` (fails for `n = 0`) | `Equivalence.lean` |
| Theorem 1 (reduction) | `theorem_1_reduction`, `theorem_1_reduction_fTolerant` | `Hardness.lean` |
| Definition 4 + overcounting | `proj`, `sum_card_proj_le` | `Projection.lean` |
| Lemma 4 | `lemma_4` | `Bisection.lean` |
| Theorem 3 | `theorem_3`, `theorem_3'` (`n = 3k`), `theorem_3_asymptotic` (`3n ≤ 4|E| + 8`) | `LowerLinear.lean` |
| Lemma 6 | `lemma_6_general`, `lemma_6` | `LowerSublinear.lean` |
| Theorem 5 | `theorem_5`, `theorem_5_T` (`n(n−1)(n−2) ≤ 24h²·Tₙ(h)`, `1 ≤ h ≤ n/6`) | `LowerSublinear.lean` |
| Theorem 7 (via counting, constant 1) | `theorem_7`, `T_le` (`Tₙ(h)·h² ≤ n³`, `1 ≤ h ≤ n/3`) | `UpperBound.lean` |
| Lemma 8, Lemma 9, Claim 10 (given the EML) | `lemma_8`, `lemma_9`, `claim_10` | `Expander.lean` |
| Definition 6, Theorem 7 via expanders (given the EML) | `lift`, `hDisjoint_lift`, `T_le_of_expander` | `Expander.lean` |
| Claim 14 (integer form) | `mul_mul_ge`, `card_crossing_ge` | `Sufficiency.lean` |
| Proposition 15, 2nd bullet (false) | `prop_15_face_false` | `Sufficiency.lean` |
| Theorem 13 (corrected / as stated) | `theorem_13` / `theorem_13_false`, `U_four_one` | `Sufficiency.lean` |

**Not formalized.** The expander mixing lemma and the existence of (near-)Ramanujan graphs (Lemmas 8, 9 and
Claim 10 take the EML's conclusion `MixingBound` as a hypothesis); Theorem 11 (explicit construction); the link between `f`-tolerance and Byzantine agreement ([38], [9]);
NP-completeness of BBIS, co-NP membership and polynomial running time; the comparison with `f(n,3)` in Section 2.1.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the complete hypergraph is `h`-disjoint for `h ≥ 1` (`hDisjoint_complete`), Theorem 13's
extremal hypergraph is not (`exists_not_hDisjoint`), and the complete graph satisfies the `MixingBound`
hypothesis (`mixingBound_top`). Everything is self-contained on top of Mathlib.
CSLib candidates: `lemma_4` / `exists_subsum_eq` (`Bisection.lean`), `card_filter_inter_card_eq_one_le`
(`Projection.lean`), `exists_hitting` (`UpperBound.lean`).
