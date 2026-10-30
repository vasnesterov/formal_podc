# Differences between the formalization and the paper

Paper: Bousquet, Feuilloley, Zeitoun, *Brief Announcement: Global certification via perfect hashing*, PODC 2024
(HAL hal-04467834v2).

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Implicit assumption `M(n) ≥ n` (Theorems 3, 4).** The definition of a scheme says `P(G)` iff for every
   identifier assignment there is an accepted certificate. If `M(n) < n`, no assignment exists, so every
   `n`-vertex graph would have to satisfy `P`. Theorem 3 is then false: `theorem_3_false_of_small_range` shows
   that `M(3) < 3` rules out every scheme for bipartiteness. We assume `∀ n, n ≤ M n` throughout.
   **R4** (identifiers must exist; this is a standard convention that holds in all uses, and the paper's
   standard case is `M = n^c`). → ⚠️
2. **Theorem 7, degenerate parameters.** As stated (`k ≤ ℓ`), it fails for `k = ℓ = 1`: the size
   `⌈1·e·log 1⌉ = 0` in any base, and the empty family is not perfect (`theorem_7_false_l_one`). It also fails
   for `k = 0 < ℓ` (no functions into `∅`). **R2** (degenerate). We prove it for `1 ≤ k ≤ ℓ`, `ℓ ≥ 2`
   (`theorem_7`). The scheme also needs the cases `n = 0` and `n = M(n)`; there `exists_hashList` uses the
   family `{id}`. → ⚠️
3. **Theorem 7, "has size" vs "has size at most".** Read literally (a *set* of exactly `⌈k e^k log ℓ⌉`
   functions), it fails for `k = ℓ = 2`: the bound is 11 (`ln`) or 15 (`log₂`), but only 4 functions exist
   (`theorem_7_exact_size_false`). The intent "at most" is evident (the paper uses only the upper bound
   `log |H_{k,ℓ}| = O(k + log log ℓ)`). **R3**. → ⚠️
4. **Base of `log` in Theorem 7.** The paper leaves the base unspecified. We prove the bound with `ln` (the
   stronger statement, Mehlhorn's form) and derive the `log₂` version
   (`Cslib.exists_isPerfectHashFamily_card_le_logb`). No issue.

Theorem 7 is a cited numbered theorem, so items 2–3 count as statements, but they are excused. Worst label:
⚠️ Minor statement issues. Borderline call: none of the items changes the asymptotic content of
Theorems 3/4 or the refutation of Conjecture 1.

## Modelling choices

5. **Certificates.** The paper fixes, for each `n`, an arbitrary set `C` of size `2^{s(n)}`. We take
   `C = {0, …, 2^{s(n)} − 1} ⊆ ℕ` (`s(n)`-bit strings) for all `n`. So the verifier cannot learn `n` from which
   set the certificate belongs to, and must decode `n` from the bits. This is a special case of the paper's
   definition, hence stronger for upper bounds; `IsGlobalScheme.toAbstract` and `theorem_4_paper_def` give the
   paper's literal form (`IsGlobalSchemeAbstract`).
6. **Encoding of `n`.** The paper says the verifier "reads `n` in the global certificate" without saying how
   a fixed-length certificate can be parsed. We write `n` in unary (`n + 1` bits, `decodeN`), which is
   `O(n)` and absorbed in the bound. (A self-delimiting binary code would cost `O(log n)`; either is fine.)
7. **Encoding of `h` and `L`.** `h` is stored as its index `idx < |L_n|` in a list `fam M n` (the family
   of Theorem 7 for `(n, M(n))`, chosen by `Classical.choose`). `L` is stored as a number `code < n'^n`
   (base-`n'` digits, `finFunctionFinEquiv`). The vertices of `H` are numbered by `Fintype.equivFin` (`0..n'−1`
   instead of the paper's `1..n'`). Size `certSize = n + 1 + ⌈log₂ |L_n|⌉ + n⌈log₂ n'⌉`.
8. **Verifier on malformed certificates.** A digit `≥ n'` (only possible when `n' = 0`) decodes to "no colour"
   and the node rejects. A node also rejects if its *own* colour is undefined. The paper's verifier only checks
   the neighbour pairs; for `n' ≥ 1` the two agree. For `n' = 0` and an isolated vertex the paper's literal
   verifier would accept although there is no homomorphism. This is harmless, since then there is no list
   `L` to write.
9. **Neighbourhood view.** The view contains the *set* `{Id v | v ∈ N(u)}`, exactly as in Definition 5, as
   a `Set ℕ` (no finiteness or decidability needed). The verifier is an arbitrary `Prop`-valued predicate, as
   in the paper ("does not have to be decidable").
10. **Asymptotics.** `O(n log n' + log log M)` is made explicit: `s(n) ≤ 10 (n log₂ n' + log₂ log₂ M(n))` for
    all `n ≥ 1`. The constant 10 is uniform in `H` and `M`. For `n' ≤ 1` the paper's bound degenerates to
    `O(log log M)`, and our scheme for that case (`isGlobalScheme_small`) uses 0 bits: the property is then
    "no edges (and `V = ∅` if `H` is empty)", which the view decides locally. For `n = 0` the bound
    `log₂ log₂ M(0)` can be `0` while the scheme still needs `1` bit, so the bound is stated for `n ≥ 1`.
11. **Theorem 3** is stated for `Bipartite := G.Colorable 2` (Mathlib), definitionally "homomorphism to `K₂`".
12. **Conjecture 1.** Formalized for `M(n) = n^c` with natural `c ≥ 1` (the paper: polynomial `M`). The
    statement refuted: "there is `ε > 0` such that every scheme has size `≥ ε n ln n` for infinitely many
    `n`" (`conjecture_1_false`). This is the weakest reading of the lower bound `Ω(n log n)`, so its negation
    also refutes the "for all large `n`" reading. The matching lower bound `Ω(n)` (Theorem 2, from [3]) is not formalized, so
    "the optimum is `Θ(n)`" is only formalized as its upper half.

## Not formalized

* Theorem 2 (Feuilloley–Hirvonen bounds; cited, not proved in the paper).
* Section 4 (CSP generalization; informal, no precise statement).

## Proof gaps

None beyond item 6, and one degenerate slip in the size count: the paper bounds the certificate by
`O(n log n') + O(n + log log M)` and absorbs the `O(n)` (for `h`, and for `n` itself) into `O(n log n')`.
This needs `n' ≥ 2`; for `n' ≤ 1` the claimed bound is `O(log log M)`, which the paper's scheme does not meet
(e.g. `M(n) = n`). A trivial 0-bit scheme covers that case (`isGlobalScheme_small`, item 10). **R2**
(degenerate `H`). Otherwise the paper's proof of Theorem 4 is complete and correct up to the encoding
details. Soundness indeed needs no check that `h` is perfect (`sound` holds even for non-injective labellings).
