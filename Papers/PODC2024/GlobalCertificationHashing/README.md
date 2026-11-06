# Global certification via perfect hashing — PODC 2024

Nicolas Bousquet, Laurent Feuilloley, Sébastien Zeitoun. *Brief Announcement: Global certification via perfect
hashing.* PODC 2024. DOI [10.1145/3662158.3662781](https://doi.org/10.1145/3662158.3662781). Formalized version:
HAL [hal-04467834v2](https://hal.science/hal-04467834v2) (same text as the proceedings brief announcement).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✏️ Slip.** Theorem 4 (homomorphism to `H` with `O(n log n' + log log M)` bits) and Theorem 3 (bipartiteness with
`O(n + log log M)` bits) are proved, with explicit constant 10, uniformly in `H` and `M`, so Conjecture 1 of
Feuilloley–Hirvonen is indeed false. The only mistakes are the implied assumption `M(n) ≥ n`, degenerate cases, and the
words "has size" in the cited Theorem 7, which should say "at most".

## Mistakes in the paper

### ✏️ Slips
- Theorems 3 and 4, implied assumption `M(n) ≥ n`: the definition of a scheme asks that `G` satisfies `P` iff *for every
  identifier assignment* some certificate is accepted. If `M(n) < n`, no injective identifier assignment into
  `{0,…,M(n)−1}` exists, so the right-hand side holds trivially and every `n`-vertex graph would have to satisfy `P`. For
  example, with `M(3) < 3` the triangle would have to be bipartite, and no scheme for bipartiteness exists at all, of any
  size (`theorem_3_false_of_small_range`). Every reader makes this assumption (identifiers must exist); we assume
  `M(n) ≥ n` too, and then both theorems hold.
- Theorem 7 (perfect hash families, cited from Mehlhorn), degenerate parameters: the claimed `(k, ℓ)`-perfect hash family
  "which has size `⌈k e^k log ℓ⌉`" (for all `k ≤ ℓ`) does not exist for `k = ℓ = 1`: the bound is `⌈e · log 1⌉ = 0` in any
  base, but the empty family is not perfect for `S = {0}` (`theorem_7_false_l_one`). The case `k = 0 < ℓ` is just as
  degenerate: no function into the empty set exists.
- Theorem 7, "has size": read as "exactly this size" it fails already for `k = ℓ = 2`: the bound is `⌈2e² ln 2⌉ = 11` (`15`
  with `log₂`), but there are only `4` functions `{0,1} → {0,1}` (`theorem_7_exact_size_false`). The paper uses the result
  only as an upper bound. We prove the intended statement: size **at most** `⌈k e^k ln ℓ⌉` for `1 ≤ k ≤ ℓ`, `ℓ ≥ 2` (hence
  also with `log₂`), by the counting argument (`theorem_7`); it gives Theorems 3 and 4. The trivial family `{id}` covers
  `n = M(n)` (using `n ≤ M(n)`).
- Proof of Theorem 4, size count: the `O(n)` bits for `h` are absorbed into `O(n log n')`, which needs `n' ≥ 2`; for
  `n' ≤ 1` a trivial 0-bit scheme is used instead (`isGlobalScheme_small`).

### Typos
- The proof in Section 3 is labelled "Proof of Theorem 3" but proves Theorem 4.
- In Theorem 4, `n' = |V(H')|` should be `|V(H)|`.
- The verifier "reads `n` in the global certificate", but the certificate is a fixed-length bit string, so `n`
  must be written in a self-delimiting way. This is not discussed; unary `n` costs `n + 1 = O(n)` bits, which we use.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Global certification exactly as in Section 2 (`Model.lean`). The graphs are finite simple graphs on any
  `Fintype V`, with `n = |V|`. Identifiers are given by an injective `Id : V → ℕ` with values `< M(n)`. Node `u`
  sees `Id u`, the *set* `Id '' N(u)` of its neighbours' identifiers, and the global certificate. The verifier
  is an arbitrary predicate (no computability, as in the paper). A scheme of size `s` and range `M` satisfies
  `P V G ↔ ∀ Id, ∃ c < 2^{s(n)}, every node accepts` (`IsGlobalScheme`).
* Certificates of `s(n)` bits are numbers `c < 2^{s(n)}`. This fixes the paper's "set `C` of size `2^{s(n)}`"
  to `{0,…,2^{s(n)}−1}` for every `n`, so the verifier gets no information about `n` from the certificate
  for free. This is stronger than the paper's definition, where `C` may depend on `n` arbitrarily.
  `IsGlobalScheme.toAbstract` / `theorem_4_paper_def` give the paper's literal definition.
* There is no distributed execution to model: verification is one local predicate per node (radius 1). There
  are no failures and no randomness. The perfect hash family exists by a counting argument; the verifier
  picks it by choice.
* The scheme (`Scheme.lean`) is the paper's: certificate `1ⁿ0 · idx · code`, with `n` in unary, `idx` the
  index of a hash function in the `(n, M(n))` family, and `code < n'^n` the list `L` in base `n'`. A node
  accepts iff its colour `L[h(Id u)]` is a vertex of `H` adjacent to `L[h(Id v)]` for every neighbour `v`.
  Soundness holds for *any* labelling, even a non-injective one (`sound`): as the paper observes, perfection
  of `h` is not checked.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4 (`O(n log n' + log log M)`, explicitly `≤ 10(n log₂ n' + log₂ log₂ M(n))`, `n ≥ 1`) | `theorem_4` (paper's literal definition: `theorem_4_paper_def`) | `Main.lean` |
| Theorem 3 (bipartiteness, `≤ 10(n + log₂ log₂ M(n))`) | `theorem_3` | `Main.lean` |
| `k`-colourability (Section 1, special case of Theorem 4) | `colorable_scheme` | `Main.lean` |
| Conjecture 1 is false (`M = n^c`: a scheme of size `O(n)`, so no scheme lower bound `ε n ln n` holds, not even for infinitely many `n`) | `theorem_3_poly`, `conjecture_1_false` | `Main.lean` |
| Correctness of the scheme (completeness / soundness) | `complete`, `sound`, `isGlobalScheme_verifier` | `Scheme.lean` |
| Size of the scheme | `certSize`, `certSize_le` | `Scheme.lean`, `Main.lean` |
| Theorem 7 (corrected: size `≤ ⌈k e^k ln ℓ⌉`, `1 ≤ k ≤ ℓ`, `ℓ ≥ 2`) | `theorem_7` (= `Cslib.exists_isPerfectHashFamily_card_le`; `log₂`: `..._logb`) | `Hashing.lean`, `Podc/Foundations/Combinatorics/PerfectHash.lean` |
| Theorem 7 literal, counterexamples | `theorem_7_false_l_one`, `theorem_7_exact_size_false` | `Hashing.lean` |
| Implicit `M(n) ≥ n` | `theorem_3_false_of_small_range` | `Main.lean` |

**Not formalized.** The lower bound `Ω(n + log log M)` of Theorem 2 (cited from Feuilloley–Hirvonen, DISC 2018),
so the optimality claim "`Θ(n)` for polynomial `M`" is only formalized as the upper bound. Also not
formalized: the informal Section 4 (general CSPs), which states no precise claim.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
hypothesis `n ≤ M n` is satisfiable (e.g. `M = id` or `M n = n^c`, used in `conjecture_1_false`). The scheme
definition is not vacuous: `theorem_3_false_of_small_range` shows it can fail. The perfect hash family lemma is
staged in `Podc/Foundations/Combinatorics/PerfectHash.lean` (CSLib candidate).
