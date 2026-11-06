# Adjacency Labeling for Power-Law Graphs — PODC 2016

Casper Petersen, Noy Rotbart, Jakob Grue Simonsen, Christian Wulff-Nilsen. *Brief Announcement:
Near-Optimal Adjacency Labeling Scheme for Power-Law Graphs.* PODC 2016. Formalized version: full
version arXiv [1502.03971](https://arxiv.org/abs/1502.03971) v1; numbering follows it.

**Verdict: 🔧 Easy fix.** The checked results all hold once the paper's missing definitions are filled in the only
way that makes its proofs work: the upper bounds (Theorems 1 and 2), the lower bounds (Proposition 4 and Theorem 3)
and the properties of `P'_α` (Propositions 1–3). The normalising constant `C` is never defined, so we use
`C = 1/ζ(α)`; Proposition 4 is false only for `c` large compared to `n`, and the repairs of Proposition 3, the
Proposition 4 padding argument and the greedy construction of Theorem 3 are local. The experiments and the
threshold prediction were not checked.

## Mistakes in the paper

### ✏️ Slips
- Proposition 4 fails when `c` is large compared to `n`: for `n = 2`, `c = 100`, one bit suffices, but the claimed
  bound is `⌊√200/2⌋ = 7` (`prop4_false`). For `c ≥ (n-1)/2`, `S_{c,n}` is the family of all graphs, which have
  labels of about `n/2` bits, while `⌊√(cn)/2⌋` grows without bound in `c`. The intended regime (constant `c`,
  growing `n`) is fine, and we prove the bound for all `c < n` (`prop4`).
- Definition 2: the normalising constant `C` is never defined, and the proofs need `C·ζ(α) = 1`: Prop. 1's proof
  needs `C·ζ(α) ≥ 1`, and Thm 3's construction needs `C·ζ(α) ≤ 1`. This is an implied assumption (the standard
  normalisation of a power law); with `C = 1/ζ(α)` (`C`) all results hold. Thm 3's construction uses
  `Σ_{i ≤ i₁} ⌊Cn/i^α⌋ ≤ n`. With a small `C`, the class-size constraints of Definition 2 no longer bound the
  maximum degree by `O(n^{1/α})`, because the isolated vertices absorb the slack. With a large `C`, `P'_α` is empty
  for large `n` and the lower bound fails. Neither alternative was formalized.
- Definition 1 (`n / log n` with `log 1 = 0`) is meaningless for `n = 1`. Under the literal reading, with the Lean
  convention `x/0 = 0`, `P'_α ⊄ P_α` at `n = 1`. We require `k ≥ 1`, which is automatic for `n ≥ 2`.
- Prop. 1's proof defines `k' = ⌊n^{1/α}⌋` but the integral step needs `⌈n^{1/α}⌉`; with `⌈·⌉` the stated bound,
  including the `+3`, comes out exactly (`prop1`).
- Theorem 3, Phase 1 omits the requirement that the added pair be non-adjacent, so as written the loop does not
  terminate (`exists_maximal_fill`).
- Theorem 3 is claimed "for all `n`", but the construction needs `n` large; it is true for all large `n`
  (`theorem3_proper`, `theorem3`).

### Typos
- `i₁` must be the smallest *positive* such integer (`i = 0` qualifies trivially).
- "Moon's bound `⌊n/2⌋`" is for fixed-length labels. For labels of length *at most* `ℓ`, counting gives
  `⌊(n-1)/2⌋` (`moon`), which suffices for every use.
- The paper's `C'` is called a constant but depends on `n` through `i₁/n^{1/α}`, which stays bounded; ours does not
  depend on `n`.

## Proof gaps (statements true)

### 🔧 Proposition 3 (integral comparison in the wrong direction)
The proof uses `Σ_{i=k}^d i^{-α} ≤ ∫_k^d x^{-α}dx`, which misses the term `k^{-α}`, and `|V_i| ≤ Cn/i^α + 1` for
all `i`, which fails for `i = 2` (`+2`).

**Impact.** Statement true: `P'_α ⊆ P_α` holds with a larger constant (`prop3`).

**Repair.** The inclusion holds with `C'₀ = (C/(α-1)+8)^α + Cα/(α-1)` (`prop3`).

### 🔧 Theorem 3 (the greedy construction)
Phase 2 claims that after greedily adding edges between unprocessed vertices of `V'` "at most one vertex of `V'`
remains unprocessed", but the remaining unprocessed vertices form a *clique* and there can be several (targets 3,
3, 2 joined in the order `ab, ac, bc` leave `a, b` unprocessed).

**Impact.** Statement true (`theorem3_proper`, `theorem3`).

**Repair.** We replace each greedy loop by an edge-maximal graph (`exists_maximal_fill`). The remaining clique has
at most `i₁` vertices, so all of them are saturated by leaves (`bip_phase`). Parity is fixed in advance by
choosing `|V₁|` (`realize`).

### 🔧 Proposition 4 (padding argument)
The proof uses `n` both for the family size and for the embedded graph, so as written it covers only family sizes
of the form `⌊m²/c⌋`.

**Impact.** Statement true for all `c < n` (`prop4`).

**Repair.** Our proof embeds an arbitrary graph on `⌊√(cn)⌋ + 1` vertices directly into `n` vertices and applies
the counting bound `⌊(m-1)/2⌋` (`prop4`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Graphs are finite simple graphs on `Fin n`. `deg`, `|V_i| = numDeg G i`, `c`-sparse means
  `|E| ≤ cn` (`Sparse`), and `log n = ⌈log₂ n⌉` (`lg`, the number of bits of an identifier).
* An adjacency labeling scheme with `X`-bit labels for a family `F` of `n`-vertex graphs
  (`HasAdjLabeling n F X`) is a decoder fixed for the family. The decoder is an arbitrary relation on
  bit lists and may depend on `n`. Every `G ∈ F` must have labels of length `≤ X` such that the
  decoder decides adjacency of any two distinct vertices. Upper bounds construct an explicit decoder
  that depends only on `⌈log₂ n⌉`. Lower bounds hold against arbitrary decoders.
* `P_α` (Definition 1, `IsPowerLaw α C'`) takes the constant `C'` as a parameter. `P'_α`
  (Definition 2, `IsProperPowerLaw α`) is transcribed literally with `C = 1/ζ(α)`. The class `V₀` of
  isolated vertices is unconstrained, as in the paper. Theorem 3's graph uses isolated vertices for
  the slack instead of the paper's extra degree-`≥ i₁` singletons. Definition 2 allows this.
* "`Ω(n^{1/α})` for all `n`" is formalized as: there is `κ > 0` such that for all large `n` every
  scheme needs `κ n^{1/α}` bits.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (`√(2cn log n) + 2 log n + 1`, `S_{c,n}`) | `theorem1` | `Labeling.lean` |
| Theorem 2 (`(C'n)^{1/α} (log n)^{1-1/α} + 2 log n + 1`, `P_α`, `C' ≥ 2`) | `theorem2` | `Labeling.lean` |
| Proposition 1 (max degree `≤ (C/(α-1)+2) n^{1/α} + i₁ + 3`) | `prop1` | `Props.lean` |
| Proposition 2 (`P'_α` sparse for `α > 2`) | `prop2` | `Props.lean` |
| Proposition 3 (`P'_α ⊆ P_α`, constant `C'₀`) | `prop3`, `C'₀` | `Props.lean` |
| Proposition 4 (`⌊√(cn)/2⌋` lower bound; with `c < n`) / failure for large `c` | `prop4` / `prop4_false` | `Labeling.lean` |
| Theorem 3 (`Ω(n^{1/α})` for `P'_α`, and for `P_α` with `C' ≥ C'₀`; `α > 2`) | `theorem3_proper`, `theorem3` | `LowerBound.lean`, `Main.lean` |
| Thm 3 construction: every graph on `i₁` vertices is induced in some `G ∈ P'_α` | `construct` | `LowerBound.lean` |
| Degree realization around an induced subgraph (the three phases) | `realize`, `exists_maximal_fill`, `bip_phase` | `Realization.lean` |
| Moon's counting bound; induced subgraphs inherit schemes | `moon`, `HasAdjLabeling.of_embedding` | `Counting.lean` |
| Fat/thin threshold scheme | `exists_threshold_scheme`, `hasAdjLabeling_of_threshold` | `Labeling.lean` |
| `ζ`-tail bounds, facts about `i₁` | `one_sub_C_mul_sum_Icc_le`, `sum_Ioc_rpow_neg_le`, `i₁_le`, `lt_i₁` | `Zeta.lean` |

Theorems 1 and 2 hold with `+ log n` in place of `+ 2 log n`, because a thin vertex has degree `< f(n)`.

**Not formalized.** Proposition 5 (Barabási–Albert graphs have low arboricity; it relies on external
results), the induced-universal-graph corollaries, and the experimental section with the threshold prediction.
Proposition 3 and Theorem 3 for `P_α` with the paper's exact constant `C'`, below `C'₀`: a pen-and-paper check
shows that it also suffices, but this is not in Lean; see `differencies.md`.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: for `α > 2` and all large `n`, `P'_α` and `P_α` contain `n`-vertex graphs
(`eventually_exists_isProperPowerLaw`, `eventually_exists_isPowerLaw`). The lower bounds are
non-vacuous on their own, because an empty family would admit 0-bit labels. Everything is built on
Mathlib. The labelling-by-class-sizes lemma comes from CSLib (`Fintype.exists_labelling`).
CSLib candidates: `HasAdjLabeling`, `moon`, `HasAdjLabeling.of_embedding` (adjacency labeling basics),
and `exists_maximal_fill` / `bip_phase` (degree-constrained edge-maximal supergraphs).
