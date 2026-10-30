# Local MDS Approximation on Bounded Genus Graphs — PODC 2016

Saeed Akhoondian Amiri, Stefan Schmid, Sebastian Siebertz. *A Local Constant Factor MDS Approximation
for Bounded Genus Graphs.* PODC 2016. DOI [10.1145/2933057.2933084](https://doi.org/10.1145/2933057.2933084).
Formalized version: arXiv [1602.02991](https://arxiv.org/abs/1602.02991) v2 (the latest arXiv version); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The core result holds. On graphs whose depth-1 minors have edge density
`≤ c` and which exclude `K_{t,3}` as a depth-1 minor, the modified Lenzen–Pignolet–Wattenhofer algorithm
is a `(6c²t + (2t+5)c + 4)`-approximation (Lemma 12). We prove it with the paper's constant, for every
choice of dominators, and the algorithm runs in 6 LOCAL rounds. But the counting lemmas behind it are
false as stated: Lemma 7, Corollary 8 and Lemma 11 (Lean counterexamples), and also Lemma 9 (informal
counterexample). The `O(g)` factor of Theorem 13 is not established: the paper's argument gives `O(g²)`.

## Mistakes in the paper

* **Lemma 7 is false (items 2 and 3).** The `K_{t,3}` argument picks `c ∈ C_{m_j}` and contracts the
  star of `m_i` minus `c`. If `c` is itself a leaf of `m_i` (`c ∈ N_i`), the vertices `u ∈ N_j` whose
  only neighbour in `N_i` is `c` are not bounded at all.
  *Counterexample.* Take the planar graph `m_i – c' – u_k – m_j`, `k = 1..K`, i.e. `K_{2,K}` on
  `{c', m_j} × {u_k}` plus the pendant edge `m_i c'`. Assumption 6 holds with `c = 2`, `t = 3`.
  `M = {m_i, m_j}` is a minimum dominating set and `D = ∅`. The stars are `N_i = {c'}` and
  `N_j = {u_1, …, u_K}`. All `K` vertices `u_k` see `N_i`, so item 2 (`≤ 2ct = 12`) fails for
  `K = 13`. With the order `m_j, m_i`, item 3 (`≤ 4ct = 24`) fails for `K = 25`.
  Item 1 has the same gap but is not refuted formally.
  *Fix.* Count only leaves outside `C = ⋃ C_m` that have a neighbour outside `C`. Then the bounds are
  `2c(t-1)` and `4c(t-1)`. (`lemma_7_2_false`, `lemma_7_3_false`; fixed: `Setup.lemma_7_12`,
  `Setup.lemma_7_3`)
* **Corollary 8 is false.** Corollary 8 claims `|Y| ≤ 6c²t|M|`. In the same graph, `Y` contains all
  `u_k`, so `|Y| ≥ K` while `|M| = 2`; this fails for `K = 145`.
  *Fix.* Our `Y` excludes `C`. With the corrected Lemma 7 we get `|Y| + |Y_D| ≤ 6c²(t-1)|M|`, where
  `Y_D` is the part seeing stars of `M ∩ D`. (`corollary_8_false`; fixed: `Setup.corollary_8`)
* **Lemma 11 is false.** The proof applies Lemma 9 to `dom(u)`, which may lie in `C_m`.
  *Counterexample.* Take the book `K_{1,1,K}` with spine `m x` and pages `u_k`. Assumption 6 holds
  with `c = 2`, `t = 3`. `M = {m}`, `D = ∅`, `C_m = {x}` (every admissible `C_m` contains `x`), and
  `Y = Z = ∅`. Since `m` and `x` tie for the maximal residual degree, `dom ≡ x` is a legal choice
  ("choose any"). Then all `K + 1` leaves of `m` have their dominator inside the star outside
  `Y ∪ Z`, but the lemma claims `≤ (2(t-1)+4)c|M| = 16`; this fails for `K = 17`.
  *Fix.* Also exclude `C` from the dominator's range. Then the paper's bound
  `(2(t-1)+4)c|M|` holds. (`lemma_11_false`; fixed: `Setup.lemma_11`)
* **Lemma 9 is false for some admissible `C_m`.** The `K_{t,3}` argument covers only
  `u ∈ N(c)` for `c ∈ C_m`, not `u ∈ C_m` itself. Example (not formalized): take `m` adjacent to `v`,
  and `m` and `v` both adjacent to 18 vertices `u`. The `u`'s form 6 paths `a_i – c_i – b_i`. The
  graph is planar, so `c = 3`, `t = 3`, and `D = ∅`. `C_m = {c_1, …, c_6}` covers `N(m)` and
  `v ∉ C_m`, but `v` has 18 neighbours in the star, more than `2c(t-1) = 12`.
  *Fix.* Count only the neighbours outside `C`; then the bound `2c(t-1)` holds.
  (fixed: `Setup.lemma_9`)
* **Theorem 13's `O(g)` factor is not established; the proof gives `O(g²)`.** Lemma 12's factor
  `6c²t + …` is `O(g)` only if `c = O(1)`. The paper takes `c ≈ 3` ("`c ≤ 3.01` in sufficiently large
  graphs", §4). However, Lemmas 5 and 10 apply the density bound to *small* depth-1 minors as well,
  and small graphs of genus `g` have density up to `Θ(√g)`; for example, `K_k` has genus
  `⌈(k-3)(k-4)/12⌉`. So `c = Θ(√g)` is necessary, and with `t = 4g + 3` the argument gives `O(g²)`.
  The claim is not refuted.
  We prove the theorem with the genus facts as hypotheses: `c(g) = 3 + ⌊√(3g)⌋ + 1` suffices, and the
  factor is `≤ 1100(g+1)²`. We also show that the hypotheses alone force `c` to grow with `g`.
  The claimed `O(g)` rounds are an overstatement in the other direction: the algorithm needs 6 rounds.
  (`theorem_13`, `factor_le`, `density_unbounded`, `output_isLocal`)
* **Lemma 5: gap in the proof; statement true.** `H̃` contracts only the stars of `m ∈ M \ D`.
  Vertices of `N(D \ M) \ (D ∪ M)` whose unique `M`-neighbour lies in `M ∩ D` stay uncontracted, so
  `|V(H̃)| = |D \ M| + |M|` is wrong. We contract a star around *every* `m ∈ M` and exclude
  `D`-vertices from the leaves. The lemma then holds for every dominating set `M`. (`lemma_5`)
* **Lemma 12's proof needs repair; statement true with the paper's constant.** The final count adds
  the faulty `|Y|` bound. We count dominator images instead:
  - `M ∪ C`, `Z` (Lemma 10), and the corrected `Y`;
  - images of sources in `M ∪ C` or in `Y_D`;
  - images inside stars (corrected Lemma 11).

  The total is `(c+1) + 3(2c+1) + 6c²(t-1) + (2(t-1)+4)c ≤ 6c²t + (2t+5)c + 4` (per `|M|`).
  (`lemma_12`)
* **Minor slips.**
  - Lemma 12 assumes "edge density at most `c`", but it needs Assumption 6 (density of all depth-1 minors).
  - The final line of the proof of Lemma 12 drops the factor `|M|`.
  - Lemma 10's strict `|Z| < |M ∪ C|` fails for the empty graph; we prove `≤`.
  - In the proof of Lemma 7, "`m_i ∉ C_{m_2}`" should be `C_{m_j}`. Moreover, `C_{m_j}` may contain
    `m_i`; this is harmless because `m_i` covers no vertex of `N_j`.
  - Lemma 11's proof says that `m` has at most `4c + 2c(t-1)` `E'`-neighbours. Only the undominated
    ones are bounded, by `deg(dom(u))`.
  - Algorithm 1 has a stray `end if`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finite simple graphs `G : SimpleGraph V`.
* LOCAL model: synchronous and deterministic, with no failures and unique identifiers.
* The algorithm is the paper's modified Algorithm 1 with integer parameter `c` (line 5: `|A| ≤ 2c`).
* Approximation: the Phase-2 dominator choice ("choose any `dom(v) ∈ N[v]` of maximal residual
  degree") is a hypothesis `IsDominator`, so the bound holds for **every** tie-breaking. "f-approximation"
  is stronger than the paper's: the output dominates and `|S| ≤ f·|M|` for *every* dominating set `M`.
* Locality: identifiers are the elements of a linearly ordered `V`, and ties go to the smallest
  identifier (`domMin`). `output_isLocal` shows that membership of `v` in the output depends only on the
  radius-6 view of `v` (CSLib's `Cslib.Local.IsLocal`).
* Depth-1 minors are defined as in §2 (pairwise disjoint stars with centers); "`ε(H) ≤ c` for all
  depth-1 minors" is `Depth1DensityLE G c` (`|E(H)| ≤ c|V(H)|`).
* Mathlib has no surfaces, so the genus facts (Lemmas 1–4) are hypotheses for Theorem 13. Every
  depth-1 minor satisfies Euler's bound `|E(H)| ≤ 3|V(H)| + 6g` (Lemmas 1, 4), and `G` excludes
  `K_{4g+3,3}` (Lemma 2).

**Main results in Lean.** Names are in namespace `Podc.BoundedGenusMDS`.

| Paper | Lean | File |
|---|---|---|
| Output is a dominating set (§3) | `output_isDominatingSet` | `Defs.lean` |
| Lemma 5 | `lemma_5` | `Lemma5.lean` |
| Lemma 7.1–7.2, corrected (`2c(t-1)`) | `Setup.lemma_7_12` | `Lemma7.lean` |
| Lemma 7.3, corrected (`4c(t-1)`) | `Setup.lemma_7_3` | `Lemma7.lean` |
| Lemma 7.2 / 7.3 as stated: **false** | `lemma_7_2_false`, `lemma_7_3_false` | `Counterexamples.lean` |
| Corollary 8, corrected | `Setup.corollary_8` | `Lemma12.lean` |
| Corollary 8 as stated: **false** | `corollary_8_false` | `Counterexamples.lean` |
| Lemma 9, corrected | `Setup.lemma_9` | `Lemma7.lean` |
| Lemma 10 (`≤`) | `Setup.lemma_10` | `Lemma12.lean` |
| Lemma 11, corrected (paper's constant) | `Setup.lemma_11` | `Lemma12.lean` |
| Lemma 11 as stated: **false** | `lemma_11_false` | `Counterexamples.lean` |
| **Lemma 12** (`6c²t + (2t+5)c + 4`) | `lemma_12` | `Lemma12.lean` |
| Lemma 12 for the deterministic 6-round LOCAL algorithm | `lemma_12_local`, `output_isLocal` | `Locality.lean` |
| Theorem 13 (genus facts as hypotheses), `O(g²)` | `theorem_13`, `factor_le` | `Genus.lean` |
| `c` cannot be independent of `g` | `density_unbounded` | `Genus.lean` |

**Not formalized.**
* Lemmas 1–4 (genus theory) enter as hypotheses.
* Section 4 (Lemma 14, Algorithm 2, Theorem 15) and the first-order definability of Section 5.
* The Lemma 9 counterexample is not formalized.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The counterexample graphs also show that the hypotheses of Lemma 12 are satisfiable:
they meet Assumption 6 via `SimpleGraph.depth1_of_cover_two` (a vertex cover of size two gives density
`≤ 2` and no `K_{3,3}`). The depth-1 minor library is staged in
`Podc/Foundations/Combinatorics/SimpleGraph/Depth1Minor.lean` (a CSLib candidate). It bridges to
CSLib's minors (`MinorDensityLE.depth1DensityLE`). The locality proof uses CSLib's
`Cslib.Local.GAgree`.
