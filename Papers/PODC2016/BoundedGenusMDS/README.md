# Local MDS Approximation on Bounded Genus Graphs — PODC 2016

Saeed Akhoondian Amiri, Stefan Schmid, Sebastian Siebertz. *A Local Constant Factor MDS Approximation
for Bounded Genus Graphs.* PODC 2016. DOI [10.1145/2933057.2933084](https://doi.org/10.1145/2933057.2933084).
Formalized version: arXiv [1602.02991](https://arxiv.org/abs/1602.02991) v2 (the latest arXiv version); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The local constant factor on bounded genus graphs stands: on graphs whose depth-1 minors
have edge density `≤ c` and which exclude `K_{t,3}` as a depth-1 minor, the modified Lenzen–Pignolet–Wattenhofer
algorithm is a `(6c²t + (2t+5)c + 4)`-approximation (Lemma 12), which we prove with the paper's constant, for every
choice of dominators, and it runs in 6 LOCAL rounds. The counting lemmas behind it are false as stated (Lemma 7,
Corollary 8 and Lemma 11 with Lean counterexamples, Lemma 9 with an informal one), but local changes repair them.
With the genus facts as hypotheses, the `O(g)` factor of Theorem 13 is only proved as `O(g²)`, and Section 4's
`24g + O(1)` factor was not checked.

## Mistakes in the paper

### ⚠️ Theorem 13 (`O(g)` approximation factor)
The `O(g)` factor is not established: the proof treats the density bound `c` as a constant, but Lemmas 5 and 10
need it for small depth-1 minors, where genus-`g` graphs have density `Θ(√g)`, so the argument only gives `O(g²)`
(`density_unbounded`).

**Impact.** The `O(g)` factor is unestablished, not refuted. A local constant factor for every fixed genus stands:
we prove an `O(g²)` approximation (`≤ 1100(g+1)²`, `theorem_13`, `factor_le`).

**Details.** Lemma 12's factor `6c²t + …` is `O(g)` only if `c = O(1)`. The paper takes `c ≈ 3` ("`c ≤ 3.01` in
sufficiently large graphs", §4). However, Lemmas 5 and 10 apply the density bound to *small* depth-1 minors as
well, and small graphs of genus `g` have density up to `Θ(√g)`; for example, `K_k` has genus `⌈(k-3)(k-4)/12⌉`. So
`c = Θ(√g)` is necessary, and with `t = 4g + 3` the argument gives `O(g²)`. We show that the hypotheses alone force
`c` to grow with `g` (`density_unbounded`). The claimed `O(g)` rounds are an overstatement in the other direction:
the algorithm needs 6 rounds (`output_isLocal`).

**Repair.** We prove the theorem with the genus facts as hypotheses: `c(g) = 3 + ⌊√(3g)⌋ + 1` suffices, and the
factor is `≤ 1100(g+1)²` (`theorem_13`, `factor_le`).

### 🔧 Lemma 7, items 2 and 3, and Corollary 8 (neighbours between stars)
Lemma 7 fails on the planar graph `m_i – c' – u_k – m_j` (`k = 1..K`), where all `K` leaves of `m_j` see the star
of `m_i`, beyond the bound `2ct = 12` (item 2, `K = 13`) or `4ct = 24` (item 3, `K = 25`), and in the same graph
Corollary 8's `|Y| ≤ 6c²t|M|` fails for `K = 145`, since `Y` contains all `u_k`, so `|Y| ≥ K`, while `|M| = 2`
(`lemma_7_2_false`, `lemma_7_3_false`, `corollary_8_false`).

**Impact.** The counting behind Lemma 12 breaks: its final count adds the faulty `|Y|` bound of Corollary 8 (and
relies on the false Lemma 11). Corrected versions (bounds `2c(t-1)` and `4c(t-1)`, a smaller `Y`) suffice to prove
Lemma 12 with the paper's constant (`lemma_12`).

**Details.** The `K_{t,3}` argument picks `c ∈ C_{m_j}` and contracts the star of `m_i` minus `c`. If `c` is itself
a leaf of `m_i` (`c ∈ N_i`), the vertices `u ∈ N_j` whose only neighbour in `N_i` is `c` are not bounded at all.
In the counterexample, the graph is `K_{2,K}` on `{c', m_j} × {u_k}` plus the pendant edge `m_i c'`. Assumption 6
holds with `c = 2`, `t = 3`. `M = {m_i, m_j}` is a minimum dominating set and `D = ∅`. The stars are `N_i = {c'}`
and `N_j = {u_1, …, u_K}`. Item 2 uses the order `m_i, m_j`; item 3 the order `m_j, m_i`. Item 1 has the same gap
but is not refuted formally.

**Repair.** Count only leaves outside `C = ⋃ C_m` that have a neighbour outside `C`. Then the bounds are `2c(t-1)`
and `4c(t-1)` (`Setup.lemma_7_12`, `Setup.lemma_7_3`). Our `Y` excludes `C`. With the corrected Lemma 7 we get
`|Y| + |Y_D| ≤ 6c²(t-1)|M|`, where `Y_D` is the part seeing stars of `M ∩ D` (`Setup.corollary_8`). Lemma 12 then
counts dominator images instead:
- `M ∪ C`, `Z` (Lemma 10), and the corrected `Y`;
- images of sources in `M ∪ C` or in `Y_D`;
- images inside stars (corrected Lemma 11).

The total is `(c+1) + 3(2c+1) + 6c²(t-1) + (2(t-1)+4)c ≤ 6c²t + (2t+5)c + 4` (per `|M|`).

### 🔧 Lemma 11 (dominators inside a star)
Lemma 11 fails on the book `K_{1,1,K}` (spine `m x`, pages `u_k`) with the legal dominator choice `dom ≡ x`: all
`K + 1` leaves of `m` have their dominator inside the star outside `Y ∪ Z`, beyond the bound `(2(t-1)+4)c|M| = 16`
for `K = 17` (`lemma_11_false`).

**Impact.** Repaired by also excluding `C` from the dominator's range; then the paper's bound holds and Lemma 12
goes through.

**Details.** The proof applies Lemma 9 to `dom(u)`, which may lie in `C_m`. In the counterexample, Assumption 6
holds with `c = 2`, `t = 3`; `M = {m}`, `D = ∅`, `C_m = {x}` (every admissible `C_m` contains `x`), and
`Y = Z = ∅`. Since `m` and `x` tie for the maximal residual degree, `dom ≡ x` is a legal choice ("choose any").

**Repair.** Exclude `C` from the dominator's range as well. Then the paper's bound `(2(t-1)+4)c|M|` holds
(`Setup.lemma_11`).

### 🔧 Lemma 9 (for some admissible `C_m`)
Lemma 9 fails when `m` and `v` are both adjacent to 18 vertices forming 6 paths `a_i – c_i – b_i` and
`C_m = {c_1, …, c_6}`: `v` has 18 neighbours in the star, more than `2c(t-1) = 12` (informal counterexample, not
formalized).

**Impact.** Repaired by counting only neighbours outside `C`, which is all Lemma 11 needs.

**Details.** The `K_{t,3}` argument covers only `u ∈ N(c)` for `c ∈ C_m`, not `u ∈ C_m` itself. In the example the
graph is planar, so `c = 3`, `t = 3`, and `D = ∅`; `C_m` covers `N(m)` and `v ∉ C_m`.

**Repair.** Count only the neighbours outside `C`; then the bound `2c(t-1)` holds (`Setup.lemma_9`).

### ✏️ Slips
- Lemma 10's strict `|Z| < |M ∪ C|` fails for the empty graph, where both sides are 0. We prove `≤`, which is all
  the paper uses (`Setup.lemma_10`).
- Lemma 12 assumes "edge density at most `c`", but it needs Assumption 6 (density of all depth-1 minors).
- The final line of the proof of Lemma 12 drops the factor `|M|`.

### Typos
- Algorithm 1 has a stray `end if`.

## Proof gaps (statements true)

### 🔧 Lemma 5 (the contracted minor `H̃`)
`H̃` contracts only the stars of `m ∈ M \ D`, so vertices of `N(D \ M) \ (D ∪ M)` whose unique `M`-neighbour lies
in `M ∩ D` stay uncontracted and `|V(H̃)| = |D \ M| + |M|` is wrong.

**Impact.** Statement true; repaired (`lemma_5`), and it holds for every dominating set `M`.

**Repair.** We contract a star around *every* `m ∈ M` and exclude `D`-vertices from the leaves.

### 🔧 Lemma 11 (the `E'`-neighbours of `m`)
Lemma 11's proof says that `m` has at most `4c + 2c(t-1)` `E'`-neighbours, but this fails when leaves of `m` are
dominated by `D`: only the undominated ones are bounded, by `deg(dom(u))`.

**Impact.** The corrected Lemma 11 goes through (`Setup.lemma_11`).

**Repair.** Use the residual degree: `d_{V-D}(m) ≤ d_{V-D}(dom(u))`.

### 🔧 Lemma 7 (`m_i ∉ C_{m_2}`)
In the proof of Lemma 7, "`m_i ∉ C_{m_2}`" should be `C_{m_j}`, and the corrected claim is still unjustified, since
`C_{m_j}` is arbitrary and may contain `m_i`.

**Impact.** Harmless, because `m_i` covers no vertex of `N_j` (`Setup.lemma_7_12`).

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
* Section 4 (Lemma 14, Algorithm 2, Theorem 15, the `24g + O(1)` factor) and the first-order definability of
  Section 5. Theorem 15 might recover an `O(g)` factor by another algorithm; we did not check it.
* The Lemma 9 counterexample is not formalized.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The counterexample graphs also show that the hypotheses of Lemma 12 are satisfiable:
they meet Assumption 6 via `SimpleGraph.depth1_of_cover_two` (a vertex cover of size two gives density
`≤ 2` and no `K_{3,3}`). The depth-1 minor library is staged in
`Podc/Foundations/Combinatorics/SimpleGraph/Depth1Minor.lean` (a CSLib candidate). It bridges to
CSLib's minors (`MinorDensityLE.depth1DensityLE`). The locality proof uses CSLib's
`Cslib.Local.GAgree`.
