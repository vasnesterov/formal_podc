# A Combinatorial Topology Approach to Arrow's Theorem — PODC 2022

Sergio Rajsbaum, Armajac Raventós-Pujol. *A Distributed Combinatorial Topology Approach to Arrow's Impossibility
Theorem.* PODC 2022, pp. 471–481. DOI [10.1145/3519270.3538433](https://doi.org/10.1145/3519270.3538433).
Formalized version: the PODC version; no arXiv version exists. For the proofs that the PODC version defers
(Prop. 4.1, Thm. 4.2, Section 4.2) we used the full version, *A Combinatorial Topology Approach to Arrow's
Impossibility Theorem* (MPRA 120023, 2024; Social Choice and Welfare, 2025). Numbering is the PODC one unless
marked "full version".
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Arrow's theorem (Thm. 2.1), its topological form (Thm. 2.2), the index lemma, the
orientability of `N_I` and the index-lemma proof of the base case are all correct, after small repairs. **Theorem
4.2 (domain restrictions) is false**, and Proposition 4.1 misses a hypothesis in its last sentence. The full version
corrects Section 4, and its corrected characterization (Theorem 6) is verified.

## Mistakes in the paper

### ❌ Theorem 4.2 (domain restrictions, two critical profiles)
Theorem 4.2 is false whenever the blue edges of the two removed critical profiles share a vertex, e.g. for `R₁ = (BAC, ACB)`, `R₂ = (CBA, ACB)` every unanimous IIA map on `N_I \ {R₁, R₂}` is dictatorial (`thm42_counterexample`, `thm42_not_admits_of_adjacent`).

**Impact.** A secondary result of Section 4; Arrow's theorem and its topological proof are unaffected. The
statement is true for disjoint blue edges (critical pairs), and the full version replaces it by a correct
characterization (Theorem 6), which we verified (`thm42_admits_of_disjoint`, `thm6`).

**Details.** The theorem considers `n = 2`, `|X| = 3`, and two critical profiles `R₁ ∈ C₁`, `R₂ ∈ C₂` with
*different* blue edges, and claims that `N_I \ {R₁, R₂}` admits a non-dictatorial unanimous IIA map. When the
two blue edges share a vertex (12 of the 30 choices), the antiunanimity profile spanned by the two edges is
still in the domain, and it forces dictatorship. In the explicit instance the remaining profile is
`(BCA, ACB)`. The full version's Theorem 6 adds critical triples.

### ⚠️ Proposition 4.1 and Theorem 4.2, "moreover" sentences (subdomains)
"Every domain contained in one of these maximal domains admits a non-dictatorial map" is false, e.g. for the one-profile domain `{(ABC, ACB)}`, where unanimity forces `F(R) ∈ {ABC, ACB}`, one voter's preference (`prop41_moreover_false`, `thm42_moreover_false`).

**Impact.** A missing hypothesis: non-dictatoriality is not inherited by subdomains that lose a vertex of
`N_I`. The sentence holds for subdomains in which every pair of alternatives stays free, and the rest of
Prop. 4.1 is correct (`prop41_moreover_of_pairFree`).

### ⚠️ Full version, example of a critical triple
The full version's example of a critical triple uses `(BCA, ABC)`, which lies in `C₁`, not `C₂`, so removing the three listed profiles leaves a dictatorial domain (`paper_triple_example_not_critical`).

**Impact.** Typo-level slip: the intended profile is `(CBA, ACB)`.

### Typos and slips
- Lemma 3.2: "`σ₃(i) = +` (resp. `+`)" should be "`−` (resp. `+`)".
- Lemma 5.2, Step 3: `F^n(R)` should be `F^n(R')`.
- Full version, Section 4.2: "deleting a triangle on each of the concentric cylinders" is imprecise (two of
  the six profiles of each are deleted).

## Proof gaps (statements true)

### 🛠️ Lemma 5.1 (reduction from `|X| = 3` to `|X| ≥ 3`)
The auxiliary profile `x R' b R' a R' y` needs `a, b, x, y` pairwise distinct, but `x, y` are fixed in advance, so `a = x` breaks the construction.

**Impact.** Statement true; repaired (`arrow_of_three`).

**Repair.** If `a, b` both lie in the triple, IIA finishes the proof. Otherwise, run the construction with two
elements of the triple different from `a` and `b`.

### 🛠️ Section 3.3 (base case via the index lemma)
"The two remaining contributions have to be `−1` each" needs each of them to be `≥ −1`, which the paper does not show (a priori a cycle that is not tricoloured could contribute `±2`).

**Impact.** Statement true; the missing step is proved (`cyc_split`).

**Repair.** Each contribution lies in `{0, −1}`, because a non-unanimous Condorcet cycle is oriented opposite
to the unanimous ones.

### 🛠️ Lemma 3.2 (orientability of `N_I`)
The proof's pairing is not a pairing when `≥ 2` coordinates are free, and the boundary-edge characterization used in Figure 7 is stated without proof.

**Impact.** Statement true; repaired (`lemma_3_2`, `isBoundary_iff`).

**Repair.** We pair by flipping one fixed free coordinate, and prove the boundary-edge characterization.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Static combinatorics; no distributed system. The Section 6 analogy with tasks is informal.
- **Preferences.** Strict total orders on an arbitrary, possibly infinite, type of alternatives. Voters form a
  finite type with at least 2 elements.
- **Axioms.** Unanimity, IIA and dictatorship as in the paper. Domain-restricted versions are used for Section 4.
- **Complexes.** A vertex of `N_I` is literally the set of profiles `U^σ_{ab}`; simplices are vertex sets with a
  common profile (nerves). The same holds for `N_O`.
  - Theorem 2.2 is stated without "chromatic", as in the PODC version. We prove that unanimous simplicial maps are
    automatically chromatic, so nothing is lost.
- **Three alternatives.** Computations use a sign model, proved equivalent to the set-level complexes. The Section 4
  statements are decided by the kernel after a proved reduction to sign functions on the 12 vertices.

**Main results in Lean** (namespace `Podc.ArrowTopology`).

| Paper | Lean | File |
|---|---|---|
| **Thm. 2.1** (Arrow; any finite `n ≥ 2`, any `X` with 3 elements) | `theorem_2_1` | `Main.lean` |
| **Thm. 2.2** (topological Arrow); base case `n = 2`, `\|X\| = 3` | `theorem_2_2`, `theorem_2_2_base` | `Main.lean` |
| Thm. 3.1 (index lemma, generalized) | `Cslib.Simplicial.index_eq_content` | CSLib `SimplicialComplex/IndexLemma.lean` |
| Lemma 3.2 (`N_I` orientable, any `n`) | `lemma_3_2` | `Orientation.lean` |
| §2.3.3 / full-version Props. 3–4 (IIA ⇔ chromatic, dictator ⇔ projection) | `prop_3_forward`, `prop_3_backward`, `prop_4_unanimity`, `prop_4_dictator` | `Complexes.lean` |
| Lemmas 5.1, 5.2 (reductions) | `arrow_of_three`, `arrow_of_two_voters` | `Reduction.lean` |
| §4.1 (cylinders dictatorial), Prop. 4.1 | `not_admits_C1`, `not_admits_C2`, `prop41_admits`, `prop41_maximal` | `Domains.lean` |
| **Thm. 4.2 false** | `thm42_false`, `thm42_counterexample` | `Domains.lean` |
| Full-version Thm. 6 | `thm6` | `Domains.lean` |
| §4.2 polarised domain is non-dictatorial; `χ = −8` | `ThreeAlts.polarised_admits`, `polarised_euler` | `Polarised.lean` |

**Not formalized.**
- Non-contractibility of the polarised domain. Mathlib has no geometric realization; we prove the certificate
  `χ = −8 ≠ 1` but not "contractible ⇒ χ = 1".
- The dimension of `N_I` (the vertex counts are proved).
- The infinite-voters remark, weak orders, and Remarks 2.1–2.3.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
Section 4 checks use kernel `decide` (no `native_decide`). The preference framework, nerves and the index lemma come
from CSLib (`Cslib/Foundations/SocialChoice/`, `Cslib/Foundations/Combinatorics/SimplicialComplex/`).
