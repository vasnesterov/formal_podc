# A Distributed Combinatorial Topology Approach to Arrow's Impossibility Theorem (PODC 2022)

Sergio Rajsbaum, Armajac Raventós-Pujol. PODC 2022, pp. 471–481, DOI 10.1145/3519270.3538433.
- Local copy: `papers/2022/3519270.3538433_A_Distributed_Combinatorial_Topology_Approach_to_Arrow_s_Impossibility.pdf`.
- No arXiv version exists. The full version cited as [49] is *A Combinatorial Topology Approach to Arrow's
  Impossibility Theorem* (MPRA paper 120023, Feb 2024; later in Social Choice and Welfare, 2025). We used it for
  the proofs that the PODC version defers (Prop. 4.1 / Thm. 4.2 / Section 4.2) and for its Propositions 3–4.
- Numbering below is the **PODC** numbering unless marked "full version".

## Status

**Complete. No `sorry`, no axioms.** `lean_verify` on the main theorems reports only `propext`,
`Classical.choice`, `Quot.sound`. Build: `lake build Papers.PODC2022.ArrowTopology.Main`
(and the other modules listed below).

**Verdict.** The main results are correct: Arrow's theorem (Thm. 2.1), its combinatorial-topology form
(Thm. 2.2), the index lemma (Thm. 3.1), orientability of `N_I` (Lemma 3.2), the index-lemma proof of the
base case `n = 2, |X| = 3` (Section 3.3) and the reduction lemmas (Lemmas 5.1, 5.2). The proofs needed only
minor repairs (Lemma 5.1 has a real but easily fixed gap). In contrast, the domain-restriction statements
of Section 4 of the PODC version are partly **false** (see below and `differencies.md`); the full version
corrects them, and its corrected characterization is verified.

**Section 4 (domain restrictions, `n = 2`, `|X| = 3`).** All results were checked by sound kernel
`decide` after a proven reduction to sign functions (`DomainBridge.lean`).
- The basic restriction is correct: neither cylinder admits a non-dictatorial map (Section 4.1).
- Prop. 4.1 is correct, except for a missing hypothesis in its last sentence ("every subdomain of a maximal
  domain admits a non-dictatorial map"). Being non-dictatorial is not inherited by subdomains that lose a
  vertex of `N_I`. With the hypothesis "all pairs stay free" the sentence holds (`prop41_moreover_of_pairFree`).
- Thm. 4.2 is **false**: when the two blue edges are adjacent, `N_I \ {R₁, R₂}` is still dictatorial.
  Its "moreover" sentence has the same missing hypothesis.
- The polarised domain does admit a non-dictatorial map (Section 4.2). For "not contractible" we prove the
  combinatorial certificate `χ = −8 ≠ 1`.
- The full version's corrected characterization (its Theorem 6) is **verified** (`thm6`). Its example of a
  critical triple is wrong: it uses a profile from the wrong cylinder.

## Model / framework (explicit)

No distributed system is modelled: everything is static combinatorics (the paper's Section 6 analogy with
tasks is only discussed, see `Counts.lean`).
- **Preferences:** strict total orders `Pref X` on an arbitrary type `X` of alternatives (possibly
  infinite); profiles `ι → Pref X` for a type of voters `ι` (`Cslib/Foundations/SocialChoice/Aggregation.lean`).
- **Arrow's axioms:** `Unanimity`, `IIA`, `IsDictator`/`Dictatorial`, `ArrowHolds ι X`; domain-restricted
  versions `UnanimityOn D`, `IIAOn D`, `IsDictatorOn D`, `AdmitsNonDictatorial D`.
- **Complexes (Section 2.3):** vertices of `N_I` are literally the *sets of profiles*
  `U^σ_{ab} = {R | voter i ranks a above b iff σ i}` (`VI ι X`); vertices of `N_O` the sets of orders
  `U^s_{ab}` (`VO X`); simplices = finite sets of vertices with a common point (nerves, as Mathlib
  `PreAbstractSimplicialComplex`: `NI ι X`, `NO X`). Simplicial maps: `IsSimplicialMap`
  (`Cslib/Foundations/Combinatorics/SimplicialComplex/Nerve.lean`). Unanimous / chromatic / projection maps: `IsUnanimousMap`,
  `IsChromatic`, `IsProjection`.
- **Sign model (three alternatives, computations):** vertex `(j, σ)` with `j : Fin 3` the pair `AB, BC, CA`
  and `σ : ι → Bool` the sign vector; triangles = consistent sign triples `t : Fin 3 → ι → Bool`; a chromatic
  map is a sign function `s : Fin 3 × (ι → Bool) → Bool` (`SignModel.lean`). `ThreeAlt.lean` proves that for
  `X = {x, y, z}` the signature map from profiles to consistent sign triples is a bijection, which transports
  everything to the set-theoretic complexes.
- **Index lemma (Section 3.2):** a 2-complex is a finite family of oriented triangles `T → V × V × V`; boundary
  edge = lies in exactly one triangle; oriented = on every other edge both induced directions occur equally often
  (`Cslib/Foundations/Combinatorics/SimplicialComplex/IndexLemma.lean`).

## Main results ↔ Lean

| Paper | Lean | File |
|---|---|---|
| Thm. 2.1 (Arrow) | `Podc.ArrowTopology.theorem_2_1` (any finite `ι`, `2 ≤ card ι`; any `X` with 3 distinct elements, possibly infinite) | `Main.lean` |
| Thm. 2.2 (topological Arrow), general | `theorem_2_2` | `Main.lean` |
| Thm. 2.2 for `n = 2`, `|X| = 3` (Section 3.3) | `theorem_2_2_base` (set-level), `theorem_2_2_signs` (sign model) | `Main.lean`, `BaseCase.lean` |
| Thm. 3.1 (index lemma, generalized) | `Cslib.Simplicial.index_eq_content` | `Cslib/Foundations/Combinatorics/SimplicialComplex/IndexLemma.lean` |
| Lemma 3.2 (`N_I` orientable; any number of voters) | `lemma_3_2`; boundary edges: `isBoundary_iff` | `Orientation.lean` |
| Section 3.3 steps: `C = 0`, `I = 0`, boundary = 4 Condorcet cycles, contributions `+1,+1` / `{0,−1}` | `content_eq_zero`, `index_eq_zero`, `index_eq`, `boundary_multiset`, `cyc_unanimous`, `cyc_split` | `BaseCase.lean` |
| Section 2.3.3 / full-version Prop. 3 (IIA ⇔ chromatic simplicial map) | `prop_3_forward`, `prop_3_backward` | `Complexes.lean` |
| Full-version Prop. 4 (unanimity ⇔, dictator ⇔ projection) | `prop_4_unanimity`, `prop_4_dictator`, `prop_4_dictatorial` | `Complexes.lean` |
| (new) unanimous simplicial maps are chromatic | `isChromatic_of_unanimous` | `Complexes.lean` |
| Lemma 5.1 (`|X| = 3` ⇒ `|X| ≥ 3`) | `arrow_of_three` | `Reduction.lean` |
| Lemma 5.2 (`n = 2` ⇒ `n ≥ 2`) | `arrow_of_two_voters` | `Reduction.lean` |
| Base case ⇒ Thm. 2.1 | `arrow_of_base`, `arrow_two_three`, `arrow_base` | `Reduction.lean`, `Main.lean` |
| Sec. 4.1 (cylinder `C₁` is dictatorial) | `not_admits_C1`, `not_admits_C2` | `Domains.lean` |
| Prop. 4.1 (existence, maximality) | `prop41_admits`, `prop41_maximal`; condition needed: `prop41_equal_blueEdge` | `Domains.lean` |
| Prop. 4.1, last sentence — false as stated (missing hypothesis) | counterexample `prop41_moreover_false` (via `not_admits_ABC_ACB`); corrected `prop41_moreover_of_pairFree` | `Domains.lean` |
| Thm. 4.2 — **false** for adjacent blue edges | `thm42_false`, `thm42_counterexample`, `thm42_not_admits_of_adjacent`; true part: `thm42_admits_of_disjoint`, `thm42_maximal`; "moreover": counterexample `thm42_moreover_false`, corrected `thm42_moreover_of_pairFree` | `Domains.lean` |
| Full-version Thm. 6 (characterization, all pairs free) | `thm6` | `Domains.lean` |
| Full-version example triple is not critical | `paper_triple_example_not_critical` | `Domains.lean` |
| Sec. 4.2 polarised domain: `F` well defined, unanimous, IIA, non-dictatorial | `ThreeAlts.polarised_admits`, `polarF_P_AB/AC/BC`, `polarised_nonDictatorial` | `Polarised.lean` |
| Sec. 4.2 "not contractible" (proxy: f-vector `(12, 36, 16)`, `χ = −8 ≠ 1`) | `polarised_fVector`, `polarised_euler` | `Polarised.lean` |
| Bridge: domains ↔ sign functions | `ThreeAlts.admitsNonDictatorial_iff_sign`, `AdmitsNonDictatorial.mono` | `DomainBridge.lean` |
| Sec. 2.3.2 vertex counts (any finite `X`) | `card_VI`, `card_VO` | `VertexCount.lean` |
| Sec. 6 counts (36 = 64 − 28 triangles, 24 + 12, `N_O` = 8 − 2) | `NI_vertices`, `NI_triangles`, `NI_triangles_eq_chromatic_minus`, `NI_distinct_labels`, `NO_triangles` | `Counts.lean` |

## Files

- `SignModel.lean`, `ThreeAlt.lean`: sign model and its link with profiles (three alternatives).
- `Complexes.lean`: `N_I`, `N_O`, Propositions 3–4, chromaticity of unanimous maps.
- `Orientation.lean`: Lemma 3.2. `BaseCase.lean`: Section 3.3. `Reduction.lean`: Section 5. `Main.lean`.
- `DomainBridge.lean`: reduction of domain statements to sign functions. `Domains.lean`: Section 4.1, Prop. 4.1,
  Thm. 4.2, full-version Thm. 6 (concrete `Alt = {A, B, C}`, the six orders `Ord3`, profiles `Prof2`, Bool
  checker `admitsB` with soundness and completeness proofs). `Polarised.lean`: Section 4.2. `Counts.lean`: Section 6 counts.
  `VertexCount.lean`: Section 2.3.2.

## Infrastructure / CSLib candidates

- `Cslib/Foundations/SocialChoice/Aggregation.lean` (whole file; now in CSLib): preferences, `ofRank`, `extend`,
  Arrow's axioms, restricted domains. Also the helpers `rank3`, `rank4`, `exists_ne_ne`, `restrictAgg`
  in `Reduction.lean`.
- `Cslib/Foundations/Combinatorics/SimplicialComplex/Nerve.lean` (nerves, simplicial maps) and
  `Cslib/Foundations/Combinatorics/SimplicialComplex/IndexLemma.lean` (generalized index lemma) — both now in CSLib.
- Arrow's theorem itself (`theorem_2_1` with Lemmas 5.1/5.2 and Props 3/4) would be a natural CSLib addition
  together with `Cslib/Foundations/SocialChoice/`.
