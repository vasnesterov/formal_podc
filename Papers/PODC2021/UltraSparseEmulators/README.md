# Ultra-Sparse Near-Additive Emulators — PODC 2021

Michael Elkin, Shaked Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021. DOI
[10.1145/3465084.3467926](https://doi.org/10.1145/3465084.3467926). Formalized version: arXiv
[2106.01036](https://arxiv.org/abs/2106.01036) v1; numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The centralized result of Section 2 holds: for every `ε ∈ (0,1)` and integer `κ ≥ 2`,
Algorithm 1, with the wrong variable of line 18 corrected, builds a `(1+ε, 30(34 log κ/ε)^{log κ − 1})`-emulator with
at most `n^{1+1/κ}` edges (leading constant 1), in every order of consideration, and it is ultra-sparse (`n + o(n)`
edges) for `κ ≈ log n · log log n`. The new charging argument (eqs. (2)–(4)) is correct as written, and the gaps in
Lemma 2.10 and Corollary 2.15 need only local repairs. The CONGEST algorithm and the spanners were not checked.

## Mistakes in the paper

### ✏️ Slips
- Algorithm 1, line 18 (condition on the wrong variable). Line 18 moves to `N_i` all `r_{C''} ∈ S_i` "such that
  `d_G(r_C, r_{C'}) ≤ 2δ_i`". The condition mentions `r_{C'}`, the variable of the previous loop, not `r_{C''}`.
  Read literally, it is always true, so every center still in `S_i` moves to `N_i` and later joins the new
  supercluster however far away it is, which destroys the radius bound (Lemma 2.5). The prose of Section 2.1.1
  (`δ_i < d_G(r_C, r_{C''}) ≤ 2δ_i`) gives the intended rule, which is what we formalize (`step`).
- Section 2.2.4, `⌈log((κ+1)/2)⌉ ≤ log κ` "for all `κ ≥ 2`". The inequality fails for non-integer `κ`: for
  `κ = 7/2` the left side is 2 and the right side is `log₂ 3.5 ≈ 1.81`, and with `ε = 1/2` the stated `β` bound
  fails as well (`not_numPhases_le_logb`, `not_rescale_seven_halves`). The paper's convention is `κ = 1, 2, …`, and
  for integers the claim holds (`numPhases_le_logb_natCast`). Corollary 2.15 plugs in `κ = f(n) log n`; rounding it
  to an integer costs nothing.
- Eq. (13) and the rescaled `β` of Section 2.2.4 use `=` where `≤` is meant.
- Lemma 2.10, Case 2: if the first `U_i`-clustered vertex of a segment is its left endpoint, the predecessor `w₁`
  does not exist; this case is trivial.
- Eq. (8) uses laminarity (`r₁' ∈ C₁`), which is stronger than what Lemma 2.9 states; the sentence before the lemma
  announces it, and the lemma's proof gives it.

### Typos
- `R_{i+1} = 2δ_i + R_i` is defined "for `i ∈ [1, ℓ]`", leaving `R_1` undefined.
- The recursions for `α_i, β_i` say "for `i > 1`" (meant: `i ≥ 1`).
- Eq. (12) includes the term `j = 0` with `(1/ε)^{-1}` (harmless: `R_0 = 0`).
- The introduction of Section 2.2 announces the running-time and stretch sections in the opposite order.

## Proof gaps (statements true)

### 🔧 Corollary 2.15 (choice of `f`)
The derivation sets `κ = f(n) log n` for an arbitrary `f = ω(1)`, but the claimed `β` holds only for a slowly
growing `f`.

**Impact.** The corollary holds; we use `f = log₂ log₂ n` (`corollary_2_15`).

**Details.** Any `f = ω(1)` gives `n + o(n)` edges, but `β = (log log n/ε)^{(1+o(1)) log log n}` requires a slowly
growing `f` (e.g. `f(n) = n` gives `β ≈ (log n/ε)^{log n}`).

### 🔧 Lemma 2.10 (induction on the minimal index)
The lemma is stated for the *minimal* index `i`, but the induction hypothesis is applied to subpaths whose minimal
index may be smaller.

**Impact.** The lemma holds; dropping "minimal" from the statement repairs the induction (`Hierarchy.lemma_2_10`).

**Details.** As printed, the step needs monotonicity of `α_j, β_j`, which is true but not stated.

**Repair.** We prove the lemma for every walk and every admissible `i`, with no shortest paths needed.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Centralized, deterministic. Input: a finite, unweighted, undirected graph `G : SimpleGraph V`, possibly
  disconnected; `n = |V|`.
* Output: a graph `H` on the same vertices whose edge `{x, y}` weighs `d_G(x, y)` (`distW G`). It is an
  `(α, β)`-emulator (`SimpleGraph.IsEmulator`, staged in `Podc/`) iff `d_G ≤ d_H ≤ α·d_G + β` for all
  pairs, with `d = ⊤` between disconnected vertices.
* Algorithm 1 is modelled phase by phase on the set of cluster centers. Each center has a status
  `S/N/U/T/J` (in `S_i`, in `N_i`, unclustered, new supercluster center, joined). Clusters are
  reconstructed from the "joined" pointers.
* The arbitrary order of line 6 is an arbitrary list `ord i` of all vertices per phase; centers no
  longer in `S_i` are skipped. Every execution has this form, and all theorems quantify over all
  orders.
* Parameters are exactly those of Section 2.1.2, with `κ` an integer.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Algorithm 1 | `step`, `phase`, `run`, `ultraSparseEmulator` | `Algorithm.lean`, `Main.lean` |
| Lemmas 2.1, 2.2 (counted form) | `card_centers_succ` | `Analysis.lean` |
| Lemma 2.3 | `lemma_2_3` | `Main.lean` |
| Eq. (1) (`|P_ℓ| ≤ deg_ℓ`) | `eq_1_centers` | `Main.lean` |
| Eqs. (2)–(4), Lemma 2.4 | `card_edges_phase`, `card_edges_le`, `lemma_2_4` | `Analysis.lean`, `Main.lean` |
| Lemma 2.5 | `radius_le` | `Analysis.lean` |
| Lemmas 2.6, 2.12, eqs. (5), (12), (13) | `lemma_2_6`, `lemma_2_12`, `eq_5`, `eq_12`, `eq_13` | `Params.lean` |
| Lemmas 2.7, 2.8, 2.9 | fields `inter`, `lev_le`, `nest` of `hierarchy` (invariants `PInv.U_edge`, `PInv.sep`) | `Analysis.lean`, `Phase.lean` |
| Lemma 2.10 | `Hierarchy.lemma_2_10` | `Stretch.lean` |
| Corollary 2.11 | `Hierarchy.isEmulator`, `corollary_2_11` | `Stretch.lean`, `Main.lean` |
| Corollary 2.13 (+ Lemma 2.4) | `corollary_2_13` | `Main.lean` |
| Section 2.2.4 (rescaling) | `rescale_natCast` | `Params.lean` |
| Corollary 2.14 | `corollary_2_14`, `exists_emulator` | `Main.lean` |
| Corollary 2.15 | `corollary_2_15` | `Corollary215.lean` |
| `⌈log((κ+1)/2)⌉ ≤ log κ` false for real `κ` | `not_numPhases_le_logb`, `not_rescale_seven_halves` | `Params.lean` |

**Not formalized.** Running time (Section 2.2.3, "polynomial time"; the Lean algorithm is a
noncomputable definition). The CONGEST algorithm and the faster centralized algorithm (Section 3),
and the spanners of Section 4.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: the hypotheses are only `0 < ε < 1`, `κ ≥ 2`, and that each order lists
every vertex; `exists_emulator` instantiates the order with `Finset.univ.toList`. Weighted distances
come from CSLib (`SimpleGraph.wdist`, `WeightedSpanner.lean`); graph distances from Mathlib.
