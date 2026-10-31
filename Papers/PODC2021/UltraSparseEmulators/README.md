# Ultra-Sparse Near-Additive Emulators — PODC 2021

Michael Elkin, Shaked Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021. DOI
[10.1145/3465084.3467926](https://doi.org/10.1145/3465084.3467926). Formalized version: arXiv
[2106.01036](https://arxiv.org/abs/2106.01036) v1; numbering follows it. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The centralized result of Section 2 is correct: for every
`ε ∈ (0,1)` and integer `κ ≥ 2`, Algorithm 1 builds a `(1+ε, 30(34 log κ/ε)^{log κ − 1})`-emulator with
at most `n^{1+1/κ}` edges (leading constant 1), in every order of consideration. It is ultra-sparse
(`n + o(n)` edges) for `κ ≈ log n · log log n`. The new charging argument (eqs. (2)–(4)) is correct as
written. The minor issues: line 18 of Algorithm 1 has a typo that, read literally, breaks the
algorithm; the inequality `⌈log((κ+1)/2)⌉ ≤ log κ` needs `κ` to be an integer, which is the paper's
convention.

## Mistakes in the paper

* **Algorithm 1, line 18 (typo with evident intent).** The line moves to `N_i` all `r_{C''} ∈ S_i`
  "such that `d_G(r_C, r_{C'}) ≤ 2δ_i`". The condition mentions `r_{C'}`, the variable of the previous
  loop, not `r_{C''}`. Read literally, it is always true, so every center still in `S_i` moves to
  `N_i` and later joins the new supercluster, however far away it is. That destroys the radius bound
  (Lemma 2.5). The prose of Section 2.1.1 (`δ_i < d_G(r_C, r_{C''}) ≤ 2δ_i`) gives the intended rule,
  which is what we formalize (`step`).
* **`⌈log((κ+1)/2)⌉ ≤ log κ` "for all `κ ≥ 2`" (Section 2.2.4) holds only for integer `κ`.** For
  `κ = 7/2` the left side is 2 and the right side is `log₂ 3.5 ≈ 1.81`. With `ε = 1/2` the stated `β`
  bound then fails as well (`not_numPhases_le_logb`, `not_rescale_seven_halves`). The paper's
  convention is `κ = 1, 2, …`, and for integers the claim holds (`numPhases_le_logb_natCast`).
  Corollary 2.15 plugs in `κ = f(n) log n`; rounding it to an integer costs nothing. Under the
  paper's convention this is an imprecision, not an error.
* **Corollary 2.15's derivation is incomplete; the corollary holds.** The text sets `κ = f(n) log n`
  for an arbitrary `f = ω(1)`. That gives `n + o(n)` edges, but `β = (log log n/ε)^{(1+o(1)) log log n}`
  requires a slowly growing `f` (e.g. `f(n) = n` gives `β ≈ (log n/ε)^{log n}`). We use
  `f = log₂ log₂ n` (`corollary_2_15`).
* **Proof gaps in Lemma 2.10, all easily repaired.** The lemma is stated for the *minimal* index `i`,
  but the induction hypothesis is applied to subpaths whose minimal index may be smaller. We prove it
  for every walk and every admissible `i`, with no shortest paths needed. If the first
  `U_i`-clustered vertex of a segment is its left endpoint, the predecessor `w₁` does not exist; this
  case is trivial. Eq. (8) uses laminarity (`r₁' ∈ C₁`), which is stronger than what Lemma 2.9 states.
  (`Hierarchy.lemma_2_10`)
* **Typos.** `R_{i+1} = 2δ_i + R_i` is defined "for `i ∈ [1, ℓ]`", leaving `R_1` undefined. The
  recursions for `α_i, β_i` say "for `i > 1`" (meant: `i ≥ 1`). Eq. (13) and the rescaled `β` use `=`
  where `≤` is meant.

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
