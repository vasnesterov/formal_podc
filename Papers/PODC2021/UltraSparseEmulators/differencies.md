# Differences between the formalization and the paper

Paper: Elkin, Matar, *Ultra-Sparse Near-Additive Emulators*, PODC 2021, arXiv:2106.01036v1.
Scope: the centralized construction of Section 2 (Algorithm 1, Lemmas 2.1–2.12, Corollaries
2.11, 2.13–2.15). Not formalized: the running-time analysis (Section 2.2.3), the CONGEST algorithm
(Section 3), the faster centralized algorithm (Section 3.3, Theorems 3.13–3.14), and the spanners of
Section 4.

## Statement-level issues in the paper

1. **Algorithm 1, line 18 (typo, R3 → ⚠️).** The line reads "for all clusters `r_{C''} ∈ S_i` such that
   `d_G(r_C, r_{C'}) ≤ 2δ_i`". The condition uses `r_{C'}`, the loop variable of lines 14–17, not
   `r_{C''}`. Taken literally, the condition does not depend on `r_{C''}` and is true (`r_{C'}` was within
   `δ_i`), so every remaining center of `S_i` moves to `N_i` and later joins the supercluster at any
   distance. Then the radius bound (Lemma 2.5) fails. The prose of Section 2.1.1 states the intended
   rule (`δ_i < d_G(r_C, r_{C''}) ≤ 2δ_i`), and we formalize that (`step`). Decided by R3: the fix is
   local and recoverable from the paper.
2. **`ℓ ≤ log κ` needs integer `κ` (R4, no label change).** Section 2.2.4 claims
   `⌈log((κ+1)/2)⌉ ≤ log κ` "for all `κ ≥ 2`". This is false for real `κ`: for `κ = 7/2`, the left side
   is `2` and the right side is `log₂ 3.5 ≈ 1.81` (`not_numPhases_le_logb`). The β bound of
   Corollary 2.14 then fails too for, e.g., `κ = 7/2, ε = 1/2` (`not_rescale_seven_halves`). The
   paper's convention is `κ = 1, 2, …` (Introduction), and for integers the claim holds
   (`numPhases_le_logb_natCast`). So we take `κ : ℕ`. Corollary 2.15 substitutes
   `κ = f(n) log n`, which is not an integer in general; rounding it up (as we do, `kappa`) costs
   nothing. No label change: R4, the integer assumption is the paper's own standing convention.
3. **Corollary 2.15's derivation is incomplete (imprecision, no label change).** The text derives
   Corollary 2.15 from "`κ = f(n) log n` for any `f(n) = ω(1)`". That gives `n + o(n)` edges for every
   such `f`, but the claimed `β = (log log n/ε)^{(1+o(1)) log log n}` holds only for slowly growing `f`
   (`log f(n) = o(log log n)`). For `f(n) = n` it fails. The corollary itself is existential ("our
   algorithm constructs … with … β = …"), so it holds with a suitable `f`; we use `f = log₂ log₂ n`.

## Proof-level gaps (repaired, statements true)

4. **Lemma 2.10, induction with "minimal index".** The lemma is stated for the *minimal* `i` such that
   the path is `U^{(i)}`-clustered. The proof applies the induction hypothesis to subpaths that are
   `U^{(i-1)}`-clustered, whose minimal index may be smaller. This needs `α_j ≤ α_{i-1}`, `β_j ≤ β_{i-1}`
   (true, unstated). We prove the stronger statement for every walk and *every* `i` such that the walk
   is `U^{(i)}`-clustered (`Hierarchy.lemma_2_10`). Shortest paths are not needed at all.
5. **Lemma 2.10, Case 2: `w₁` may not exist.** If the first `U_i`-clustered vertex `z₁` of a segment is
   its left endpoint `x`, it has no predecessor `w₁`. That case is trivial (`d_H(x, r₁) ≤ R_i`) and we
   treat it separately (`segment`).
6. **Lemma 2.9 is weaker than what is used.** Eq. (8) needs `r₁' ∈ C₁`, i.e. the `P_j`-cluster of `z₁`
   is *contained* in its `P_i`-cluster (laminarity, as the sentence before the lemma says). The lemma
   only states that some `C' ∈ P_j` contains `v`. Our `Hierarchy.nest` states and proves laminarity in
   the form used.
7. **Lemma 2.1 per supercluster vs. in aggregate.** We prove only what Lemma 2.3 and eq. (3) use:
   `deg_i · #(new superclusters) ≤ #(clusters that joined)`, hence `|P_{i+1}|(deg_i + 1) ≤ |P_i|`
   (`card_centers_succ`). Lemma 2.2 (disjointness) is built into the representation: each center has
   one status.
8. **Telescoping (Lemma 2.4).** The paper uses `P_{ℓ+1} = ∅`. The sum telescopes to
   `deg_0 |P_0| − deg_{ℓ+1}|P_{ℓ+1}| ≤ n^{1+1/κ}` without it (`card_edges_le`). Our size bound holds after
   any number of phases.

## Typos / slips (no effect)

9. Section 2.1.2 defines `R_{i+1} = 2δ_i + R_i` "for every `i ∈ [1, ℓ]`", leaving `R_1` undefined.
   The intended range is `i ∈ [0, ℓ-1]` (Lemma 2.6 gives `R_1 = 2`). We define `R` for all `i`.
10. The recursions for `β_i` and `α_i` are stated "for `i > 1`". They are meant for `i ≥ 1`.
11. Eq. (13) states `α_i = 1 + 34εi`. It is an upper bound (`eq_13`). Likewise the rescaled β in
    Section 2.2.4 is written with `=` where `≤` is meant.
12. Eq. (12) includes the term `j = 0` with `(1/ε)^{-1}` (harmless: `R_0 = 0`).
13. Section 2.2 says the running time is analysed in Section 2.2.3 and the stretch in Section 2.2.2,
    but lists them in the opposite order.

## Modelling choices

- **Graph.** `G : SimpleGraph V` on a finite type `V`, `n = |V|`, unweighted, undirected, possibly
  disconnected. Distances: Mathlib's `G.dist`/`G.edist`. Two centers are "neighbouring"
  (`Near G δ x y`) iff they are connected and `d_G(x, y) ≤ δ`. The paper uses `d_G ≤ δ` with
  `d_G = ∞` for disconnected vertices, which is the same.
- **Emulator.** A `SimpleGraph V` `H` with edge weight `w({x, y}) = d_G(x, y)` (`distW G`), distances
  `H.wdist` from CSLib. `IsEmulator G H w α β` means `d_G ≤ d_H ≤ α d_G + β` for all pairs, with
  `d = ⊤` between disconnected vertices. The paper allows emulators with extra vertices; the
  construction uses none. Parallel edges inserted in different phases are merged. This only lowers
  the edge count.
- **Order of consideration.** Line 6 removes "a cluster center" from `S_i` in an arbitrary order. We
  process the vertices in the order of an arbitrary list `ord i` containing all vertices, skipping
  those no longer in `S_i`. Every run of the while loop corresponds to such a list: append the
  remaining vertices to the sequence of considered centers. Conversely, every list gives a run. All
  results are stated for every `ord`. That is, they hold for every execution of Algorithm 1.
- **Clusters** are represented by their centers. A phase only needs the set of centers. Clusters are
  reconstructed as `ctr (i+1) v = par_i (ctr i v)`, where `par_i` maps a joined center to its
  supercluster center (`Analysis.lean`).
- **Parameters.** `δ_i = (1/ε)^i + 2R_i`, `deg_i = n^{2^i/κ}`, `ℓ = ⌈log₂((κ+1)/2)⌉`, exactly as in
  Section 2.1.2. `ε > 0` is added (the paper writes `ε < 1`). Corollary 2.13 assumes `ε ≤ 1/10` as the
  paper does. Corollary 2.14 runs the algorithm with `ε/(34ℓ)` as in Section 2.2.4 and states the
  explicit `β = 30(34 log₂ κ/ε)^{log₂ κ − 1}` instead of `O(log κ/ε)^{log κ − 1}`.
- **Corollary 2.15** is stated with explicit `g(n) = o(n)` and `h(n) → 0`:
  `|E(H)| ≤ n + g(n)` and `β = (log₂ log₂ n/ε)^{(1+h(n)) log₂ log₂ n}`, for `κ(n) = ⌈log₂ n · log₂ log₂ n⌉`
  and all large `n`. The `o(1)` term `h` is allowed to depend on `ε` (as usual for a fixed accuracy
  parameter); `g` does not.
- **Running time** ("polynomial deterministic time"): not formalized. The algorithm is a
  noncomputable Lean definition.
