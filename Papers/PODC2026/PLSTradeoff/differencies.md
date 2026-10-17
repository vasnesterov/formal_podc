# Differences between the formalization and the paper

Paper: A. Filtser, O. Fischer, *Near-Resolution of the Tradeoff Conjecture in Distributed Proof
Labeling Schemes*, PODC 2026 (arXiv:2605.19078v1). Numbering follows the arXiv version.

## Errors and imprecisions in the paper

1. **Theorem 1.6, ball-size claim: false for `t = 1`** (false only in a degenerate case). The paper
   claims `min_v |B_t(v)| = Ω(|V(G_{t,m})|)` for the whole family `t, m ≥ 1`. For `t = 1` a node of
   an even layer has exactly two neighbours, so `|B_1(v)| = 3` while `|V| = 2m + 3`
   (`Layered.ball_t1_counterexample`, `Layered.ball_inr_one`). For `t ≥ 2` (and `m ≥ 1`) the claim
   holds with constant `1/3` (`Layered.ball_large`). The lower bound part of Theorem 1.6 is
   unaffected (and for `t = 1` the question is moot, since a 1-PLS is a `t`-PLS).
2. **Lemma 5.6 is false for `n < r / O(1)`** (false only in a degenerate case). It claims, for every
   `r ≥ 1`, an `O(r)`-PLS sharing any `r`-bit string with `O(1)` bits per node. On a graph with
   `n` nodes the labelings with `c` bits per node can encode fewer than `2^{(c+1)n}` strings, so
   this is impossible when `r > (c+1)n`. The proof uses Lemma B.1, which assumes `|V| > r`. The
   correct cost is `O(1 + r/n)`; we prove cost `2⌈r/n⌉ + 8` with radius `4r + 2`
   (`exists_stringShare`; sharper: radius `2r+1`, cost `2⌈r/n⌉ + 6`). In the application
   (`r ≈ 2 log₂ n`) this is `O(1)`, so Theorem 1.2 is unaffected.
3. **Lemma 4.5: the stated radius does not match the verifier** (proof gap; statement true). The
   proof builds an `r`-PLS with `r = 3t + 2`, but node `v` reconstructs
   `C̃_u(v) = {w ∈ B_r(u) | …}` for nodes `u` at distance up to `r + 2`, which requires seeing
   radius about `2r + 2`. We search clusters within radius `2t` instead of `3t + 2` (enough: a node
   of `Ĉ_v` is within `t` of `v` by `v`'s diameter check, and then `Ĉ_u = Ĉ_v` follows from the two
   diameter checks), and then radius `3t + 2` does suffice (`exists_tsCert`). We also check only the
   node's own cluster (weak diameter, ratio) and two separation at the node itself; since every
   node checks, this is equivalent.
4. **Lemma 5.1, last inequality** (proof slip; statement true). From `|Bad_i| ≥ t log n + 1` the
   proof derives `|B ∩ L_i| ≥ (1 + 1/t)^{t log n} |B_{2t log n}(v_i) ∩ L_i| > n`, but
   `(1+1/t)^{t log n} ≥ n` only gives `≥ n`. The missing strict factor comes from the first bad
   radius itself (`|B_{r'_1}| > (1+1/t)|B_{r'_1 - 2}|`). Our proof (`card_bad_le`) counts this
   factor. The same strictness issue appears in the warm-up overview ("`(1+1/t)^{Θ(t log n)} > n`");
   the warm-up formalization uses `K = t⌈log₂ n⌉ + 1` steps.
5. **Corollary 5.4 / Lemma 5.2 assume `n ≥ 2t log n`; Theorem 1.2 does not** (proof gap in a
   degenerate case). The case `n < 2t log n` is not treated. Our counting proof
   (`card_not_allClustered`) covers all `n`: in a connected graph the ball `B_{2K}(u)` has at least
   `min(n, 2K + 1)` nodes (`card_ball_ge`), and both cases give failure probability `≤ 1/(2n)` per
   node.
6. **Lemma 5.5 (Newman's trick), count of graphs** (imprecision). The union bound uses
   `|G_n| ≤ 2^{n choose 2}`, but graphs with identifiers from `[poly(n)]` are more numerous (the
   choice of the identifier set adds a factor `poly(n)^n`); the bound `n^{-n²}` still wins. In our
   model the identifier set is the fixed node type, and we use failure probability `≤ 1/2` per graph
   with `n² + 1` samples (`exists_good_family`), which needs only `|G_n| ≤ 2^{n²}`.
7. **"Cost `O(⌈p/t⌉)`" for `p = 0`** (typo-level). The schemes always use a constant number of bits,
   so the bound should read `O(⌈p/t⌉ + 1)` (Section 5 itself speaks of "constant additive factors").
   Our Theorem 1.2 has cost `2⌈(2p+1)/t⌉ + 64`.
8. **Theorem 1.4 / Lemma 4.2 need `2/t ≤ δ`** (implicit). The paper writes `t = Ω(1)`. For smaller `t`
   the 1-PLS itself is a `t`-PLS of cost `p = O(⌈p/t⌉)`. Our `tradeoff_of_padded` assumes `2/t ≤ δ`.

## Modelling choices and changed definitions

* **Nodes and identifiers.** The node set is a fixed finite type `V` with a linear order (the
  identifiers); a configuration family is a set `𝒢` of graphs on `V` together with all input
  assignments `V → ι`. Hence `n = |V|` is known to everybody (the paper assumes the verifier knows
  `n`); the verifier formally also "knows" the set of all identifiers. So the identifier space equals the
  node set, a special case of the paper's identifiers from `[poly(n)]`. The constructions of
  Lemmas 3.2, 4.5 and 5.6 use only `n`, the identifiers in the view and the view itself, but the
  Newman family of Theorem 1.2 (`exists_good_family`) is a function on `V` and is chosen by counting
  over graphs on `V` only; for identifiers from `[poly(n)]` the count must include the choice of
  the identifier set (item 6), which is not formalized.
* **Locality.** `IsLocal R f`: the output at `v` is equal for any two labelled configurations that
  agree on all edges incident to nodes at distance `< R` from `v` and on the inputs and labels of all
  nodes at distance `≤ R` (exactly what `R` LOCAL rounds reveal; for `R = 1` this is the standard PLS
  view). Verifiers are arbitrary (not necessarily computable) functions, as in the paper (the leader
  of Lemma 3.2 performs an exhaustive search).
* **Labels and cost.** Labels are `List Bool`; `PLS.CostLE p` bounds the honest prover's label
  length on yes-instances of the family. Tuples of strings use our own self-delimiting encoding
  (`encList`, `2|s| + 1` bits per string) instead of an unspecified "fixed delimiter scheme"; this
  changes only constants.
* **Explicit constants** instead of `O(·)`:
  * Lemma 3.2: radius `max(R, 2t+2)`, cost `2c + 2⌈ε(2p+1)⌉ + 2`.
  * Lemma 4.5: radius `3t+2`, cost `2⌈log₂ n⌉ + 4`.
  * Warm-up / Corollary 4.7: radius `12t⌈log₂ n⌉ + 14`, cost `4⌈log₂ n⌉ + 2⌈(2p+1)/t⌉ + 10`.
  * Theorem 1.2: radius `40t⌈log₂ n⌉ + 32`, cost `2⌈(2p+1)/t⌉ + 64` (connected graphs).
  * Theorem 1.4 (conditional): radius `3t+2`, cost `4⌈log₂ n⌉ + 2⌈2β(2p+1)/t⌉ + 10`.
  * Lemma 6.4: `m ≤ 4(t+1)p` (from `m² ≤ 2p|V|`).
* **Partitions.** A partition is a cluster map `cl : V → Set V` (`v ∈ cl v`, `u ∈ cl v → cl u = cl v`);
  an ordered partition (Definition 3) is a cluster index `idx : V → ℕ`. Two separation is stated for
  walks as in the paper and proved equivalent to "non-`X` nodes of different clusters are at distance
  `> 2`" (`twoSep_iff`).
* **Definition 4 outputs.** `Comp(v)` and `X_C(v)` are represented by a cluster map and a set of
  marked nodes, correct on the clusters of all nodes within distance 2 of `C_v` (`TSOut.Correct`).
* **Lemma 3.2 construction.** The `Lex` splitting does not pad (the last blocks may be shorter); the
  leader's check that the decoded tuple has `|C ∩ X|` entries is dropped (soundness does not need
  it: malformed encodings decode to some labeling anyway). The leader is the largest identifier of
  `C \ X`, as in the paper.
* **Warm-up construction (Section 1.1).** Balls of even radius `2k`, `1 ≤ k ≤ t⌈log₂ n⌉ + 1`, so
  weak diameter `≤ 4(t⌈log₂ n⌉ + 1)`. The paper derives Corollary 4.7 from Bartal's padded
  decompositions; we derive the same statement from the warm-up (as the overview does).
* **Algorithm `A` (Section 5.1).** Defined by well-founded recursion on the identifier order
  (`taken`), with the cluster of `u` given by `FindMyCluster` (`cen`), so Lemmas 5.8/5.9 become the
  characterization `cen_eq_iff`. Radius indices range over `Fin (3K+3)` (radii `2K+2, …, 8K+6`, where
  `K = t⌈log₂ n⌉`) instead of `{2K+2, …, 8K}`, so that `n = 1` is not degenerate; weak diameter
  `16K + 12`. Probability is replaced by counting over all assignments `V → Fin (3K+3)` (uniform
  distribution), via fibre counting along the identifier order
  (`Cslib.Probability.pow_mul_card_filter_forall_le`).
* **Section 5.2 verifier.** The reconstructed cluster of `u` keeps only nodes within `2ρ` of `u`
  (`ρ = 8K + 6` the largest radius), which makes it computable in the local view without changing it.
  The shared index is decoded by `decIdx`; garbage strings decode to index `0`.
* **Lemma 5.6.** Proved with a different (simpler) verifier: bounded clusters reachable by short walks
  through marked nodes, no maximality or size checks, radius `2r + 1` (see `StringShare.lean`). Lemma
  B.1 is proved by an extremal argument with clusters of size `min(r, n)`; Lemmas B.2/B.3 are not
  needed. `r = 0` is handled separately.
* **Padded decompositions (Definition 6).** A distribution is a finite family of weighted partitions
  (all distributions over partitions of a finite set are of this form); `Λ` ranges over naturals
  `≥ 1` (the paper: reals `> 0`), which weakens the hypothesis of Theorem 1.4.
* **Theorem 1.6.** The configuration family is the singleton `{G_{t,m}}` for each `t, m` (stronger
  lower bound). The 1-PLS of Lemma 6.3 checks consistency by node identity instead of the
  degree-based case analysis of Lemma 6.2, so "`m` odd, `m ≥ 3`" is not needed; labels are rows of
  the input matrix without index tags (cost exactly `m`). Lemma 6.1 (nondeterministic equality) is
  not assumed: the lower bound is proved by a direct fooling-set argument.

## Not formalized

* Theorem 4.1 (Conroy–Filtser padded decompositions of `K_r`-minor-free graphs), Theorem 4.6
  (Bartal), hence Corollary 4.4 and the unconditional Theorem 1.4: Theorem 1.4 is proved assuming the
  padded decomposition scheme (`tradeoff_of_padded`).
* Corollary 1.3 (MST verification; needs the 1-PLS of Korman–Kutten).
* Planarity of `G_{t,m}` (Theorem 1.6).
* The closing remarks of Section 5 on removing the knowledge of `n` and connectivity.
