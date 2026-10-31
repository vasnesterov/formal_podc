# Differences between the formalization and the paper

Paper: Bitton, Emek, Izumi, Kutten, *Message Reduction in the LOCAL Model is a Free Lunch*, PODC 2019,
arXiv 1909.08369v1.

## Statement-level issues (with the deciding rule)

1. **Theorem 1.2 (size clause) and Lemma 4.7 are false** (❌, R3 not applicable, R5 → not 🚨).
   - Claim: `|S| ≤ Õ(n^{1+1/(2^{k+1}−1)})` whp, for every `1 ≤ k ≤ log log n`, `0 ≤ h ≤ log n`.
   - Counterexample: `k = 1`, `h = 2`, `K_n`. With probability `≥ 1/8`, `|S| ≥ n s/8 = Ω(n^{11/6} log³ n)`
     (`theorem_1_2_size_false`; for any `C`, `D` and all large `n`, `P(|S| > C n^{4/3} log^D n) ≥ 1/8`).
   - Not R3: the fix changes either the claimed bound (`n^{1+δ}` → `n^{1+δ+ε}`) or the algorithm
     (capping `F_v` inside a trial), and the paper's proof reasons with the wrong count. The prose
     "each node `v` tries to identify `min{c n^{2^j δ} log n, |N_j(v)|}` neighbors" hints at a cap, but
     both the prose ("advances to the next trial unless `|F_v| ≥ …`") and Pseudocode 2 test the
     threshold only between trials. The proof of Lemma 4.7 does not use a cap either: it multiplies a
     per-trial count `O(n^{2^j δ} log³ n)` (that is `s_j` without the factor `n^ε`) by the number of
     trials. So the error is in the counting, not a pseudocode typo.
   - Not R4: the parameter range `0 ≤ h ≤ log n` is explicit, and the counterexample uses constant `h`. For
     `h = Θ(log n)`, `n^ε = O(1)` and the claim holds.
   - Not 🚨 (R5, borderline). The headline claims hold: the abstract's spanner with "constant stretch
     and `O(n^{1+ε})` edges … sending `O(n^{1+ε})` messages" (choose `δ, 1/h ≤ ε/3`), and Theorem 1.3.
     Theorem 1.2 names `Sampler`, but only its precise size/parameter trade-off is false, not the
     algorithm's headline guarantee. The case for 🚨: the introduction calls `Sampler` with the
     guarantees of Theorem 1.2 "our main technical contribution". Against it: the abstract and the
     title result (Theorem 1.3) do not depend on the false exponent, and `Sampler` itself, with its
     size bound corrected to the paper's own message bound `Õ(n^{1+δ+ε})`, delivers them. Lemma 4.7 is a numbered lemma (❌ by R1).
2. **Lemma 4.3 proof: class intervals** (proof repair 🛠️, inside a proof). The classes
   `(n^{xε}, n^{(x+1)ε}]` exclude volume 1. We use `[b^x, b^{x+1})` via `cls = ⌊log_b vol⌋`.
3. **`V' = ⋃_{1≤j≤k−1} V'_j`** (typo inside the proof of Theorem 4.6; the intent `0 ≤ j ≤ k` is
   evident from the proof). In Lean, the final cluster of `x` is `(lvl x, cl (lvl x) x)` with
   `lvl x ≤ k` maximal (`Run.label`).
4. **`h = 0` allowed in Theorem 1.2** (degenerate, R2): `ε = 1/h` is undefined. We use `h ≥ 1`.

## Modelling choices

- **Centralized algorithm only.** We formalize Sections 3–4. The LOCAL implementation (Section 5),
  Theorem 5.1 and Section 6 are not formalized.
- **Runs as relational outcomes.** `Run G k` fixes merge maps, center marks and `F` sets satisfying the
  postconditions of Pseudocode 2 (`F_sub`, `merge_center`, `merge_some`, `merge_ne_none`). This covers
  every outcome of the coins. The first-step loop is not part of `Run`. It is modelled separately, per
  node, in `Lemma43.lean`, and Theorem 4.6 takes the conclusions of Lemmas 4.2/4.3 as hypotheses.
- **Node identities.** A level-`j` node is identified with a vertex of `V` (its root). This is faithful
  because each level-`(j+1)` node is a level-`j` center.
- **Multigraphs.** `G_j` is not built as a separate multigraph: `E_j(a, b)` is the set of original
  edges between the clusters `C_j(a)`, `C_j(b)` (`cross`). This is the paper's definition of the
  cluster graph.
- **Merge rule.** We follow Pseudocode 2, line 19 (an edge of `F = ⋃_u F_u` to a center), not the prose
  ("a center contained in `N̂_j(v)`"). The stretch proof only needs that unclustered nodes are light.
  Lemma 4.2's conclusion is used as "light, or queried some center" (hypothesis `h43`).
- **Stretch constant.** The paper writes `O(2·3^k − 1)`; we prove exactly `2·3^k − 1`. Lemma 4.4's
  hypothesis is weakened from "`Ind_H(C)` has diameter `≤ ℓ`" to "`H`-distance `≤ ℓ` inside a cluster".
  This makes the lemma stronger. Lemma 4.5 is proved in the stronger induced form (walks inside the cluster).
- **Lemma 4.3, randomness.** One node, arbitrary multigraph neighbourhood (`vol : ι → ℕ`), `L` trials.
  The samples are uniform in `Fin ((vol N)!)` and decoded into exactly uniform edges of the current
  `X_v`. This represents the adaptive process on one finite uniform space. The statement bounds the
  failure probability of the *whole* adaptive process by `L·|N|·(1−θ)^s`. The paper's union bound
  over nodes and levels, and the conditioning on `G_j`, are not formalized. `G_j` is fixed (conditioned
  on) in our statement.
- **Lemma 4.3, parameters.** We need `α ≥ 6` (for `⌊(β−1)α/β⌋ ≥ α/3`, unstated in the paper) and
  `τ ≤ α/3` (the paper's `α/3 ≥ c n^{2^j δ} log n`, using `h ≤ log n`). `lemma_4_3_parameters` derives
  both from the paper's parameters with natural logarithms, assuming `c ln n ≥ 2` and `1 ≤ h ≤ ln n`.
  The paper's "log" base is immaterial (absorbed in `c`).
- **Lemma 4.3, conclusion.** "Light or heavy" is `R = ∅` (every neighbour queried) or
  `|N \ R| ≥ τ` (`|F_v| ≥ τ`). The paper's "heavy" also requires `|N_j(v)| > |N̂_j(v)|`, which is just
  "not light".
- **Lemma 4.2.** Only the inequality `(1 − p)^m ≤ n^{−c}` for `p m ≥ c ln n` is formalized. The
  independence of the center marks from `N̂_j(v)` is immediate from the order of the steps and not
  modelled.
- **Size counterexample scope.** Only the first trial of level 0 is modelled. It always runs
  (`i = 1 ≤ 2h`, `F'_v = ∅`, `X_v = E(v) ≠ ∅`), and in a simple graph each sampled edge is the unique
  edge to its neighbour, so all of them enter `F_v ⊆ S`. Hence a lower bound on these edges is a lower
  bound on `|S|`. The number of samples is `⌈c² n^{δ+ε} ln³ n⌉` (`samples`). Any rounding works.
- **Not formalized.** Lemma 4.1 (Chernoff), the global union bound, Theorem 5.1, Lemma 6.1, Theorem 1.3.
