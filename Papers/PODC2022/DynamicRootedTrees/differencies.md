# Differences between the formalization and the paper

Sources: brief announcement (BA) arXiv:2211.11352v3 = PODC'22 DOI 10.1145/3519270.3538460 (5 pages,
model + statement only) and the full version (FV) arXiv:2211.10151v2 (El-Hayek, Henzinger, Schmid,
*Asymptotically Tight Bounds on the Time Complexity of Broadcast and its Variants in Dynamic Networks*,
ITCS'23), Sections 1–3 and Appendix A.1–A.2. All proofs we formalize are from FV.

## Statements

1. **BA's bound is one round sharper than what FV proves.** BA Theorem 3.1 claims
   `t*(𝒯ₙ) ≤ ⌈(1+√2)n − 1⌉`, whereas FV Theorem 3.6 proves only `t*(𝒯ₙ) ≤ ⌈(1+√2)n⌉` (FV's abstract states
   `⌈(1+√2)n−1⌉` again). The BA claim is **true**: FV's pigeonhole in Lemma 3.5 has slack. With
   `m = ⌈√2 n⌉` rounds allowed to have out-edges and only `R = n + m − 1 = ⌈(1+√2)n − 1⌉` rounds, the edge
   count is `≥ m(m+1)/2 + (n−1)m`, and it exceeds `(n−1)(n+m−1)` (= (out-degree `n−1`) × (number of
   sources)) iff `m(m+1) > 2(n−1)²`, which holds. We prove both: `theorem_3_6` (FV) and
   `advBroadcastTime_trees_le` / `theorem_3_1` (BA).
2. **Sharper bound (new, same proof).** `advBroadcastTime_trees_le_of_sq_lt`: `t*(𝒯ₙ) ≤ m + n − 1` for
   every `m` with `2(n−1)² < m(m+1)`, i.e. about `(1+√2)(n−1)`. (Within this proof scheme a larger `R` with a smaller
   threshold does not help: for fixed `R` the edge lower bound `∑_{t≤R} min(m,t)` minus the pigeonhole
   threshold is maximized at `m ≈ R − n + 1`. Not formalized; informal remark.)
3. **Generalization.** The proof never uses that rounds are trees, only (a) a self-loop at every node and
   (b) a root reaching everybody. `broadcasts_of_rooted` states the bound for any such dynamic network
   (FV's Section 5 makes the analogous remark for `k`-rooted networks).
4. **Junk values.** `t*(G₁,G₂,…)` (`broadcastTime`) is `sInf` (0 if broadcast never happens) and `t*(𝒢)`
   (`advBroadcastTime`) is `⨆` (0 if unbounded). The paper's `min`/`max` exist only because of the
   theorem itself. To avoid vacuity we also state the per-sequence form `broadcasts_trees`
   (every sequence of trees has broadcast after `⌈(1+√2)n−1⌉` rounds), and the lower bound via an explicit
   sequence that has not broadcast (`lbSeq_not_broadcasts`).
5. **Round 0 / empty product.** The paper never defines `G₁ ∘ ⋯ ∘ G₀`. We take the empty product to be
   the identity and `t ∈ ℕ` to include `0`; this only matters for `n = 1` (`t* = 0` instead of `1`; both
   are below the bounds). Sequences are `G : ℕ → …` with `G 0` unused, and the adversary condition is
   `∀ i, G i ∈ 𝒯ₙ` (for `i = 0` too, which is harmless).
6. **Ceilings.** The upper bound uses `Nat.ceil` (`⌈·⌉₊`), which agrees with the integer ceiling for
   `n ≥ 1` (for `n = 0` there are no trees). The lower bound is stated with `Int.ceil` as in the paper;
   `⌈(3n−1)/2⌉ = ⌊3n/2⌋` (`ceil_three_mul_sub_one_div_two`).

## Definitions

7. **Rooted trees with self-loops (`𝒯ₙ`)**: `RootedTree n` = root + parent function such that iterating the
   parent from any vertex reaches the root; the communication graph `adj` has edges parent → child plus
   all self-loops. (The parent value of the root is ignored, so several `RootedTree`s give the same graph;
   `treesWithLoops n` is the set of graphs.)
8. **Generalized neighbourhoods** `I_t^{t'}(x)`, `O_t^{t'}(x)` (FV Def. 2.1/2.2) are `Finset`s defined exactly
   as in the paper (`{x}` for `t = t'+1`, `∅` for `t > t'+1`).
9. **Rounds graph (FV Def. 3.4)** is parametrized by the threshold `m` (paper: `⌈√2 n⌉`) and the number of
   rounds `R` (paper: `⌈(1+√2)n⌉`). Vertex type `α ⊕ ℕ`; rounds outside `[1, R]` are extra isolated vertices.
   `lemma_3_5` instantiates the paper's parameters.

## Proofs

10. **Lemma 3.3** is stated in FV for `t₁ ≤ t₂` but used in Lemma 3.5 with `t₁ = 1, t₂ = t − 1 = 0` (round
    `t = 1`). We prove it for `t₁ ≤ t₂ + 1` (the extra case is trivial: `I_1^0(x) = {x}`). The proof's
    counted set uses `I_{t+1}^{t₂}`; we prove that stronger version
    (`card_filter_root_notMem_succ_add_one_le`) and derive the stated one by monotonicity.
11. **Lemma 3.2 (ii)**: the hypothesis `t ≤ t'` is unnecessary (if `t > t'+1` the out-neighbourhood is
    empty and the premise fails); stated with round `t'+1` instead of `t'` to avoid ℕ subtraction.
12. **Lemma 3.5, typos/looseness**: the in-degree formula writes `|I_1^{t−1}(x)|` for `|I_1^{t−1}(r_t)|`; the
    final comparison `|E| > ⌈(1+√2)n⌉·n` is not the pigeonhole threshold (that is `(n−1)·#sources`,
    `#sources = n + ⌈√2n⌉ − 1`), but the inequality used is still sufficient. We prove the generic
    `exists_outdeg_ge` under the exact threshold `(n−1)(n+m−1) < ∑_{t=1}^{R} min(m,t)`.
13. **Theorem 3.6**: the paper proves `|O_1^{t_n}(z)| ≥ n` via a chain of strict inequalities; we prove the
    invariant `min(n, |S ∩ [1,K]|) ≤ |O_1^K(z)|` by induction on `K` (`min_card_le_card_outNbhd`), which also
    covers the "unless `|O| = n`" case of Lemma 3.2 (ii) explicitly.
14. **Lower bound (Theorem 3.7, Zeiner–Schwarz–Schmid)**: FV only gives a figure (Figure 5). We read it as:
    rounds `1..⌊(n−1)/2⌋` the path `1→⋯→n`; rounds `⌊(n−1)/2⌋+1 .. n−2` the tree rooted at `n` with branches
    `n→1→⋯→⌊n/2⌋` and `n→n−1→⋯→⌊n/2⌋+1`; rounds `≥ n−1` the path `⌊n/2⌋→⋯→n→1→⋯→⌊n/2⌋−1`. With this
    reading the figure is correct (proved for all `n ≥ 2`; numerically, broadcast happens exactly at round
    `⌈(3n−1)/2⌉−2`). No proof is given in FV; ours uses forward invariants on out-neighbourhoods.

## Sanity checks (not in the paper)

15. Exhaustive search over all adversarial sequences (product relations as states): `t*(𝒯ₙ) = 0, 1, 2, 4,
    5, 7` for `n = 1..6` — equal to the lower bound `⌈(3n−1)/2⌉−2` for `2 ≤ n ≤ 6` — while the upper bound
    gives `2, 4, 7, 9, 12, 14`. Kernel-verified for `n ≤ 4` (`Small.lean`, `decide +kernel`, ~15 s for
    `n = 4`); `n = 5` by Python, `n = 6` by a C search modulo relabeling (not verified in Lean).
