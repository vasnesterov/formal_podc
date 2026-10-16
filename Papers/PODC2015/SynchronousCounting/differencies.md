# Differences between the formalization and the paper

Paper: Lenzen, Rybicki, Suomela, *Towards Optimal Synchronous Counting*, PODC 2015, arXiv 1503.06702v1.
Classification: **false statement**, **false only in a degenerate case**, **proof gap (statement true)**,
**under-specified definition**, **typo**, **modelling choice**.

## Theorem 1 (boosting resilience)

1. **False statement in the boundary case `n = 1`; downstream unaffected.** §4.1 and Corollary 1 use
   `n = 1` but avoid the problem by assuming `F < N/3`. §3.4 says that `F < N/3`
   "follows from the preconditions of Theorem 1". It does not when `n = 1`: with `f = 0` and `k = 3`
   (or any odd `k ≥ 3`, or even `k ≥ 6`) the hypothesis `F < (f+1)⌈k/2⌉` allows `F ≥ N/3`. For example
   `n = 1, f = 0, k = 3, F = 1, C = 2, c = 576` claims a 1-resilient counter on 3 nodes, which does not
   exist. The base counter does exist (the trivial one-node counter). Lean: `theorem1_as_stated_false`,
   using `Cslib.Byzantine.SyncCounting.not_isCounter_of_card_eq_three` (no 1-resilient counter on 3 nodes; proved
   here by a line-covering argument). The paper's own construction fails there in a concrete way: the
   Byzantine node echoes every receiver's own `a` register back to it, so each correct node sees its own
   value `N − F = 2` times and the other correct value `F = 1` time. Then all three instruction sets keep
   both counters running, and they stay apart forever (`construction_fails`, `pkStep_of_dominant`).
   For `n ≥ 2` the claim is right if `f < n/3`. It is proved as `three_mul_lt_of_paper`, used in
   `theorem1_paper`. Corollary 1 is not affected, because it explicitly replaces the hypothesis by
   `F < N/3`.
2. **Proof gap (statement true for `n ≥ 3`): the paper uses `f < n/3` without assuming it.** The proof
   of Lemma 3 says that `f < n/3` "as otherwise counting cannot be solved". That is an external
   impossibility result. We proved the needed impossibility for `3 ≤ n ≤ 3f`
   (`Cslib.Byzantine.SyncCounting.not_isCounter_of_three_le_card`). So Theorem 1 holds *exactly as stated* when
   `n ≥ 3` (`theorem1_of_three_le`). For `n = 2, f ≥ 1` the statement holds iff there is no 1-resilient
   counter on 2 nodes. We did not prove this; our line argument needs three nonempty groups. The repaired
   general theorem `boost`/`theorem1` assumes `2f < n` (all the proof needs: a strict majority of correct
   nodes in every non-faulty block) and `3F < kn`.
3. **Modelling choice: nonempty state set.** With the paper's definitions an algorithm with an empty
   state set has no executions and is vacuously a counter of any resilience. Then the existence claims of
   Theorem 1 and Section 4 would be trivially true. `Achievable` therefore requires a nonempty, finite
   state set (the paper's `S(A) = ⌈log |X|⌉` presupposes this anyway).
4. **Imprecise: `S(B) = S(A) + ⌈log(C+1)⌉ + 1`.** The state of `B` is literally `X × ([C] ∪ {∞}) × {0,1}`
   (`BState`). In general, `⌈log₂ |X_B|⌉ ≤ S(A) + ⌈log₂(C+1)⌉ + 1` holds only as an inequality; it is an
   equality for bit-field encodings. We prove the inequality (`boost`).
5. **Under-specified definition: `min ∅` in `I₃ℓ₊₁`.** "Set `a[v] ← min{j : z_j > F}`" does not say
   what happens when no value is received more than `F` times. We use `∞`. It is also unclear whether `j`
   ranges over `[C] ∪ {∞}`; with `∞` ordered last, both readings agree.
6. **Under-specified definition: output for `a = ∞`.** The output `h` of `B` must lie in `[C]`. We output
   `0` when `a = ∞`; this never matters after stabilisation.
7. **Literal reading kept:** in `I₃ℓ₊₂`, `min{C, a[ℓ]}` with `a[ℓ] = ∞` gives `C`, which is incremented to
   `C + 1 mod C`. We implement this literally (`fromKing`).
8. **Modelling choice: majority.** `majority` returns "an arbitrary value" without a strict majority. Our
   `maj` is a fixed deterministic function (the first value with a strict majority, else `0`). Since the
   lemmas only use it when a strict majority exists, this is a special case. The pointer `B` is a block index
   (`Fin k`); an out-of-range majority value falls back to the node's own block (never happens:
   pointer values are `< m ≤ k`).
9. **Modelling choice: kings.** "Node `ℓ ∈ [F+2]`" is the node `finProdFinEquiv.symm ℓ` of
   `[k] × [n] ≃ [kn]`.
10. **Typo, Lemma 2 / Lemma 3 / §3.5:** `c_k` should be `c_{k−1} = τ(2m)^k` (blocks are `0, …, k−1`). The
    final bound `T(A) + 3(F+2)(2m)^k` is right, and it is exactly what we prove.
11. **Typo, proof of Lemma 1:** "at round `w = u + (β − 1)c_{i−1}`" should be `u + β c_{i−1}`. Our
    arithmetic proof (`lemma1`) does not use `u`.
12. **Typo, proof of Lemma 4:** "Checking `I₃ℓ₊₂`" should be "Checking `I₃ℓ₊₁`". Also, "some any
    non-faulty node".
13. **Typo, Lemma 5:** "`x + 1 mod c`" should be "`mod C`".
14. **Typo, §2 (executions):** "`d` is reachable from `e` if … `π_F(x) = d` and `g(i, x) = d_i`" should
    have `π_F(x) = e`. Our `IsExec` uses the intended meaning.
15. **Typo, §3.1:** "one of which must have fewer than `f` faulty nodes" should be "at most `f`".
16. **Imprecise:** §3.3 defines `majority` for vectors of length `kn` with threshold `kn/2`, but uses it for
    vectors of length `n` and `k`. We use the threshold "more than half of the vector".
17. **Proof structure:** Lemma 3 (the leader block and its round counter agree at all correct nodes for `τ`
    rounds) is not a separate Lean theorem. It is `Rval_eq` (voting) plus the window from `lemma2`, inside
    the proof of `theorem1`. Lemmas 1 and 2 are formalized as their arithmetic cores (`lemma1`, `lemma2`,
    with `ptr_eq` linking them to the counter values).

## Section 4 (recursive construction)

18. **Typo, proof of Corollary 1:** the time is written `(3f + 2)(2m)^k`; Theorem 1 gives `3(f + 2)(2m)^k`.
    Harmless (`corollary1`, `corollary1_bounds`: time `≤ (3f+2)^{3f+3}`).
19. **Imprecise, Corollary 1:** it is stated "for `f < n/3`" (any `n`), but the proof covers only
    `n = 3f + 1`. We formalize `n = 3f + 1`.
20. **Proof gap, Theorem 2's time bound:** the proof writes the per-step cost as `3(f_{i+1}+2)h^k` and uses
    `h^k` in the space term, but Theorem 1 gives `(2m)^k = k^k = 2^k h^k`. So the proof does not establish
    the claimed `O(2^{2^{1/ε}} f)`; nothing shows that this bound is false either. We prove the weaker
    bound: with `h = 2^a` and `ε = 1/a` the factor is `2^{(a+1)2^{a+1}+12}` (`theorem2`), i.e. `2^{2^{O(1/ε)}}`.
    For a constant `ε` (Corollary 2) this is `O(f)`, so the corollary holds (`corollary2`).
21. **Computation error, §4.3 (statement true):** the paper computes `n/f = 4 ∏ 2^{r_p} = 2^{2(2^P−1)}` and
    `k_1 − 2 ≤ ε log f`. This uses `R_p = 2·2^{P−p}` instead of the stated `R_p = 2k_p = 8·2^{P−p}`, and it
    drops the factor 4. Correct value: `n/f = 2^{8·2^P−6} = 2^{4k_1−6}` (`thm3N`). Since this is still
    `Θ(k_1)`, `ε = Θ(1/log log f)` survives (`theorem3_asymptotic`).
22. **Imprecise:** Corollary 1 and Theorems 2 and 3 only give counters for special network sizes
    (`3f+1`, `4(2h)^L`, `2^{8·2^P−6} f`). The paper does not say how to get other `n`; padding with extra
    nodes is not discussed. We formalize the special sizes, and the asymptotic statements quantify over an
    infinite family (`∀ m, ∃ n f …, m ≤ f ∧ …`).
23. **Modelling choice, asymptotics:** the `O(·)` claims are stated with explicit constants and
    `Nat.log 2` / `Nat.clog 2` (`theorem3_asymptotic`: `T ≤ K f`,
    `S ≤ K ⌊log² f / log log f⌋ + ⌈log₂(C+1)⌉ + K`, `log n ≤ log f + K ⌊log f / log log f⌋`, `K = 2^33`).

## Not formalized

24. Section 5 (pulling model, randomised sampling, Theorem 4, Lemmas 8–9, Corollaries 3–5). Its proofs are
    sketches ("by picking the right constants and using concentration bounds").
