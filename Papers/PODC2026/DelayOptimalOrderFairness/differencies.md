# Differences between the formalization and the paper

Paper: Cai, Goharshady, *Brief Announcement: Delay-Optimal Transaction Order Fairness*, PODC 2026 (4-page BA;
proof ideas only, full version HAL hal-05625798 not consulted).

## Statement-level issues (decide the verdict)

1. **Theorem 5.2 for a fixed number of nodes is false** (`theorem_5_2_fixed_n_false`). Instance: `n = 4`, `|H| = 3`
   (`h = 3/4`), `k = 1`, `θ = Δ > 0`, `φ = 3/5`. Hypotheses: `k ≥ 1`, `1 − h/k = 1/4 ≤ 3/4`, `θ ≤ Δ/k`,
   `φ = 0.6 < 1 − h/(k+1) = 0.625`. Every `Δ`-synchronous profile has an acyclic AOF graph (counting form of
   Thm 5.1 with `k = 2`). Formalized instead: `theorem_5_2` (∃ `N`, ∀ `n ≥ N` with `hn ∈ ℕ`, a cycle exists) and
   `theorem_5_2_finite` (sufficient condition `φn + hc/(k+1) + 2 ≤ n` for `hc` honest out of `n`).
   *Rule:* **R3 → ⚠️.** The intended version is recoverable from the paper itself: the proof idea and the
   preceding paragraph let the number of Byzantine groups grow so that support becomes "arbitrarily close to
   `1 − h/(k+1)`", which only makes sense with `n → ∞`. The fix is a local hypothesis on `n`. *Borderline with ✅:*
   one could read "admit a valid synchronous profile" as also choosing `n`. We did not, because §2 fixes `n` as a
   model parameter and the theorem says "in the same model". Also, for the standard BFT size `n = 4`, `f = 1` the
   claimed boundary `1 − h/(k+1)` is wrong (at `k = 1`, `θ = Δ` the same counting argument rules out cycles for every `φ > 1/2`, not only above `0.625`; formalized for `φ = 3/5`). Not ❌: the paper's proof
   reasons with the intended (large-`n`) version.
2. **Theorem 3.1 for a fixed number of nodes is false** (`theorem_3_1_fixed_n_false`: for every `n ≥ 1` some
   `φ ∈ (1/2, 1)` admits no `φ`-majority cycle in any profile). Formalized instead: `theorem_3_1` (∃ `N`, ∀ `n ≥ N`,
   a profile exists). *Rule:* the existential "there is a … profile" naturally includes choosing `n`, and the
   proof idea chooses `k > 1/(1 − φ)` groups. At worst R3 → ⚠️. Since 1. already gives ⚠️, this does not
   change the verdict.

## Other differences and modelling choices

3. **Unused hypothesis.** `1 − h/k ≤ h` (Thms 5.1, 5.2) is omitted; our theorems are stronger without it.
4. **`n ≥ 1` in Thm 5.1** (`[Nonempty Node]`): with `n = 0` every pair is an AOF edge (`|I| = 0 ≥ φ·0`). Degenerate
   (R2).
5. **`Δ ≥ 0` in Thm 5.2.** With `Δ < 0` and honest nodes present no synchronous profile exists. Implicit
   (R4, standard). `θ` may be any real `≤ Δ/k` (also `≤ 0`).
6. **Thm 3.1 is stated for any `φ < 1`** (the paper: `φ ∈ (1/2, 1)`) and needs `Δ > 0`. With `Δ = 0` all honest
   nodes have identical timestamps and no vote cycle exists. The paper's "small `δ < Δ_sync/k`" assumes `Δ > 0`
   (R4). Our profile makes **all** nodes honest and synchronous, which is stronger than needed. The vote relation
   is "at least `φn` nodes received `tx` strictly before `tx'`". The paper does not define "pairwise
   `φ`-majority" in the BA. We return the chain `tx_B → ⋯ → tx_A` and the unanimous edge `tx_A → tx_B` (with
   gap `≥ D` at every node). If "`φ`-majority" is read strictly (`> φn`), apply `theorem_3_1` with
   `φ' = (1 + φ)/2 ∈ (φ, 1)`: support `≥ φ'n > φn`, so the strict reading follows immediately.
7. **Honest fraction.** `h` enters only through `|H| = h·n` (real). In Thm 5.2 we also assume `h ≤ 1` (an honest
   fraction) and require `hn` to be an integer, implicit in "honest set `H` of size `hn`".
8. **Profiles.** Every honest node receives every transaction of the profile (`ts` is total). The paper's
   synchrony ("if one honest node receives tx, every honest node receives it within `Δ`") is formalized as
   "honest timestamps of each transaction differ by at most `Δ`". Timestamps are real times; there is no clock
   skew (cf. §7, which says skew must be absorbed into `θ`).
9. **Cycle.** "The AOF graph contains a directed cycle" = `∃ x, TransGen (Prec ts θ φ) x x`. In Thm 5.2 the
   transactions are `ℕ`, and the cycle uses `m = (k+1)(n+1)` of them.
10. **Thm 5.2 construction differs in detail** from the proof idea. Honest node `i` belongs to group
    `i mod (k+1)`, so the groups are as equal as possible rather than exactly equal. Each Byzantine node supports
    every edge but one (one "group" per node, cycle length `≥ n`). Each edge therefore has at least
    `n − ⌈hc/(k+1)⌉ − 1` supporters. The exact optimal threshold for fixed `n` is not determined.
11. **Thm 5.1 proof.** It follows the proof idea: some honest node supports all `k` consecutive edges, so the
    earliest honest receive time strictly increases (`s_{j+k} > s_j`). Instead of summing around the cycle we
    unroll the cycle into a periodic walk (`not_hasCycle_of_kstep`); this is equivalent. The paper's
    intermediate fractions ("more than `(k−1)/k` … `(k−2)/k` …") are replaced by a union bound over `k` edges.
12. **"Hence AOF can be achieved by deterministic topological sorting"** is formalized as the existence of a
    strict total order respecting all AOF edges (`theorem_5_1_order`, via Szpilrajn), for arbitrary (also
    infinite) transaction sets. We do not formalize a deterministic algorithm or the hash tie-breaking.
13. **Remark §7 ("boundary gap").** Not a theorem of the paper. We show the threshold is exact on every band
    `Δ/(k+1) < θ ≤ Δ/k` (`threshold_tight`, for large `n`), so the gap the paper describes is an artifact of
    stating Thms 5.1 and 5.2 with the same `k`.
14. **Not formalized:** §2's "useful range `1 − h < φ ≤ h`" remarks (immediate), §4, §6 (protocol sketch,
    `Order(R)`, Sync HotStuff, the `n − 2f` effective honest fraction under partial synchrony).
