# Differences between the formalization and the paper

Paper: Garg & Garg, PODC 2026 brief announcement (BA) and full version arXiv 2602.10486 v1 (FV).
Numbering: BA Thm 2.1 = FV Thm 1, BA Thm 3.1 = FV Thm 3, BA Lemma 3.2 = FV Lemma 1, BA Thm 4.1 = FV Thm 4.

## Statement-level issues (with the rule from `verdicts.md` that decides each)

1. **FV §6.1: "Algorithm 5 is inflationary and monotone" — false.** Counterexample with `n = 2`
   (`Apps.alg5_not_monotone`); all positions are within `1..n`, so it does not depend on how
   `mpref[j][G[j]]` is read for `G[j] ∈ {0, n+1}`. A concrete claim "object X is in class C" (R1), the fix
   (test "`j` has proposed to `w`" instead of "`j` currently proposes to `w`") changes the algorithm, so
   not R3. Not a headline (application) → **❌** (R5). The conclusion (Alg. 5 computes the man-optimal
   matching under the three execution models) is only unestablished; a bounded model check
   (`scripts/alg5_modelcheck.py`: `python3 alg5_modelcheck.py 3 all`, exhaustive `n ≤ 3`, 300 random `n = 4`) found no
   wrong fixed point.
2. **FV §6.2: Algorithm 7 "follows from Corollary 4.2" — hypotheses false.** No common fixed point exists
   for any relaxation rule (`Apps.alg7_no_common_fixed_point`); the level component is unbounded (infinite
   lattice); non-monotone (`Apps.alg7_not_monotone`, with the paper's order `dist` by `≥`, `level` by `≤`).
   The convergence of the distance components is unestablished (not refuted). Borderline: the paper never says
   in so many words "Algorithm 7 is monotone"; what is false is the implicit claim that Algorithm 7 is an instance
   of Corollary 4.2, while its stated conclusion is only unestablished. At most ❌ (R1/R5); item 1 alone decides
   the verdict.
3. **FV/BA §2: "the set of fixed points for each `fᵢ` is a sublattice of `L`" — false**
   (`fixedPoints_not_supClosed`, on the distributive lattice `{0,1,2}²`). The use (existence of `min`) is
   correct since fixed points of a monotone inflationary function are meet-closed (`isCommonFixed_inf`).
   Borderline between a statement (R1, explicit claim in main text) and an auxiliary remark; with "sublattice"
   read loosely as "a lattice in the induced order" the first sentence would hold (meet-closed, contains `⊤`),
   but the paper cites Birkhoff and the standard meaning is join- and meet-closed. At most ❌, which does not
   change the verdict. This is the only statement-level issue that is in the brief announcement itself.
4. **BA Thm 3.1: "finite distributive lattice of vectors `N^n_m`".** For a proper sublattice the model is
   not closed (`sublattice_round_escapes`: commit `111` outside `L = {000,010,110,021,121}`). We read `L`
   as the whole box `{0,…,m}ⁿ` (FV: "for simplicity … each component … between 0 and m"), and in fact
   formalize any finite product of finite posets. ⚠️ (R4/R3: the intended reading is recoverable from the
   paper's text — the "for simplicity" paragraph, the notation `N^n_m`, and the full version's Table 2, which lists
   "product lattice" as a necessary assumption; distributivity is never used).
5. **FV §6.3: Algorithm 10 does not map `{0,…,mΔ}ⁿ` into itself** (`Apps.alg10_out_of_range`). Fix: cap
   at `mΔ`. ⚠️ (R3).
6. **FV Cor 4.1: "`fᵢ : L′ → L′` monotone and deflationary"** should be deflationary on `L` (inflationary on
   `L′`). Typo, ⚠️ (R3). Formalized as `corollary_4_1` (deflationary, start `⊤`, greatest fixed point).

## Proof repairs (statements true)

7. **Thm 3.1, fixed-point part.** The paper does not show that the process `i` scheduled after stabilization
   reads `G*`. Repair: a round with `G_{t+1} = G_t` has no writes (Lemma 3.2(3)), hence every read returns
   the committed value (`RoundExec.read_eq_of_commit_eq`).
8. **Thm 3.1, leastness.** "All writes in round `t` are `≤ Y` and so `X ≤ Y`" is circular as stated; made
   precise by strong induction on the causal order of reads (`RoundExec.commit_le`).
9. **Thm 4.1, fixed-point part.** The paper picks `t ≤ U + τ`; one needs `t ≥ U + T` so the view equals
   `G*`. With this repair the theorem holds under **plain fairness** (`theorem_4_1_fair`); strong fairness
   (Definition 6) is never needed. The paper's statement with strong fairness is `theorem_4_1`.
10. **Lemma 3.2(1).** Proved with strict inequality (BA version), which implies the FV's `≥`.

## Modelling choices

11. **Lattice.** Thm 2.1 is stated for any finite poset with `⊥` (no lattice structure needed; the paper:
    finite lattice `L ⊆ ℕⁿ`). Thms 3.1/4.1 for `(k : κ) → β k` with `κ` finite and each `β k` a finite poset
    with `⊥` (the paper: `{0,…,m}ⁿ`). General-start versions (`converges_from`,
    `parallel_converges_from`, `distributed_converges_from`) only need `WellFoundedGT`.
12. **Index sets.** Functions are indexed by an arbitrary type `ι` (the paper: `[m]` in §2, `[n]` in §3); in
    §4 processes and coordinates coincide (`ι`), as in the paper.
13. **Fairness.** `FairSeq σ` / `FairSets S`: every index infinitely often (the paper: "selects each fᵢ
    infinitely often"). `StronglyFair τ S`: every window `[t, t+τ)` contains a round with `i`.
14. **Termination.** "Terminates at `G*`" = the state sequence is eventually constant equal to `G*`
    (`TerminatesAt`).
15. **Non-interleaving round (`RoundExec`).** Reads return the committed value or the value of any write in
    the round by a process whose reads ended strictly earlier (rank `ℕ` = discretized end-of-read instant).
    The paper's real-time description ("a read overlapping writes returns the old value or any of the
    writes"; compute after reading, then write) implies this causality; our model is more permissive in
    allowing a read to return any earlier write, not just overlapping/latest ones, and any write as the
    committed value. Without causality the theorem fails (`acausal_round_breaks_leastness`), so this is a
    clarification, not an added assumption. Ranks in `ℕ` lose nothing for the paper's `n` processes (finitely
    many read-end instants can be order-embedded into `ℕ`). Each process reads a full vector (coordinates it does not
    really read are irrelevant to the computed function).
16. **Update-only-on-change** is a write policy `uooc X H k := H k ≠ X k` (Definition 3); the naive rule
    is `naive` (write every coordinate), used for the §3 example `naive_round_stuck`.
17. **Bounded staleness (Definition 5).** "At most `T` rounds old" = the coordinate equals `G s j` for some
    `t − T ≤ s ≤ t`; own coordinate equals `G t i`. Views are arbitrary vectors (in the product, so always in
    `L`). Leastness only needs stale views (`StaleView`, any `s ≤ t`).
18. **Applications.** Transitive closure: state `V × V → Bool`, `R₀` = edges ∪ diagonal; fixed point =
    reflexive–transitive closure (`TC.isLeast_rtc`). Round bound of §3.1 formalized as "after `t` rounds every
    pair joined by a walk of `≤ 2^t` edges is set; closure once `|V| − 1 ≤ 2^t`" (`TC.tc_parallel_rounds`),
    which is the paper's `O(log n)`. Alg. 5: positions 1-based, `mpref j k` = `(k+1)`-th choice, positions
    `0`/`n+1` propose to nobody. Alg. 7: abstract or concrete relaxation (`bfRelax` = running minimum over
    predecessors, as the loop computes). Alg. 10: integer arithmetic, `maxEnvy` starts at `0`.

## Not formalized

19. Algorithm 2 (CAS counting), Algorithm 4, correctness of Algorithms 5, 6, 8, 9, 10; Algorithm 6/8's
    "`∃k` … `G[i] ← G[k] + w[k,i]`" is ambiguous (with the first witness instead of the minimum the
    function is not monotone; with the minimum it is), and Algorithm 6's initialization `G[1] = w[1,1]`
    (rather than `0`) for the source — not formalized, noted only. Table 2's informal necessity claims for
    "i-locality" and "product lattice" (no precise statement). The termination-detection remark.
