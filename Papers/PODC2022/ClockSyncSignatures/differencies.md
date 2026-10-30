# Differences between the formalization and the paper

Scope: Section 2 (model of the synchronous part), Definitions 1 and 6, Algorithm CB (Figure 4), Algorithm APA
(Figure 1), Lemma 7, Lemma 8, Theorem 9, Corollary 2. Sections 3 and 4 (pulse synchronization, lower bound) are
not formalized.

## Statement-level issues (decide the verdict)

None of the checked statements is false.

1. **Lemma 8, induction step (proof repair, 🛠️ under R1).** The step uses "`x ∈ I_w ⊇ Ĩ_w` by Lemma 7". Here
   `Ĩ_w` belongs to the execution with one more `⊥`. Lemma 7 gives the opposite inclusion `I_w ⊆ Ĩ_w`, and with the
   inclusion as written the conclusion `x ∈ Ĩ_w` does not follow. The construction also goes from a
   `k`-execution to a `(k+1)`-execution, which does not by itself reach every `(k+1)`-execution. Repair
   (`lemma_8`): start from any configuration with `k+1` honest `⊥`s. Pick an honest `w` and a dealer `d` with
   `o w d = ⊥`; `d` is faulty by validity. Replace this `⊥` by the common value `c` that other honest nodes
   received from `d`, or by `0` if there is none. The new configuration satisfies validity and crusader
   consistency (`IsCrusader`) and has `k` honest `⊥`s. The IH gives `x` in all its intervals, and Lemma 7 gives
   `x ∈ Ĩ^c_w ⊆ I_w`. Choosing `c` is necessary: with an arbitrary replacement the configuration may violate
   crusader consistency and the IH does not apply. Borderline between ✅ and 🛠️. We chose 🛠️ because the step
   as written proves nothing (wrong inclusion), and the missing coverage argument needs the specific choice of
   the replacement value.

## Modelling choices

2. **Execution model.** The paper's synchronous model with a rushing adversary is CSLib's lock-step model on the
   complete graph `⊤`, with ideal signatures as abstract tokens (`LockStep.Auth`, `Scenario.AuthValid`). The
   adversary is static (the Byzantine set is fixed per scenario). The paper's synchronous section never needs
   adaptivity, and its lower bound also uses a static adversary.
3. **Signatures carry the iteration number.** Token `(d, j, v)` = `d`'s signature on `(j, v)`. Figure 4 signs
   only `b_v`. For one instance (Theorem 9) this changes nothing. For Corollary 2's repetition it is necessary:
   without it, old signatures of honest dealers can be replayed and CB validity fails. This is the standard
   session-id convention, accepted under R4.
4. **Real-valued CB.** Definition 6 and Figure 4 have binary inputs `{0, 1}`. APA broadcasts reals. We run CB
   on reals; the signature argument is value-agnostic (R3: evident intent).
5. **Self-delivery.** CSLib's networks are simple graphs, so a node does not receive its own messages. A node
   uses its own value as "the token received from itself" and its own received token as its own echo.
   Figure 4's rule "two nodes `w₁ ≠ w₂` with valid but different values" then becomes "some echo carries a valid
   signature of `d` with a value different from the token I received from `d`". The two rules are equivalent
   once a node's own echo is counted.
6. **Forwarding.** In round 2 a node forwards whatever it received from the dealer, possibly an invalid token.
   Receivers check validity (`σ.1 = d`, `σ.2.1 = j`), as in Figure 4.
7. **Trimming bookkeeping.** APA discards `f − b` values on each side, with `b` the number of `⊥` outputs. In
   `ℕ`, `f − b` is truncated. This never matters, because `b ≤ #faulty ≤ f` (`IsCrusader.numBot_le`). The
   retained interval is `[orderStat (f−b), orderStat (#vals − 1 − (f−b))]` of the sorted non-`⊥` values.
   `mem_kept`, `lo_mem_kept`, `hi_mem_kept`, `mem_kept_bounds` show that it is the interval spanned by the
   values left after discarding, i.e. the paper's `I`.
8. **Resilience.** The paper fixes `f = ⌈n/2⌉ − 1`. We prove everything for any `f` with `2f < n`
   (`alg_secure`, `lemma_8`, `apa_step`) and specialize to `f = (n+1)/2 − 1 = ⌈n/2⌉ − 1` with `n ≥ 1` in
   `theorem_9` / `corollary_2`.
9. **Definition 1.** `AASpec ℓ ε` = "honest range `≤ ℓ` ⇒ termination ∧ validity ∧ `ε`-consistency", using CSLib's
   `Problem.ApproxAgreement` (validity = between two honest inputs, equivalent to `[min, max]`;
   `ε`-consistency = `|o_v − o_w| ≤ ε`, equivalent to the paper's `max (o_v − o_w) ≤ ε`). "`T`-round" means that
   all honest nodes decide by round `T` (`TerminatesBy`).
10. **Corollary 2's round count.** The paper's `2⌈log(ℓ/ε)⌉` is read as `2⌈log₂(ℓ/ε)⌉₊` (natural-number
    ceiling), with `ε > 0`. If `ℓ ≤ ε` this is `0` rounds: every node outputs its input. The paper's real ceiling
    can be negative or undefined there (R2: degenerate).

## Minor imprecisions in the paper's proofs (no effect on statements)

11. **Lemma 7's proof indices.** The lists are written `r^1, …, r^{n−k}` and `r̃^1, …, r̃^{n−k+1}` (should be
    `n−b`, `n−b+1`). The upper endpoints are written `r̃^{n−(f−(b−1))}` and `r^{n−(f−b)}`. The correct index is
    `n − f` for both: `(n−b+1) − (f−b+1)` and `(n−b) − (f−b)`. The paper's chain
    `r̃^{n−(f−(b−1))} ≤ r^{n−(f−(b−1))} ≤ r^{n−(f−b)}` becomes `r̃^{n−f} ≤ r^{n−f}`. The lemma also needs
    `b ≤ f` (stated in the proof as `0 < b ≤ f`) and `f < n`. Our `lemma_7` assumes both.
12. **Theorem 9's validity argument** ("`r_1 ≤ a_v` as there are at most `f` corrupted nodes and CB has
    validity") needs a count. Among the non-`⊥` values at most `f − b` come from faulty dealers, since all `b`
    `⊥`s come from faulty dealers. So the `(f − b + 1)`-th smallest value is at least one honest input
    (`interval_subset`, via `card_filter_vals_add_numBot_le`).
13. **Algorithm CB's correctness** is cited from [12]. We prove it in our model (`cb_isCrusader`): validity uses
    unforgeability (an invariant on all tokens in honest histories, `good_hist`); crusader consistency only
    uses the honest echo. Both hold for any number of faults.
