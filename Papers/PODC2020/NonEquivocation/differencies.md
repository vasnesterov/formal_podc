# Differences between the formalization and the paper

Madsen–Debois, *On the Subject of Non-Equivocation*, PODC 2020 (proceedings version; the online
appendix [29] was not available).

## False statements

1. **Theorem 6.1 (false only in degenerate cases).** "For `n ≤ 2t` no algorithm solves interactive
   consistency under weak non-equivocation." False for `n ∈ {1, 2, 3}`, e.g. `n = 2, t = 1` and
   `n = 3, t = 2` (`theorem_6_1_false_n2`, `theorem_6_1_false_n3`). With `≥ n − 1` faulty processes
   only the own entry of the single correct process is constrained (`solvesIC_of_own`), so
   Algorithm 2 with parameter `n − 2` works (`solvesIC_small`). The proof needs four non-empty
   groups (`n ≥ 4`). "WLOG `n = 2t`" and "`|O| = … = t/2`" are not justified (odd `t`, `n < 2t`); we
   choose groups of sizes `1, ⌊n/2⌋ − 1, ⌈n/2⌉ − 1, 1`. Proved: `theorem_6_1` for `4 ≤ n ≤ 2t`, any
   `k`. Exact threshold: `icSolvable_wne_iff` (solvable iff `n > 2t ∨ n ≤ 3`). The paper contradicts
   itself here: its Theorem 4.2 (solvable for any `n > 1` if `t ≤ 1`) covers `n = 2, t = 1 ≤ n/2`.
2. **Lemmas 4.7 and 4.8 under the reading `v ∈ V ∪ {⊥}` (false statements; inconsistent use of
   `V`).**
   * Line 2 of Algorithm 2 says "⊥ ∉ V", but Lemma 4.7 concludes "`v ≠ ⊥`" for `v ∈ V`.
   * Under the reading where `v` may be `⊥`, a correct process can have a consistent majority for `⊥`
     (`lemma_4_7_false`: `n = 3`, `t = 1`, 2 rounds). The proof of Lemma 4.7 forgets that the only
     correct member of `Q` may be the decider `p`, whose route `p|p|q` collapses to `p|q`.
   * Lemma 4.8 is false on the same instance: process `0` has a `2`-majority for `⊥`, process `1` one
     for `v`. Its proof's appeal to Lemma 4.7 is the failing step.
   * Repaired: `lemma_4_7_repaired` (requires a correct member other than `p`, `q`). With `Maj` over
     genuine values, Lemma 4.7 is vacuous and Lemma 4.8 holds (`lemma_4_8`).
3. **Line 8 of Algorithm 2 (reading).** Algorithm 2 is not wrong as printed: line 9 returns `v` into
   an IC vector of values, and line 2 says "⊥ ∉ V", so the type-consistent reading is `v ∈ V`. We use
   it, and Theorem 5.1 holds (`theorem_5_1`). A reading that allows `v = ⊥` would break agreement in
   the run above: `0` returns `⊥`, `1` returns `v` (`literal_line8_fails`).
4. **Section 7.2, definition of the authenticated Byzantine model + Fig. 4 (imprecise definition;
   intent clear: the `⟨⊥⟩` convention was forgotten).**
   As printed (`σ(w'|p|w) = σ(p|w) ∨ σ(w'|p|w) = ⊥`), the model contradicts Definition 2.1 whenever a
   correct process observes an omission within `k ≥ 2` rounds (it reports `⟨⊥⟩`). So
   "Crash ⊆ Omission ⊆ AB" fails for the literal reading (`silentσ_not_authByzLiteral`). We use the
   intended `authByz`: absent, `p`'s report, or `⟨⊥⟩`. (Our first attempted repair, comparing with
   `rep σ(p|w)` but without `⟨⊥⟩`, fails for `k ≥ 3` (`silentσ_not_authByzRep`); that concerns our
   repair, not the paper.)
   For `k = 1` the literal reading is harmless (`equivσ_authByzLiteral_one`).
5. **Section 7.2, example (3) (informal; reinterpretation, not a refutation).** "From (I)–(III) we
   deduce `t ≥ 2`, `n ≥ 5`" refers to an algorithmic criterion. Read as a pure fault-space
   separation, a smaller witness exists: a single faulty process lying consistently about
   its own value (`n = 3`, `t = 1`) is in WNE ∩ AB but not in Omission
   (`sne_inter_authByz_not_le_omission`). The paper's example itself is checked (`paperEx3`).

## Proof gaps (statements true)

6. **Theorem 5.1.** Only a proof sketch; the case "one correct process has a consistent majority, the
   other has none" is deferred to the appendix (Lemma C.1). Full proof: `psl_correct` (induction on
   `t` over an active set `S`, with the recursive instance `sub σ q`). Validity in recursive
   instances must allow private value `⊥` (reported as `⟨⊥⟩`). Lemma 4.4 is stated accordingly
   (`rep (σ [q])`).
7. **Round lower bound (Section 6).** The paper sketches it by inclusion of the crash model and cites
   Aguilera–Toueg for consensus; the formal proof is in the appendix. We prove directly that `k ≤ t`
   rounds are insufficient already against send-omission faults, by a chain argument
   (`not_solvesIC_omission_of_le`). It needs `n ≥ t + 2`, which holds when `n > 2t ≥ 2`.

## Under-specified definitions / algorithms (fixed readings)

8. **Definitions 3.1, 4.1:** `r, r'` range over processes different from `p` (footnote 1 only says so
   for the second form). With `r = p` and the convention `σ(p|p|w) = σ(p|w)`, the definitions would
   force faulty processes to relay truthfully. All constraints apply only to routes without
   consecutive duplicates and at most `k` rounds.
9. **Algorithm 1, line 5:** `r ∉ {p, q}` (otherwise `σ_p(p|p|q) = ⊥ ≠ ⟨⊥⟩` returns `⊥`). If the
   chosen report is `⊥` we return `⟨⊥⟩` (unreachable under the hypotheses).
10. **Algorithm 2.**
    * Line 20 "∃ v" uses a fixed choice function (`Classical.choose`); agreement needs a
      deterministic choice.
    * The recursion goes down to `t = 0`, where "no majority" returns `⟨⊥⟩` (unreachable).
    * `Q ⊆` the current process set.
    * The majority's routes `p|w|q` with consecutive duplicates are skipped. This is equivalent to
      the paper's collapsing convention.
11. **Definition 4.3:** `q ∈ Q` (mentioned in the text but not in the formula) is not required. It
    plays no role (`w = ε` already gives `σ(p|q) = v`). Lemma 4.6 needs `p ≠ q`.
12. **Interactive consistency:** "the private value of a correct `q`" is `σ [q]`, assumed `≠ ⊥` at top
    level. Termination is built in (deterministic decision after `k` rounds).

## Statements strengthened / hypotheses dropped

13. Section 3 (strong NE, 1 round) holds for all `n`, `t` (the paper says `n > t`): `sne_solvesIC`.
    One round is optimal for `n ≥ 2` (`sne_not_solvesIC_zero`).
14. Theorem 4.2 holds for all `n` (the paper says `n > 1`).
15. Lemma 4.8 needs no correctness of `p`, `q`, only weak non-equivocation of `r`'s round-1 message.
16. Theorem 5.1 only needs Definitions 2.1 and 4.1 for `t + 1` rounds and only reads `t + 1` rounds
    (`psl_congr`).

## Modelling choices

17. Everything lives in the paper's PSL message-map framework: algorithms decide from the
    full-information relay `σ`. Impossibility results quantify over all deterministic decision
    functions of `p`'s view of `k` rounds. Arbitrary protocols with other message formats (e.g. the
    lock-step model of CSLib) are not covered, as in the paper.
18. Crash model (`crash`): a faulty process has a crash round `c`. In round `c`, each receiver gets
    all or none of its round-`c` reports (one full-information message). Omission (`omission`):
    per-route omissions. These are our choices; the paper does not define them formally.
19. Not formalized:
    * the informal converses (Byzantine broadcast oracle ⇒ SNE; crusader agreement oracle ⇒ WNE;
      Dolev's mapping of Byzantine `σ` with `t + 2` rounds to WNE);
    * the algorithmic reading of the §7.2 examples;
    * Table 1 entries from the literature.
20. Typo: Section 3, truncated sentence "a faulty process `q` may receive `v` from".
