# Differences between the formalization and the paper

Paper: Lv, Moscibroda, *Fair and resilient Incentive Tree mechanisms*, Distributed Computing 2016 (journal
version of PODC 2013; numbering of the journal version: Theorems 1–4 = PODC 4.1–4.4, Lemmas 1–5 = PODC
4.5–4.9, Theorem 5 = PODC 4.10; the PODC version prints the same `R(u) ≥ C(u)` in the definition of PO). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Model

1. **SL mechanisms only.** A mechanism is `f : Tree → ℝ` (reward of the root of the given subtree). The paper's
   general mechanisms map a whole referral tree to rewards; SL means `R(u) = f(T_u)`. All results we check are
   about SL mechanisms (Theorem 3 assumes SL; the mechanisms of Theorems 1, 4, 5 are SL), so nothing is lost.
2. **Ordered children.** Trees are rose trees `Tree.node c (children : List Tree)`. Paper trees are unordered.
   Theorem 3 thereby covers the larger class of order-dependent mechanisms (stronger). All our mechanisms are
   order-invariant, and USA/UGSA compare real children only up to `List.Perm`.
3. **Imaginary root.** We do not single out the root `r` with `C(r) = 0`. The budget is required for every tree,
   summing over *all* its nodes (a stronger requirement than `R(T) ≤ Φ C(T)` over the participants only).
4. **Sybil attacks.** A Sybil attack is a list of Sybil trees (`Sybil.node c sybilChildren realChildren`). The
   real subtrees attached to Sybils are, up to permutation, exactly the real child subtrees of the single
   node. With SL the placement of the Sybil trees in the rest of the referral tree is irrelevant, so this
   covers "arbitrarily connected" Sybils. Real joiners can only be below Sybils: Sybils join before the
   participants they solicit. Join sequences / "for every `i`" are replaced by final configurations (under SL
   every intermediate tree is a final configuration of a shorter sequence). One Sybil identity (`k = 1`,
   joining with a larger contribution) is allowed, as in the paper's UGSA counterexample for TDRM. For the
   impossibility (Theorem 3) only the paper's specific two-Sybil chain is used.
5. **Nonnegativity.** All properties quantify over trees with nonnegative contributions (`C(u) ≥ 0`).
   Nonnegative rewards (part of "reward mechanism" in Section 2) is the separate property `NonnegReward`; it is
   proved for all mechanisms and not assumed in Theorem 3.
6. **CSI.** We require the new participant and `u` to have positive contribution (see item 12). A new
   participant may join anywhere in `T_u`, at any position among its siblings (`Tree.JoinLeaf`).
7. **PO.** `PO` = positive profit `R(u) > C(u)` (prose of Section 3.1). `POWeak` = the printed formal
   definition `R(u) ≥ C(u)`. URO is as printed (for every `R > 0`, `C(u) > 0`, `k ≥ 1`).

## Statements

8. **Theorem 3** (`theorem_3`) is proved for `PO` (positive profit), without budget or nonnegative rewards
   and with only the `k = 1` case of PO. With the printed `POWeak` it is false for `Φ = 1`
   (`theorem_3_false_for_weak_PO`, mechanism `R(u) = C(u)`). *Rule:* R3 (the prose says "positive profit"
   and the proof uses `P(v*) > 0`; fix `≥ → >`) → ⚠️. *Open:* weak PO with `Φ < 1`. The paper's argument
   only shows that, under SL + UGSA, every node has profit `≤ 0`. We did not settle whether a mechanism with
   zero-profit opportunities, UGSA and budget `Φ < 1` exists.
   *Strength of `UGSA`:* our `UGSA` also quantifies over single-identity attacks (`k = 1`) and the empty
   forest (only possible for `c = 0`, `F = []`, demanding `f (leaf 0) ≥ 0`), so as a hypothesis it is at
   least as strong as the paper's. This does not weaken `theorem_3`: its proof uses only the paper's own
   two-identity chain attack.
9. **Theorem 1** (`theorem_1`): added `0 < b`. The paper allows `b = φ = 0`, where CCI, CSI and URO fail
   (R2, degenerate) → ⚠️ item "zero parameters". We prove the "except USA and UGSA" part as a negative
   statement: a chain split of a participant of contribution 2 into two Sybils of contribution 1 gains
   `a b` (the paper's explanation after Theorem 1).
10. **Theorem 4** (`theorem_4`): added `0 < a`, `0 < b`, `0 < λ`, `0 ≤ φ` (the paper states only `λ < Φ − φ`,
    `b < 1 − a`, `μ > 0`; with `a`, `b` or `λ ≤ 0` CSI/URO fail). R4/R2 → ⚠️ item "zero parameters". For
    `C(u) = 0` the paper's chain has `N_u = 0` nodes; we use one node of contribution 0
    (`nOf μ c = ⌈c/μ⌉ - 1`, chain length `nOf + 1`). Edge direction of Algorithm 4 follows Figure 3 (tail
    of the parent's chain → head of the child's chain); the printed `(m^u_{N_u}, m^v_1)` with Section 2's
    convention "edge `(u, v)` = `u` child of `v`" is reversed (typo). UGSA counterexample: the paper's example
    with `C(u) = μ/2`, `k > 1/(abλ)` children of contribution `μ`; its `P(u)` has `(ak + 1)` instead of
    `(ak + ½)` (typo, conclusion unaffected).
11. **Theorem 5** (`theorem_5`):
    - The paper claims "all properties, except URO"; PO fails too (`R < Φx ≤ x`). R3 (Section 4.4 says
      "except PO/URO") → ⚠️. We prove `¬ URO` and `¬ PO`.
    - Hypotheses (i)–(iv) are stated as in the paper for `x > 0`, `y ≥ 0` (derivatives via `deriv`; at `y = 0`
      a two-sided derivative in `y`). (iv) is assumed for `x', x'' > 0`.
    - Added: `R(·, y)` continuous on `[0, ∞)` (right-continuity at 0). The paper leaves `R(0, y)` unconstrained;
      a large `R(0, y)` would break the budget and a negative one φ-RPC. With (iii) this gives `R(0, y) = 0`
      (R4, degenerate zero contributions) → ⚠️ item "zero contributions".
    - Added `0 ≤ φ` and `Φ ≤ 1` (model assumptions of Section 3).
    - CSI is proved for `C(u) > 0` only: for `C(u) = 0` both examples of Algorithm 5 have `R(0, y) = 0` for all
      `y`, so CSI fails there (R2).
    - Non-vacuity: Algorithm 5 (i) with `θ > 0`, `θ + φ < Φ ≤ 1`, `φ ≥ 0` satisfies the hypotheses
      (`cdrmExample_successfullyCD`). Algorithm 5 (ii) is not formalized.
12. **Zero contributions in CSI** (all mechanisms): if the newcomer has contribution 0, no mechanism of the
    paper rewards the solicitation. TDRM and CDRM also give nothing to a solicitor with `C(u) = 0`. R2 → ⚠️.
13. **Appendix Lemmas 1–5** (structure of an optimal Sybil partition) are not formalized as stated. Their
    uniqueness formulations fail in degenerate cases. Lemma 5 fails if `u` has no solicitees (`R^e ≡ 0`, so
    every partition is optimal). Lemmas 1–3 fail if a Sybil has contribution 0 (attaching or detaching it
    changes nothing). R2/R3 (the proof idea says "at least one optimal partition is an ε-chain", which is
    what is used) → ⚠️.

## Proofs

14. **Theorem 4, USA.** Replaced. The paper maximizes `R^i` and `R^e` separately over "partitions". It never
    shows that a maximizer exists, uses contradiction-with-maximality arguments whose exchange steps are only
    weakly improving, and its Lemma 2 case (b) leaves a 0-node below `μ`. Lemma 2's auxiliary `S1 > S2` covers
    only transfers away from the balanced split. Our proof: closed form `tdrm_node`, invariant `sybil_bound`
    (induction on Sybil trees, carrying the ancestor weight `α ≤ G(ℓ)`), and the chain inequalities
    `Qc_add`, `Qc_superadd`, `Hc_add_le`, `Gc_add_le`, `Gc_subadd` (case analysis `ε + δ ≤ μ` / `> μ`,
    certificates by `linear_combination`) → 🛠️.
15. **Theorem 4, budget.** The paper's chain of inequalities is correct; we prove it as the invariant
    `(1 − a) Σ_v inner(T_v) + aμ W(T) ≤ μ C(T)` (`tdrmInner_budget`, `chain_budget`).
16. **Theorem 4, URO.** The paper's argument ("`R'(m^u_{N_u}) ≥ ε a²bλ`") is garbled. We use one child of
    contribution 1 with `M` leaf children of contribution 1; the reward grows linearly in `M`.
17. **Theorem 5, USA.** Replaced by an induction on Sybil trees (`a Sybil tree of mass m with real contribution
    E earns ≤ R(m, E)`). The paper's minimal-`k` merging argument merges non-adjacent ancestor/descendant pairs,
    which changes the rewards of the Sybils in between. It ignores Sybil ancestors in case (b) and only gets
    "at least the same reward" → 🛠️. UGSA then follows as in the paper from `x − R(x, y)` increasing
    (mean value theorem via `strictMonoOn_of_deriv_pos`).
18. **Theorem 1** ("easy to derive", no proof): budget via `(1 − a) Σ_v W(T_v) + a W(T) ≤ C(T)`.
19. **Theorem 3**: the paper's proof is formalized verbatim (with strict PO).

## Not formalized

- Theorem 2 (L-Pachira; its USA proof is imported from [7]) and the L-Luxor remark.
- Section 4.3 (split-proof mechanism of Emek et al.), Algorithm 3 (preliminary TDRM; its USA claim is only
  motivation), Algorithm 5 (ii).
- The optimality remark "maximal mutually satisfiable subsets" is the conjunction of Theorems 3, 4, 5 (all
  proved), but we did not state it separately.
