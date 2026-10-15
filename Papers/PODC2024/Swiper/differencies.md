# Differences between the formalization and the paper

Paper: Tonkikh, Freitas, *Swiper: a new paradigm for efficient weighted distributed protocols*,
PODC 2024 / arXiv 2307.15561v2.

## Errors in the paper

### E1. Theorem 2.4 (Weight Separation) is false; its proof in Appendix A.2 is wrong; Swiper violates the bound

**The theorem is false** (`ws_upper_bound_false`, `WeightSeparation.lean`): `α = 1/20`, `β = 1/10`,
parties `1..8` of weight 14 and `9..21` of weight 1 (`W = 125`, `αW = 6.25`, `βW = 12.5`). Light
sets contain at most 6 weight-1 parties; all 13 weight-1 parties form a heavy set; each weight-14
party alone is heavy. If fewer than 6 weight-1 parties hold tickets, they (light) and all weight-1
parties (heavy) have equally many tickets — violation. Otherwise 6 ticketed weight-1 parties have
`≥ 6` tickets, so each weight-14 party needs `≥ 7` and the weight-1 parties together `≥ 7`:
`T ≥ 63 > 59.85 = (α+β)(1−α)/(β−α)·21`. **Caveat:** this refutation relies on `S₁` and `S₂` being
allowed to overlap (it compares a subset of the weight-1 parties with all of them). The paper's
literal definition of Problem 3 allows overlap, so the theorem is false as stated; under a
disjoint-sets reading this instance would not be a counterexample. The 3-party instance below
(`swiper_ws_family_exceeds_bound`, with disjoint `S₁ = ∅`, `S₂`) refutes the paper's proof and
Swiper's "Robustness" claim under either reading. (The optimum is exactly 63, found numerically.) The
numerics subagent found more instances, e.g. `(α,β) = (1/10,1/5)`, `n = 22`: OPT 60 > 59.4, and
`(14/15, 29/30)` (`α+β > 1`), `n = 27`: OPT 104 > 102.6; for the family "h heavy parties of weight
`> βW` plus g unit parties" `OPT = h(a+1) + a + 1 + g − b` (`a = ⌈αW⌉−1`, `b = ⌊βW⌋+1`), with
`OPT/n → α/β²` asymptotically, which exceeds `(α+β)(1−α)/(β−α)` e.g. for small `α`, `β = 2α`
(`1/(4α)` vs `≈ 3`). No violation was found for `(α,β) = (1/4,1/3)` (best ratio OPT/bound 0.74).

Appendix A.2 uses `t_i = ⌊w_i s + γ⌋`, `γ = (α+β)/2`. Case 1 (`t(S₁) ≥ γT`) is correct and gives
`s < γ(1−γ)n/((γ−α)W)`. Case 2 (`t(S₂) < γT`) is claimed to follow "analogously, by substitution of
`1−γ` in place of `γ` and `1−β` in place of `α`". This substitution would also require replacing the
rounding offset `γ` by `1−γ`, which is not done; it is valid only when `γ = 1/2`. Redoing case 2
gives `s(β−γ)W < γ² n + (1−2γ)|S₂| ≤ max(γ², (1−γ)²) n`, not `γ(1−γ) n`.

The statement about Swiper is false, not only the proof (`WeightSeparation.lean`):
- `swiper_ws_counterexample`: `w = (1, 1, 15)`, `α = 1/20`, `β = 1/10`, `n = 3`. The paper's
  `s = 2γ(1−γ)n/((β−α)W) = 333/680` gives `t = (0, 0, 7)`, and `S₁ = ∅`, `S₂ = {1, 2}`
  (parties 1 and 2 in the paper's 1-based numbering, weight `2 > 1.7`) violates WS.
- `swiper_ws_family_exceeds_bound`: every WS-valid `t` in the family with offset `γ`
  (`w_i s + γ − 1 ≤ t_i ≤ w_i s + γ`, i.e. all `t(s, k)` of §3.1) has `T ≥ 14`, while the claimed bound is
  `(α+β)(1−α)/(β−α)·n = 8.55`. Hence Swiper's WS output (a local minimum of that family) exceeds the
  bound, contradicting the "Robustness" claim of §3 for WS.
- `counterexample_optimum`: `t = (1, 0, 1)` is a WS solution (`T = 2`), so on this small instance only
  Swiper's construction fails; the theorem itself is refuted by the 21-party instance above.

What we prove instead: `ws_upper_bound`, `T ≤ ⌈(1 − d²)/(2d) · n⌉` with `d = β − α`, using the
same family with offset `(1−d)/2` and a direct analysis of the pair `(S₁ \ S₂, S₂ \ S₁)`
(`isWS_of_rounds`: every member with `T ≥ (1−d²)/(2d)·n` is valid). This bound is symmetric under
`(α, β) ↦ (1−β, 1−α)` (as it must be, `isWS_iff_compl`), beats the paper's bound when `α+β` is close to 1
(e.g. `α=0.3, β=0.7`: `1.05n` vs `1.75n`), and is worse when `α+β` is small (e.g. `α=0.05, β=0.1`:
`9.98n` vs `2.85n`). Note also that the paper's bound is not symmetric under the complementation
symmetry, so for `α + β > 1` it is weaker than its own mirror image `(2−α−β)β/(β−α)·n`.

Minor: Theorem 2.4 is stated without ceiling (`T ≤ (α+β)(1−α)/(β−α)·n`), consistent with its
fixed-`s` proof; our corrected statement has a ceiling.

### E2. Gaps in Appendix A.1 (filled, result correct)

- "Since we already proved that viable values of `s` exist" — no such proof appears in the paper. We
  prove it (`exists_viable`) from the key computation: `T(t_s) ≥ sW − (1−αw)n → ∞`, and every member
  of the family with `T ≥ αw(1−αw)/(αn−αw)·n` is viable (`isWR_of_rounds`).
- "it is easy to see that such `s*` exists" — needs a discreteness argument. We take
  `s* = inf {s > 0 | t_s viable}`, show `s* ≥ (1−αw)/W > 0` (for smaller `s`, `t_s = 0`) and that the
  infimum is attained because `s ↦ t_s` is right-continuous and integer-valued
  (`exists_locallyMinimal`). The global minimum is in particular locally minimal.
- "there must be some `j` such that `s* w_j + αw` is an integer": proved (`border_nonempty`), via
  footnote 6 (`ts_sub_eventually_eq`), which needs `0 < αw < 1` (if `αw` were an integer, zero-weight
  parties would be on the border and `t'` would need negative tickets).
- The removal process ("taking tickets from parties in `J` as long as the assignment stays viable")
  is modelled by an arbitrary `K ⊆ J` with `t* − 1_K` viable and `t* − 1_{K∪{j}}` not viable;
  `removal_bound` holds for every such stopping point, `exists_removal` shows one exists.

## Differences in statements / modelling

- Weights and thresholds are real numbers; tickets are natural numbers. The paper's
  `ti ∈ Z≥0` is `ℕ`.
- `W ≠ 0` and `w_i ≥ 0` are explicit hypotheses (as in the problem statements).
- Theorem 2.1 is stated as the existence of a *viable* assignment (`T ≠ 0` and the WR constraint),
  as in Appendix A.1. For `W > 0` and `αw > 0`, `T ≠ 0` is implied by the WR constraint
  (`IsWR.sum_ne_zero`, take `S = ∅`).
- Our main proof of Thm 2.1 (`wr_upper_bound`) does not use the locally minimal `s*`: it takes the
  member of the family with exactly `T = ⌈bound⌉` tickets (exists by
  `Cslib.Apportionment.exists_rounds_sum_eq`) — this is the "bootstrapping" remark of §3.1. The paper's
  route is formalized separately (`wr_upper_bound_swiper`).
- The key lemma `isWR_of_rounds` does not need `w_i ≥ 0` nor `αn < 1`, and uses the real bound
  `T ≥ αw(1−αw)n/(αn−αw)` (the paper's §3.1 phrases it with the ceiling).
- Theorem 2.2 ("the problems are identical"): formalized as equality of the constraint sets for every
  `t` (`isWQ_iff_isWR`); no hypotheses on `βw, βn` or the weights are needed.
- Theorem 4.2: only its combinatorial core is formalized (`isBlunt_of_isWR`). Definition 4.1's second
  conjunct `∃A ∈ A : A ∩ F = ∅` has `F` unbound; we read it as `∀ F ∈ F, ∃ A ∈ A, A ∩ F = ∅`. Thm 4.2's
  proof correctly uses "(1−αn)T ≥ αn T". The §4.1 random-beacon example writes "(1−αn)T ≥ ⌈αn T⌉", which
  is false in general (`αn = 1/2, T = 3`). The slip is harmless there: honest parties hold an integer
  number of tickets `> (1−αn)T ≥ αn T`, hence `≥ ⌈αn T⌉`. Qualified sets are those with
  `t(P) ≥ ⌈αn T⌉` (`ticketAccess`).

## Edge cases

- `αw = 0` (an edge-case note, not a paper error: the paper requires `αw ∈ (0,1)`): the WR constraint is vacuous, `t = 0` solves Problem 1 with
  `T = 0 = ⌈0⌉`, but no *viable* assignment satisfies `T ≤ ⌈0⌉`. So the open interval is needed for the
  appendix formulation.
- `n = 1`, zero weights: covered by the theorems (only `W ≠ 0` is needed).
- Ceilings in Thm 2.1/Cor 2.3 are exactly right for the method: the family attains every total, and
  the key lemma gives validity at `T = ⌈bound⌉`.

## Not formalized

- Sections 4–6 protocol transformations (cryptographic black boxes: secret sharing, threshold
  signatures/encryption, erasure codes, VBA, SSLE) and the overhead table (Table 1).
- §3.1 algorithmic claims: Knapsack-based validity check in `O(Tn)` (dynamic programming by profits),
  quasi-linear upper/lower Knapsack bounds, `--linear` mode, binary search. (Validity of an assignment
  is trivially decidable by enumerating subsets; we did not formalize the DP.)
- Section 7 and Appendices B (MIP) and C (experiments).

## Numerical experiments

Done by a helper subagent with exact arithmetic (scripts were not kept in
the repo; exhaustive search for `n ≤ 8`–`22` on structured families, branch and bound over weight
classes, cross-checked).
- Thm 2.4: counterexamples as listed in E1. With offset `(1−d)/2` Swiper-style chains reach the optimum
  on the counterexamples (60, 63); with the paper's offset `γ` the first valid member had `T = 92`
  resp. `111`.
- Thm 2.1 is not tight in the worst case on small instances: max OPT/n found for `n ≤ 10` was 1.0 for
  `(1/4,1/3)` (bound 2.25n), 0.9 for `(1/3,1/2)` (1.33n), 1.7 for `(1/3,3/8)` (5.33n); OPT = ⌈bound⌉ only
  when `⌈bound⌉ = 1`. The paper's open question about lower bounds remains open.
- The key lemma `isWR_of_rounds` is tight: there are invalid members of the `αw`-offset family with
  `T = ⌈bound⌉ − 1`, e.g. `(αw,αn) = (1/3,1/2)`, `w = (5,2)`, `t = (1,1)` (`T = 2`, bound `2.67`), and
  `(1/4,1/3)`, `w = (19,3,3)`, `t = (4,1,1)` (`T = 6`, bound `6.75`). So the analysis of Swiper's
  construction cannot be improved, although the optimum can be far smaller.
- `n = 1`: WR optimum is 1 while the real bound can be below 1, so the ceiling in Thm 2.1 is needed.
