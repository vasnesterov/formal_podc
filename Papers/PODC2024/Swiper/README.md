# Swiper — PODC 2024

Andrei Tonkikh, Luciano Freitas. *Swiper: a new paradigm for efficient weighted distributed protocols.* PODC 2024.
DOI [10.1145/3662158.3662799](https://doi.org/10.1145/3662158.3662799). Formalized version: arXiv
[2307.15561](https://arxiv.org/abs/2307.15561) v2 (contains the appendix proofs).

**Verdict: ❌ False claim.** The weight restriction and weight qualification bounds (Theorem 2.1, Theorem 2.2,
Corollary 2.3) are correct and proved, filling gaps in Appendix A.1. **Theorem 2.4 (weight separation) is false**:
its proof in Appendix A.2 is wrong, and Swiper's own weight-separation construction violates the claimed bound. We
prove a different, correct bound instead.

## Mistakes in the paper

1. **Theorem 2.4 is false (false statement).** Claimed: every weight-separation instance has a solution with
   `T ≤ (α+β)(1−α)/(β−α)·n` tickets. Counterexample: `α = 1/20`, `β = 1/10`, 8 parties of weight 14 and 13 of
   weight 1 (`n = 21`, `W = 125`). Each weight-14 party alone is heavy, all 13 unit parties together are heavy, and
   light sets contain at most 6 unit parties. If at most 6 unit parties hold tickets, those (light) and all unit
   parties (heavy) have equally many tickets, a violation. Otherwise any 6 ticketed unit parties hold `≥ 6`
   tickets, so each weight-14 party needs `≥ 7` and the unit parties together `≥ 7`: `T ≥ 63 > 59.85`. (The
   optimum is exactly 63; for this family `OPT/n → α/β²`, here 5 versus the claimed 2.85.) This instance compares
   a set of unit parties with a superset of it, which the paper's Problem 3 allows. Under a "disjoint `S₁, S₂`"
   reading it would not be a counterexample, but item 2 refutes the proof and Swiper's guarantee under either
   reading (`ws_upper_bound_false`).
2. **The proof in Appendix A.2 is wrong, and Swiper's weight-separation construction does not meet the bound.**
   The proof rounds `t_i = ⌊w_i s + γ⌋` with `γ = (α+β)/2`. Case 1 (`t(S₁) ≥ γT`) is correct (up to typos: its complement bound writes `βWs` for `(1−α)Ws`, and
   "`t(S₂) > (1−γ)T`" means `t([n]∖S₂)`); case 2 is claimed
   "analogous by substituting `1−γ` for `γ` and `1−β` for `α`". That would also require changing the rounding
   offset from `γ` to `1−γ`, which is not done, so the argument works only for `γ = 1/2`. Redone honestly, case 2
   gives `max(γ², (1−γ)²)·n` instead of `γ(1−γ)·n`. Concretely, on three parties `w = (1, 1, 15)` with the same
   `α, β`, the paper's `s` yields `t = (0, 0, 7)`, and the two unit parties (weight 2 > `βW` = 1.7) are heavy yet
   ticketless, so they tie with `S₁ = ∅` (disjoint sets). Every valid member of the `γ`-offset family has `T ≥ 14`,
   while the bound is 8.55, which contradicts §3's "Robustness" claim for weight separation
   (`swiper_ws_counterexample`, `swiper_ws_family_exceeds_bound`). The authors' public solver
   ([DCL-TelecomParis/swiper](https://github.com/DCL-TelecomParis/swiper), commit f1d7a3d) hard-codes this bound
   and silently returns invalid tickets when it binds: weights `(2, 14)` with `α = 1/20`, `β = 1/10` give tickets
   `(0, 5)`, although party 1 alone is heavy (checked by running it).
   **What we prove instead:** `T ≤ ⌈(1−d²)/(2d)·n⌉` with `d = β − α`, using rounding offset `(1−d)/2`
   (`ws_upper_bound`). It is symmetric under `(α, β) ↦ (1−β, 1−α)`, as the problem is (the paper's bound is not).
   It beats the paper's bound when `α+β` is near 1 and is weaker when `α+β` is small.
3. **Gaps in Appendix A.1 (Theorem 2.1 true).** "Since we already proved that viable `s` exist": no such proof is
   in the paper. "It is easy to see that such `s*` exists": this needs a right-continuity/discreteness argument for
   the infimum. The border set `J` being non-empty needs `0 < αw < 1`. All three are proved
   (`exists_viable`, `exists_locallyMinimal`, `LocallyMinimal.border_nonempty`).
4. **Minor.** In Definition 4.1 the second conjunct has `F` unbound (we read it as `∀ F, ∃ A, A ∩ F = ∅`). The
   §4.1 random-beacon example writes `(1−αn)T ≥ ⌈αn T⌉`, which is false in general (`αn = 1/2`, `T = 3`) but
   harmless there because ticket counts are integers.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** No distributed model is involved: Sections 2, 3.1 and Appendix A are static combinatorics. Parties form
a finite type `ι`, with weights `w : ι → ℝ`, `w ≥ 0`, `W ≠ 0`, and tickets `t : ι → ℕ`. Problems 1–3 are the
predicates `IsWR`, `IsWQ`, `IsWS`, which quantify over all subsets as in the paper. The removal process of A.1
("remove tickets while the assignment stays viable") is modelled by an arbitrary stopping point, so every run is
covered.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (weight restriction) | `wr_upper_bound` | `WeightRestriction.lean` |
| Theorem 2.1 via the paper's locally-minimal construction | `wr_upper_bound_swiper` | `Construction.lean` |
| Theorem 2.2 (WQ = WR with complemented parameters) | `isWQ_iff_isWR` | `WeightRestriction.lean` |
| Corollary 2.3 (weight qualification) | `wq_upper_bound` | `WeightRestriction.lean` |
| Theorem 2.4: counterexample | `ws_upper_bound_false` | `WeightSeparation.lean` |
| Theorem 2.4: Swiper's construction fails | `swiper_ws_counterexample`, `swiper_ws_family_exceeds_bound` | `WeightSeparation.lean` |
| Theorem 2.4, corrected bound | `ws_upper_bound` | `WeightSeparation.lean` |
| Theorem 4.2 (combinatorial core) | `isBlunt_of_isWR` | `Applications.lean` |

**Not formalized.** The protocol transformations of Sections 4–6 (cryptographic black boxes) beyond the
combinatorial core of Theorem 4.2, the knapsack-based validity check of §3.1, Section 7 and Appendices B–C.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
rounding family ("every total `T` is attained") comes from CSLib's
`Cslib/Foundations/Combinatorics/Apportionment/Divisor.lean`.
