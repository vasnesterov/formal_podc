# Swiper: a new paradigm for efficient weighted distributed protocols

Andrei Tonkikh, Luciano Freitas. PODC 2024. DOI [10.1145/3662158.3662799](https://doi.org/10.1145/3662158.3662799),
arXiv [2307.15561](https://arxiv.org/abs/2307.15561) (v2, which contains the appendix proofs; the local PDF is v2).

## Scope and model

The paper's mathematical content is Section 2 (three "weight reduction" problems and upper bounds),
Section 3.1 (the Swiper family of ticket assignments and why a local minimum respects the bounds) and
Appendix A (proofs). Sections 4–6 are protocol transformations relying on cryptographic black boxes
(secret sharing, threshold signatures, erasure codes, VBA, SSLE); only the purely combinatorial core of
Theorem 4.2 is formalized. Section 7 and Appendices B–C are experiments / a MIP formulation (not
formalized).

No distributed-computing model is involved: everything is static combinatorics. Parties are a
`Fintype ι` (`n = Fintype.card ι`), weights `w : ι → ℝ` with `w i ≥ 0` and `W = ∑ w ≠ 0`, ticket
assignments `t : ι → ℕ`.

## Main results ↔ Lean

| Paper | Lean | Status |
|---|---|---|
| Problems 1–3 (WR, WQ, WS constraints) | `IsWR`, `IsWQ`, `IsWS` (`Defs.lean`) | definitions |
| "viable" (App. A.1) | `Viable`; `viable_iff` (= `IsWR` when `W>0`, `αw>0`) | |
| Thm 2.1 (WR upper bound) | `wr_upper_bound` (`WeightRestriction.lean`) | proved |
| Thm 2.1 via the paper's construction (App. A.1) | `wr_upper_bound_swiper` (`Construction.lean`) | proved |
| key computation of App. A.1 / "bootstrapping" claim of §3.1 | `isWR_of_rounds` | proved (stronger: real bound, no ceiling) |
| existence of a locally minimal viable `s*` (gap in paper) | `exists_viable`, `exists_locallyMinimal` | proved |
| "there must be some `j` with `s* w_j + αw ∈ ℤ`" | `LocallyMinimal.border_nonempty` | proved |
| footnote 6 (`t' = t_{s*-ε}`) | `ts_sub_eventually_eq`, `LocallyMinimal.not_viable_removeTickets_border` | proved |
| ticket removal ends with `t̂` viable, `t̂̂` not | `LocallyMinimal.exists_removal` | proved |
| bound for any stopping point of the removal | `removal_bound` | proved |
| §3.1: the family `t(s,k)` hits every total `T` | `Cslib.Apportionment.exists_rounds_sum_eq` | proved |
| Thm 2.2 (WQ = WR with complemented parameters) | `isWQ_iff_isWR` | proved (no hypotheses needed) |
| Cor 2.3 (WQ upper bound) | `wq_upper_bound` | proved |
| Thm 2.4 (WS upper bound `(α+β)(1−α)/(β−α)·n`) | `ws_upper_bound_false` | **false** as stated (Lean counterexample, uses overlapping `S₁ ⊆ S₂` as the paper's definition allows); Swiper's WS construction violates it on a 3-party instance with disjoint sets (refutes the proof and the Robustness claim under either reading): `swiper_ws_counterexample`, `swiper_ws_family_exceeds_bound` |
| Thm 2.4, corrected | `ws_upper_bound`: `T ≤ ⌈(1−(β−α)²)/(2(β−α))·n⌉` (`WeightSeparation.lean`) | proved |
| WS symmetry (not in paper) | `isWS_iff_compl` | proved |
| Def 4.1, Thm 4.2 (combinatorial core) | `IsBlunt`, `isBlunt_of_isWR` (`Applications.lean`) | proved |

All theorems are sorry-free; `lean_verify` on `wr_upper_bound`, `wr_upper_bound_swiper`,
`wq_upper_bound`, `ws_upper_bound`, `ws_upper_bound_false`, `swiper_ws_family_exceeds_bound`,
`isBlunt_of_isWR` reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Findings (details in `differencies.md`)

1. **Theorem 2.4 (WS upper bound) is false.** `ws_upper_bound_false`: `α = 1/20`, `β = 1/10`,
   8 parties of weight 14 and 13 of weight 1 (`n = 21`): every WS solution has `T ≥ 63`, the claimed
   bound is `59.85`. This uses overlapping `S₁ ⊆ S₂`, which the paper's definition allows (under a
   disjoint-sets reading it would not be a counterexample). Numerically, for this family `OPT/n → α/β²` (here 5 vs the claimed 2.85).
   The proof in A.2 fails in its second case ("analogous by substitution", but the floor offset `γ`
   is not substituted; valid only for `γ = 1/2`). Swiper's WS mode also violates the bound on the
   3-party instance `w = (1,1,15)`: the paper's `s` gives the invalid `t = (0,0,7)`, and every WS-valid
   member of the `γ`-offset family has `T ≥ 14 > 8.55`. We prove the replacement bound
   `⌈(1−d²)/(2d)·n⌉`, `d = β−α` (`ws_upper_bound`); it is better than the paper's when `α+β` is near
   1 and is a correct (though weaker) bound otherwise.
2. **Gaps in App. A.1 filled**: existence of viable `s` (the paper says "we already proved" — it did
   not), existence of a locally minimal `s*` (discreteness/right-continuity argument), and `J ≠ ∅`.
3. Theorem 2.1/2.2/Cor 2.3 are correct as stated. Edge-case note (not an error): the paper's
   requirement `αw ∈ (0,1)` is needed (at `αw = 0` with "viable", the bound `⌈0⌉ = 0` cannot be
   met); `n = 1` and zero weights are fine.

## Infrastructure

- `Cslib/Foundations/Combinatorics/Apportionment/Divisor.lean` (migrated from `Podc/` to CSLib, namespace `Cslib.Apportionment`): `Rounds` (rounding with offset, i.e.
  stationary divisor methods with ties), `exists_rounds_sum_eq` (every house size attainable),
  `rounds_floor`, one-sided continuity of `s ↦ ⌊a s + c⌋₊`.

## Status

Complete; no `sorry`. Files: `Defs.lean`, `WeightRestriction.lean`, `Construction.lean`,
`WeightSeparation.lean`, `Applications.lean`.

Rough token spend: ~0.35M (paper agent) + ~0.25M (numerics subagent) ≈ 0.6M.
