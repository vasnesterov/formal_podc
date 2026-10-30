import Papers.PODC2023.OptimalEBAOmission.BasicCtx
import Papers.PODC2023.OptimalEBAOmission.Counterexamples

/-!
# Main results of Alpturer–Halpern–van der Meyden (PODC 2023), §6

* **Proposition 6.1** — `Context.prop_6_1` (`Prop61.lean`): implementations of `P0` are EBA decision
  protocols, nonfaulty agents decide after at most `t + 1` rounds, Validity holds for all agents.
* **Theorem 6.3** — `Context.thm_6_3` (`Thm63.lean`), under the extra hypotheses "competitors are
  one-shot" and `NFConsistent`; `thm_6_3_min`, `thm_6_3_basic` below: all implementations of `P0` in
  `γ_min`, `γ_basic` are optimal (`t ≤ n - 2`).
* **Proposition 6.4** — `prop_6_4_min`, `prop_6_4_basic` (repaired 0-chains); with the paper's
  0-chains it is false: `Counterexamples.prop_6_4_lit_false`.
* **Theorem 6.5** — `thm_6_5`; **Theorem 6.6** — `Basic.thm_6_6`.
* **Corollary 6.7** — `cor_6_7_min`, `cor_6_7_basic` (`t ≤ n - 2`); without `t ≤ n - 2` it is false:
  `Counterexamples.cor_6_7_min_false`.
-/

namespace Podc.OptimalEBAOmission

open Context

variable {n t : ℕ}

/-- **Theorem 6.5.** If `t ≤ n - 2`, then `P^min` (decide `1` at time `t + 1`) implements `P0` in
`γ_min,n,t`. -/
theorem thm_6_5 (ht : t + 2 ≤ n) : Implements (pmin (n := n) (t := t) (t + 1)) :=
  Min.pmin_implements (by omega) le_rfl (by omega) (Or.inl le_rfl)

/-- **Proposition 6.4** (`γ_min`, repaired 0-chains). If `n - t ≥ 2`, `P0` is safe w.r.t.
`γ_min,n,t`. -/
theorem prop_6_4_min (ht : t + 2 ≤ n) : Safe (minCtx n t) := fun _ hP =>
  (thm_6_5 ht).safeWrt_congr hP (Min.pmin_safe (by omega) le_rfl (by omega) (Or.inl le_rfl))

/-- **Proposition 6.4** (`γ_basic`, repaired 0-chains). If `n - t ≥ 2`, `P0` is safe w.r.t.
`γ_basic,n,t`. -/
theorem prop_6_4_basic (ht : t + 2 ≤ n) : Safe (basicCtx n t) := fun _ hP =>
  (Basic.thm_6_6 ht).safeWrt_congr hP (Basic.safe ht)

/-- **Theorem 6.3 for `γ_min`**: if `t ≤ n - 2`, every implementation of `P0` in `γ_min,n,t` is
optimal (among one-shot protocols). -/
theorem thm_6_3_min (ht : t + 2 ≤ n) {P : (minCtx n t).Protocol} (hP : Implements P) :
    OptimalOneShot P :=
  thm_6_3 subset_rfl hP (prop_6_4_min ht P hP) (Min.nfConsistent P)

/-- **Theorem 6.3 for `γ_basic`**: if `t ≤ n - 2`, every implementation of `P0` in `γ_basic,n,t`
is optimal (among one-shot protocols). -/
theorem thm_6_3_basic (ht : t + 2 ≤ n) {P : (basicCtx n t).Protocol} (hP : Implements P) :
    OptimalOneShot P :=
  thm_6_3 subset_rfl hP (prop_6_4_basic ht P hP)
    ((Basic.nfConsistent (by omega)).congr ((Basic.thm_6_6 ht).state_eq hP))

/-- **Corollary 6.7** (`P^min`). If `t ≤ n - 2`, `P^min` is optimal w.r.t. `γ_min,n,t` (among
one-shot protocols). -/
theorem cor_6_7_min (ht : t + 2 ≤ n) : OptimalOneShot (pmin (n := n) (t := t) (t + 1)) :=
  thm_6_3_min ht (thm_6_5 ht)

/-- **Corollary 6.7** (`P^basic`). If `t ≤ n - 2`, `P^basic` is optimal w.r.t. `γ_basic,n,t`
(among one-shot protocols). -/
theorem cor_6_7_basic (ht : t + 2 ≤ n) : OptimalOneShot (pbasic (n := n) (t := t)) :=
  thm_6_3_basic ht (Basic.thm_6_6 ht)

/-- Non-vacuity: `P^min` and `P^basic` are EBA decision protocols that decide after at most
`t + 1` rounds (Proposition 6.1 applied to Theorems 6.5 and 6.6). -/
theorem pmin_pbasic_eba (ht : t + 2 ≤ n) :
    IsEBA (pmin (n := n) (t := t) (t + 1)) ∧ IsEBA (pbasic (n := n) (t := t)) :=
  ⟨(prop_6_1 subset_rfl (thm_6_5 ht)).1, (prop_6_1 subset_rfl (Basic.thm_6_6 ht)).1⟩

/-- Optimality (all competitors) implies optimality among one-shot competitors. -/
theorem Context.Optimal.optimalOneShot {γ : Context n} {P : γ.Protocol} (h : Optimal P) :
    OptimalOneShot P :=
  ⟨h.1, fun P' hE _ => h.2 P' hE⟩

/-- **Corollary 6.7 is false for `t = n - 1`**, in the paper's sense of optimality (all
competitors): `P^min` is not optimal in `γ_min,n,n-1` for `n ≥ 2`. -/
theorem cor_6_7_min_false' (hn : 2 ≤ n) :
    ¬ Optimal (pmin (n := n) (t := n - 1) (n - 1 + 1)) := fun h =>
  Counterexamples.cor_6_7_min_false hn h.optimalOneShot

end Podc.OptimalEBAOmission
