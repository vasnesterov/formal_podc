import Papers.PODC2019.SharpThresholdLLL.Process

/-!
# Examples: non-vacuity and sharpness of the criterion

* `ex3`: a rank-3 instance (one variable uniform on `Fin 8`, three events `X = 0`, `X = 1`,
  `X = 2`) with `d = 2` and `p = 1/8`, so `p · 2^d = 1/2 < 1`. All hypotheses of
  `theorem_1_3` hold, and the variable affects all three events (`ex3_rank`). So the theorem is
  not vacuous.
* `sharp`: with `≤` instead of `<` the statement fails. One fair bit `X` and two events `X = 0`,
  `X = 1` give `d = 1`, `Pr[E_v] = 1/2 = 2^{-d}`, and no assignment avoids both events
  (`sharp_no_good_assignment`).
-/

open Finset

namespace SharpThresholdLLL

/-! ## A rank-3 instance satisfying the hypotheses of Theorem 1.3 -/

/-- One variable, uniform on `Fin 8`; events `E_t = {X = t}` for `t : Fin 3`. -/
noncomputable def ex3 : Instance Unit (fun _ => Fin 8) (Fin 3) where
  prob _ _ := 1 / 8
  prob_nonneg _ _ := by norm_num
  prob_sum _ := by simp
  vbl _ := {()}
  bad t x := (x () : ℕ) = t
  bad_local t x y h := by rw [h () (by simp)]

lemma ex3_pr (t : Fin 3) : ex3.pr t = 1 / 8 := by
  classical
  unfold Instance.pr Instance.condProb Cslib.Probability.piExpect Cslib.Probability.piWeight
    Instance.marg Instance.empty
  rw [← (Equiv.funUnique Unit (Fin 8)).symm.sum_comp]
  simp only [Fintype.prod_unique, Equiv.funUnique_symm_apply, ex3]
  fin_cases t <;> simp [Fin.sum_univ_eight]

lemma ex3_rank : (ex3.evs ()).card = 3 := by
  decide

lemma ex3_dep (t : Fin 3) : (ex3.dep t).card ≤ 2 := by
  fin_cases t <;> decide

/-- Theorem 1.3 applies to `ex3` (with `p = 1/8`, `d = 2`). -/
theorem ex3_theorem_1_3 :
    (∀ s, ex3.Reachable (1 / 8) s → ∀ j, s.σ j = none → ∃ s', ex3.Step (1 / 8) j s s') ∧
      (∀ s, ex3.Reachable (1 / 8) s → ∀ x : Unit → Fin 8, (∀ i, s.σ i = some (x i)) →
        ∀ v, ¬ ex3.bad v x) ∧
      ∃ x : Unit → Fin 8, ∀ v, ¬ ex3.bad v x :=
  ex3.theorem_1_3 (p := 1 / 8) (d := 2) (fun _ => by rw [ex3_rank]) (fun t => (ex3_pr t).le)
    ex3_dep (by norm_num)

/-! ## The criterion `p < 2^{-d}` cannot be relaxed to `p ≤ 2^{-d}` -/

/-- One fair bit; `E_b = {X = b}`. -/
noncomputable def sharp : Instance Unit (fun _ => Bool) Bool where
  prob _ _ := 1 / 2
  prob_nonneg _ _ := by norm_num
  prob_sum _ := by simp
  vbl _ := {()}
  bad b x := x () = b
  bad_local b x y h := by rw [h () (by simp)]

lemma sharp_pr (b : Bool) : sharp.pr b = 1 / 2 := by
  classical
  unfold Instance.pr Instance.condProb Cslib.Probability.piExpect Cslib.Probability.piWeight
    Instance.marg Instance.empty
  rw [← (Equiv.funUnique Unit Bool).symm.sum_comp]
  simp only [Fintype.prod_unique, Equiv.funUnique_symm_apply, sharp]
  cases b <;> simp

lemma sharp_dep (b : Bool) : (sharp.dep b).card = 1 := by
  cases b <;> decide

lemma sharp_rank : (sharp.evs ()).card = 2 := by decide

/-- At the threshold `p · 2^d = 1` (here `p = 1/2`, `d = 1`, rank 2) no assignment avoids all
bad events. So Theorems 1.1 and 1.3 need the strict inequality. -/
theorem sharp_no_good_assignment :
    (∀ b, sharp.pr b ≤ 1 / 2) ∧ (∀ b, (sharp.dep b).card ≤ 1) ∧ (1 / 2 : ℝ) * 2 ^ 1 = 1 ∧
      ¬ ∃ x : Unit → Bool, ∀ b, ¬ sharp.bad b x := by
  refine ⟨fun b => (sharp_pr b).le, fun b => (sharp_dep b).le, by norm_num, ?_⟩
  rintro ⟨x, hx⟩
  exact hx (x ()) rfl

end SharpThresholdLLL
