import Papers.PODC2024.HistoryIndependent.Alg4StepW

/-!
# Algorithm 4: Theorem 12
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K] {v₀ : Fin K}

/-- The invariant is preserved by the writer's internal steps. -/
lemma inv_stepW {s : St K} (hI : Inv v₀ s) (h1 : s.wpc ≠ .idle) (h2 : ∀ v, s.wpc ≠ .done v) :
    Inv v₀ (stepW s) := by
  cases hs : s.wpc with
  | idle => exact absurd hs h1
  | done v => exact absurd hs (h2 v)
  | scanB v j =>
    simp only [stepW, hs]
    cases hB : s.Bm j
    · by_cases hK : j.val + 1 < K
      · simp only [WPC.scanNext, Bool.false_eq_true, ite_false, hK, dite_true]
        exact inv_stepW_scanB_next hI hs hB hK
      · simp only [WPC.scanNext, Bool.false_eq_true, ite_false, hK, dite_false]
        exact inv_stepW_scanB_end hI hs hB hK
    · simp only [WPC.scanNext, ite_true]; exact inv_stepW_scanB_one hI hs hB
  | rdF1 v => simp only [stepW, hs]; exact inv_stepW_rdF1 hI hs
  | setB v => simp only [stepW, hs]; exact inv_stepW_setB hI hs
  | rdF2 v => simp only [stepW, hs]; exact inv_stepW_rdF2 hI hs
  | rdF1' v => simp only [stepW, hs]; exact inv_stepW_rdF1' hI hs
  | clrB v => simp only [stepW, hs]; exact inv_stepW_clrB hI hs
  | setA v => simp only [stepW, hs]; exact inv_stepW_setA hI hs
  | down v j => simp only [stepW, hs]; exact inv_stepW_down hI hs
  | up v j => simp only [stepW, hs]; exact inv_stepW_up hI hs

/-- **The invariant is preserved by every enabled step.** -/
theorem inv_sstep {s : St K} (hI : Inv v₀ s) {ℓ : Lbl v₀} (hen : Enabled v₀ s ℓ) :
    Inv v₀ (sstep v₀ s ℓ) := by
  cases ℓ with
  | inv p o =>
    cases p with
    | w =>
      obtain ⟨hw, v, rfl⟩ := hen
      exact inv_invW hI hw v
    | r =>
      obtain ⟨hr, rfl⟩ := hen
      exact inv_invR hI hr
  | tau p =>
    cases p with
    | w => exact inv_stepW hI hen.1 hen.2
    | r => exact inv_stepR hI hen.1 hen.2
  | ret p x =>
    cases p with
    | w =>
      have hen' : s.wpc = .done x := hen
      simp only [sstep, hen']; exact inv_retW hI hen'
    | r =>
      obtain ⟨val, hs, -⟩ := hen
      simp only [sstep, hs]; exact inv_retR hI hs

/-- The invariant holds at the end of every execution. -/
theorem inv_sOf {α : List (Lbl v₀)} (h : (alg4 v₀).Valid α) : Inv v₀ (sOf v₀ α) := by
  induction α using List.reverseRecOn with
  | nil => exact inv_init v₀
  | append_singleton α ℓ ih =>
    rw [sOf_snoc]
    exact inv_sstep (ih ((alg4 v₀).valid_of_prefix h (List.prefix_append _ _)))
      (enabled_of_valid v₀ h)

end Alg4

end Cslib.SharedMemory
