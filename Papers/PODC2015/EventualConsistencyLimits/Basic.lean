import Papers.PODC2015.EventualConsistencyLimits.Model

/-!
# Basic facts about executions and abstract executions
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*} [DecidableEq ι]

@[simp] lemma proj_nil (i : ι) : proj i ([] : List (ι × Ev Obj V M)) = [] := rfl

@[simp] lemma proj_append (i : ι) (α β : List (ι × Ev Obj V M)) :
    proj i (α ++ β) = proj i α ++ proj i β := by
  simp [proj, List.filterMap_append]

@[simp] lemma proj_cons (i j : ι) (e : Ev Obj V M) (α : List (ι × Ev Obj V M)) :
    proj i ((j, e) :: α) = if j = i then e :: proj i α else proj i α := by
  by_cases h : j = i <;> simp [proj, h]

lemma proj_singleton (i j : ι) (e : Ev Obj V M) :
    proj i [(j, e)] = if j = i then [e] else [] := by
  by_cases h : j = i <;> simp [proj, h]

lemma proj_eq_nil {i : ι} {β : List (ι × Ev Obj V M)} (h : ∀ x ∈ β, x.1 ≠ i) :
    proj i β = [] := by
  simp only [proj, List.filterMap_eq_nil_iff]
  intro x hx
  simp [h x hx]

namespace Store

variable (D : Store ι Obj V M St)

lemma run_append (i : ι) (l l' : List (Ev Obj V M)) :
    D.run i (l ++ l') = (D.run i l).bind fun σ => l'.foldlM (D.step i) σ := by
  simp [run, List.foldlM_append]

lemma state_append (i : ι) (α β : List (ι × Ev Obj V M)) :
    D.state i (α ++ β) = (D.state i α).bind fun σ => (proj i β).foldlM (D.step i) σ := by
  simp [state, run_append]

lemma state_snoc (i j : ι) (e : Ev Obj V M) (α : List (ι × Ev Obj V M)) :
    D.state i (α ++ [(j, e)]) = if j = i then (D.state i α).bind fun σ => D.step i σ e
      else D.state i α := by
  rw [state_append, proj_singleton]
  by_cases h : j = i
  · simp [h]
  · simp [h]

lemma state_append_of_not_mem {i : ι} (α β : List (ι × Ev Obj V M))
    (h : ∀ x ∈ β, x.1 ≠ i) : D.state i (α ++ β) = D.state i α := by
  rw [state_append, proj_eq_nil h]
  cases D.state i α <;> rfl

lemma state_snoc_self {i : ι} {e : Ev Obj V M} {α : List (ι × Ev Obj V M)} {σ : St}
    (h : D.state i α = some σ) : D.state i (α ++ [(i, e)]) = D.step i σ e := by
  simp [state_snoc, h]

lemma state_snoc_ne {i j : ι} {e : Ev Obj V M} (α : List (ι × Ev Obj V M)) (h : j ≠ i) :
    D.state i (α ++ [(j, e)]) = D.state i α := by
  simp [state_snoc, h]

@[simp] lemma state_nil (i : ι) : D.state i ([] : List (ι × Ev Obj V M)) = some (D.init i) :=
  rfl

/-- States only depend on the projection. -/
lemma state_congr {i : ι} {α β : List (ι × Ev Obj V M)} (h : proj i α = proj i β) :
    D.state i α = D.state i β := by
  simp [state, h]

namespace IsExec

variable {D}

lemma state_isSome {α : List (ι × Ev Obj V M)} (h : D.IsExec α) (i : ι) :
    ∃ σ, D.state i α = some σ := by
  induction h with
  | nil => exact ⟨_, rfl⟩
  | @snoc α j e σ σ' _ hσ hst _ ih =>
    by_cases hji : j = i
    · subst hji; exact ⟨σ', by rw [state_snoc_self D hσ, hst]⟩
    · rw [state_snoc_ne D α hji]; exact ih

lemma snoc' {α : List (ι × Ev Obj V M)} {i : ι} {e : Ev Obj V M} (h : D.IsExec α)
    (hen : ∀ σ, D.state i α = some σ → ∃ σ', D.step i σ e = some σ')
    (hr : ∀ m, e = .recv m → ∃ j, j ≠ i ∧ (j, .send m) ∈ α) : D.IsExec (α ++ [(i, e)]) := by
  obtain ⟨σ, hσ⟩ := h.state_isSome i
  obtain ⟨σ', h'⟩ := hen σ hσ
  exact .snoc h hσ h' hr

lemma of_append {α β : List (ι × Ev Obj V M)} (h : D.IsExec (α ++ β)) : D.IsExec α := by
  suffices ∀ γ, D.IsExec γ → ∀ β, γ = α ++ β → D.IsExec α from this _ h β rfl
  intro γ hγ
  induction hγ with
  | nil => intro β h; rw [List.nil_eq_append_iff] at h; rw [h.1]; exact .nil
  | @snoc α' i e σ σ' h' _ _ _ ih =>
    intro β hβ
    induction β using List.reverseRecOn with
    | nil => simp at hβ; rw [← hβ]; exact .snoc h' ‹_› ‹_› ‹_›
    | append_singleton β x _ =>
      rw [← List.append_assoc] at hβ
      obtain ⟨h1, -⟩ := List.append_inj' hβ rfl
      exact ih β h1

end IsExec

end Store

end Podc.EventualConsistencyLimits
