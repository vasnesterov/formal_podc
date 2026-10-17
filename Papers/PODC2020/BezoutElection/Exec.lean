import Papers.PODC2020.BezoutElection.Defs

/-!
# Generic lemmas on executions (pending operations, outputs)

CSLib candidates (they hold for any implementation `Impl A B P L`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
  {I : Impl A B P L}

-- CSLib candidate
/-- A pending operation can only disappear by a response of its process. -/
lemma step_pend_none {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {p : P} (hp : C.pend p ≠ none) (hp' : C'.pend p = none) : ∃ r, ℓ = .ret p r := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv p' o => simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv h).1 hp
    | tau p' =>
      simp only [Label.proc] at hq; subst hq
      rw [(Impl.step_tau h).2.1] at hp'; exact absurd hp' hp
    | ret p' r => simp only [Label.proc] at hq; subst hq; exact ⟨r, rfl⟩
  · rw [(Impl.step_other h hq).2] at hp'; exact absurd hp' hp

-- CSLib candidate
/-- If `p` is pending at time `t` and idle at time `t₂ ≥ t`, it returns in between. -/
lemma InfExec.exists_ret_between (e : I.InfExec) {p : P} {t t₂ : ℕ}
    (hp : (e.cfg t).pend p ≠ none) (hp₂ : (e.cfg t₂).pend p = none) (ht : t ≤ t₂) :
    ∃ t', t ≤ t' ∧ t' < t₂ ∧ ∃ r, e.lbl t' = .ret p r := by
  induction t₂, ht using Nat.le_induction with
  | base => exact absurd hp₂ hp
  | succ t₂ ht ih =>
    by_cases h : (e.cfg t₂).pend p = none
    · obtain ⟨t', h1, h2, h3⟩ := ih h; exact ⟨t', h1, by omega, h3⟩
    · obtain ⟨r, hr⟩ := step_pend_none (e.step_eq t₂) h hp₂
      exact ⟨t₂, ht, by omega, r, hr⟩

-- CSLib candidate
lemma outputs_append (α β : List (Label P A)) (p : P) :
    outputs (α ++ β) p = (outputs α p).or (outputs β p) := by
  simp [outputs, respsOf_append, List.head?_append]

-- CSLib candidate
lemma outputs_ne_none_of_mem {α : List (Label P A)} {p : P} {r : A.Resp}
    (h : Label.ret p r ∈ α) : outputs α p ≠ none := by
  unfold outputs respsOf
  intro hn
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at hn
  simpa using hn _ h

lemma outputs_eq_none_of_proc_ne {α : List (Label P A)} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    outputs α p = none := by
  simp [outputs, respsOf_eq_nil_of_proc_ne h]

end BezoutElection
