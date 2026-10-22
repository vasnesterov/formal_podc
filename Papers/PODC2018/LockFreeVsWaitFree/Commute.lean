import Papers.PODC2018.LockFreeVsWaitFree.Critical

/-!
# Commuting steps (used in Lemma 8 and Claim 9 of [ACHP18])

* `Impl.step_swap` — if the step of `a` does not change the base object accessed by the step of
  `b` (it accesses another object, or only reads it), then executing the two steps in either
  order leads to configurations that agree on the memory and on every process other than `a`.
* `Ctx.Good.swap` — the same for the next labels of two processes after a good execution.
* `Ctx.opsOf_ext_single`, `Ctx.respsOf_ext_single` — the operations and responses of a process
  scheduled once only depend on its own step.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory Impl

section StepSwap

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

-- CSLib candidate
/-- A step leaves base object `j` unchanged if it does not access it or applies a read-only
operation to it. -/
lemma mem_step_of_readOnly {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {j : ι} (hj : ∀ o k, ℓ = .tau ℓ.proc → I.act ℓ.proc (C.loc ℓ.proc) = .access j o k →
      (B j).ReadOnly o) : C'.mem j = C.mem j := by
  rcases mem_of_step h j with e | ⟨hτ, -, o, k, hact, hv⟩
  · exact e
  · rw [hv]; exact hj o k hτ hact _

-- CSLib candidate
/-- Two steps with the same label from configurations in which the stepping process has the same
local state, from the same state of base object `j`, lead to the same state of `j`. -/
lemma mem_step_eq {C C' D D' : Config A B P L} {ℓ : Label P A} (hC : I.step C ℓ = some C')
    (hD : I.step D ℓ = some D') (hloc : C.loc ℓ.proc = D.loc ℓ.proc) {j : ι}
    (hj : C.mem j = D.mem j) : C'.mem j = D'.mem j := by
  cases ℓ with
  | inv p o => rw [(step_inv hC).2.2.2.2, (step_inv hD).2.2.2.2, hj]
  | ret p r => rw [(step_ret hC).2.2.1, (step_ret hD).2.2.1, hj]
  | tau p =>
    obtain ⟨-, -, i, o, k, hact, hm, -⟩ := step_tau hC
    obtain ⟨-, -, i', o', k', hact', hm', -⟩ := step_tau hD
    simp only [Label.proc] at hloc
    rw [← hloc, hact] at hact'
    cases hact'
    rw [hm, hm']
    by_cases hji : j = i
    · subst hji; simp [hj]
    · simp [Function.update_of_ne hji, hj]

-- CSLib candidate
/-- **Commuting steps.** If the step `ℓa` of `a` does not change the base object accessed by the
step `ℓb` of `b ≠ a` (it accesses another object or reads it), the two orders lead to
configurations that agree on the memory and on all processes other than `a`. -/
lemma step_swap {a b : P} (hab : a ≠ b) {C Ca Cab Cb Cba : Config A B P L} {ℓa ℓb : Label P A}
    (hpa : ℓa.proc = a) (hpb : ℓb.proc = b) (h1 : I.step C ℓa = some Ca)
    (h2 : I.step Ca ℓb = some Cab) (h3 : I.step C ℓb = some Cb) (h4 : I.step Cb ℓa = some Cba)
    (hnw : ∀ i o, ℓb = .tau b → I.PoisedAt C b i o → ∀ o', ℓa = .tau a → I.PoisedAt C a i o' →
      (B i).ReadOnly o') :
    AgreeOn {r | r ≠ a} Cab Cba := by
  have hCa_b := step_other h1 (show ℓa.proc ≠ b by rw [hpa]; exact hab)
  have hCb_a := step_other h3 (show ℓb.proc ≠ a by rw [hpb]; exact Ne.symm hab)
  -- `a`'s step does not change the object accessed by `b`'s step
  have hA : ∀ j o, ℓb = .tau b → I.PoisedAt C b j o → ∀ {D D' : Config A B P L},
      I.step D ℓa = some D' → D.loc a = C.loc a → D'.mem j = D.mem j := by
    intro j o hτb hpo D D' hD hlD
    apply mem_step_of_readOnly hD
    intro o' k hτ hact
    rw [hpa] at hτ hact
    rw [hlD] at hact
    have hpend : C.pend a ≠ none := by rw [hτ] at h1; exact (step_tau h1).1
    exact hnw j o hτb hpo o' hτ ⟨hpend, k, hact⟩
  refine ⟨?_, ?_, ?_⟩
  · funext j
    by_cases hbj : ℓb = .tau b ∧ ∃ o, I.PoisedAt C b j o
    · obtain ⟨hτb, o, hpo⟩ := hbj
      have e1 : Ca.mem j = C.mem j := hA j o hτb hpo h1 rfl
      have e2 : Cba.mem j = Cb.mem j := hA j o hτb hpo h4 hCb_a.1
      rw [e2]
      exact mem_step_eq h2 h3 (by rw [hpb]; exact hCa_b.1) e1
    · have hB : ∀ {D D' : Config A B P L}, I.step D ℓb = some D' → D.loc b = C.loc b →
          D'.mem j = D.mem j := by
        intro D D' hD hlD
        rcases mem_of_step hD j with e | ⟨hτ, -, o, k, hact, -⟩
        · exact e
        · exfalso
          rw [hpb] at hτ hact
          rw [hlD] at hact
          have hpend : C.pend b ≠ none := by rw [hτ] at h3; exact (step_tau h3).1
          exact hbj ⟨hτ, o, hpend, k, hact⟩
      rw [hB h2 hCa_b.1]
      exact mem_step_eq h1 h4 (by rw [hpa]; exact hCb_a.1.symm) (hB h3 rfl).symm
  · intro r hr
    simp only [Set.mem_ofPred_eq] at hr
    by_cases hrb : r = b
    · subst hrb
      have hobj : ∀ i o k, ℓb = .tau r → I.act r (Ca.loc r) = .access i o k →
          Ca.mem i = C.mem i := by
        intro i o k hτ hact
        rw [hCa_b.1] at hact
        have hpend : C.pend r ≠ none := by rw [hτ] at h3; exact (step_tau h3).1
        exact hA i o hτ ⟨hpend, k, hact⟩ h1 rfl
      obtain ⟨D', hD', hl, -, -⟩ := step_exact hpb hCa_b.1 hCa_b.2 hobj h2
      rw [h3] at hD'; cases hD'
      rw [← hl, (step_other h4 (show ℓa.proc ≠ r by rw [hpa]; exact hab)).1]
    · rw [(step_other h2 (show ℓb.proc ≠ r by rw [hpb]; exact Ne.symm hrb)).1,
        (step_other h1 (show ℓa.proc ≠ r by rw [hpa]; exact Ne.symm hr)).1,
        (step_other h4 (show ℓa.proc ≠ r by rw [hpa]; exact Ne.symm hr)).1,
        (step_other h3 (show ℓb.proc ≠ r by rw [hpb]; exact Ne.symm hrb)).1]
  · intro r hr
    simp only [Set.mem_ofPred_eq] at hr
    by_cases hrb : r = b
    · subst hrb
      have hobj : ∀ i o k, ℓb = .tau r → I.act r (Ca.loc r) = .access i o k →
          Ca.mem i = C.mem i := by
        intro i o k hτ hact
        rw [hCa_b.1] at hact
        have hpend : C.pend r ≠ none := by rw [hτ] at h3; exact (step_tau h3).1
        exact hA i o hτ ⟨hpend, k, hact⟩ h1 rfl
      obtain ⟨D', hD', -, hp, -⟩ := step_exact hpb hCa_b.1 hCa_b.2 hobj h2
      rw [h3] at hD'; cases hD'
      rw [← hp, (step_other h4 (show ℓa.proc ≠ r by rw [hpa]; exact hab)).2]
    · rw [(step_other h2 (show ℓb.proc ≠ r by rw [hpb]; exact Ne.symm hrb)).2,
        (step_other h1 (show ℓa.proc ≠ r by rw [hpa]; exact Ne.symm hr)).2,
        (step_other h4 (show ℓa.proc ≠ r by rw [hpa]; exact Ne.symm hr)).2,
        (step_other h3 (show ℓb.proc ≠ r by rw [hpb]; exact Ne.symm hrb)).2]

end StepSwap

namespace Ctx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] {X : Ctx P ι L B}

/-- The next label of `p` only depends on its local state, its pending operation and the
invocation status of `p₀`. -/
lemma nl_congr {α α' : List (LLabel P)} {p : P} (hl : (X.cfg α).loc p = (X.cfg α').loc p)
    (hp : (X.cfg α).pend p = (X.cfg α').pend p)
    (hst : p = X.p₀ → (opsOf α X.p₀ = [] ↔ opsOf α' X.p₀ = [])) : X.nl α p = X.nl α' p := by
  have hnext : X.I.nextLabel (X.cfg α) p = X.I.nextLabel (X.cfg α') p := by
    unfold nextLabel; rw [hl]
  unfold nl
  rw [hp, hnext]
  by_cases hpr : p = X.p₀
  · subst hpr
    have := hst rfl
    by_cases h1 : opsOf α X.p₀ = []
    · simp [h1, this.1 h1]
    · have h2 : opsOf α' X.p₀ ≠ [] := fun h => h1 (this.2 h)
      simp [h1, h2]
  · simp [hpr]

/-- The next label of `p` is not changed by steps of other processes. -/
lemma Good.nl_ext_of_not_mem {α : List (LLabel P)} (hα : X.Good α) {p : P} {σ : List P}
    (hp : p ∉ σ) : X.nl (X.ext α σ) p = X.nl α p := by
  obtain ⟨h1, h2⟩ := hα.ext_other hp
  refine nl_congr h1 h2 (fun h => ?_)
  subst h; rw [opsOf_ext_of_not_mem hp]

/-- `p` is poised at `i` with operation `o` after `α`. -/
lemma Good.poised_ext_of_not_mem {α : List (LLabel P)} (hα : X.Good α) {p : P} {σ : List P}
    (hp : p ∉ σ) {i : ι} {o : (B i).Op} :
    X.I.PoisedAt (X.cfg (X.ext α σ)) p i o ↔ X.I.PoisedAt (X.cfg α) p i o := by
  obtain ⟨h1, h2⟩ := hα.ext_other hp
  exact ⟨fun h => h.congr h1 h2, fun h => h.congr h1.symm h2.symm⟩

/-- **Commuting the next steps of two processes** (schedule version of `step_swap`). -/
lemma Good.swap {α : List (LLabel P)} (hα : X.Good α) {a b : P} (hab : a ≠ b)
    {ℓa ℓb : LLabel P} (ha : X.nl α a = some ℓa) (hb : X.nl α b = some ℓb)
    (hnw : ∀ i o, X.I.PoisedAt (X.cfg α) b i o → ∀ o', X.I.PoisedAt (X.cfg α) a i o' →
      (B i).ReadOnly o') :
    X.ext α [a, b] = α ++ [ℓa, ℓb] ∧ X.ext α [b, a] = α ++ [ℓb, ℓa] ∧
      AgreeOn {r | r ≠ a} (X.cfg (α ++ [ℓa, ℓb])) (X.cfg (α ++ [ℓb, ℓa])) := by
  have hb' : X.nl (X.ext α [a]) b = some ℓb := by
    rw [hα.nl_ext_of_not_mem (by simpa using Ne.symm hab), hb]
  have ha' : X.nl (X.ext α [b]) a = some ℓa := by
    rw [hα.nl_ext_of_not_mem (by simpa using hab), ha]
  have e1 : X.ext α [a, b] = α ++ [ℓa, ℓb] := by
    rw [show [a, b] = [a] ++ [b] from rfl, ext_concat, ext1_of_some hb', ext_singleton,
      ext1_of_some ha]; simp
  have e2 : X.ext α [b, a] = α ++ [ℓb, ℓa] := by
    rw [show [b, a] = [b] ++ [a] from rfl, ext_concat, ext1_of_some ha', ext_singleton,
      ext1_of_some hb]; simp
  refine ⟨e1, e2, ?_⟩
  have hga : X.Good (α ++ [ℓa]) := (hα.nl_step ha).2
  have hgb : X.Good (α ++ [ℓb]) := (hα.nl_step hb).2
  have hb'' : X.nl (α ++ [ℓa]) b = some ℓb := by rwa [ext_singleton, ext1_of_some ha] at hb'
  have ha'' : X.nl (α ++ [ℓb]) a = some ℓa := by rwa [ext_singleton, ext1_of_some hb] at ha'
  have s1 := (hα.nl_step ha).1
  have s2 := (hga.nl_step hb'').1
  have s3 := (hα.nl_step hb).1
  have s4 := (hgb.nl_step ha'').1
  simp only [List.append_assoc, List.singleton_append] at s2 s4
  refine step_swap hab (nl_proc ha) (nl_proc hb) s1 s2 s3 s4 ?_
  intro i o _ hpo o' _ hpo'
  exact hnw i o hpo o' hpo'

/-- The operations of a process scheduled exactly once only depend on its own step. -/
lemma opsOf_ext_single (α : List (LLabel P)) {p : P} {σ τ : List P} (hσ : p ∉ σ) (hτ : p ∉ τ)
    (hα : X.Good α) :
    opsOf (X.ext α (σ ++ p :: τ)) p = opsOf (X.ext1 α p) p ∧
      respsOf (X.ext α (σ ++ p :: τ)) p = respsOf (X.ext1 α p) p := by
  rw [show σ ++ p :: τ = (σ ++ [p]) ++ τ by simp, ext_append, ext_concat,
    opsOf_ext_of_not_mem hτ, respsOf_ext_of_not_mem hτ]
  unfold Ctx.ext1
  rw [hα.nl_ext_of_not_mem hσ, opsOf_append, respsOf_append, opsOf_append, respsOf_append,
    opsOf_ext_of_not_mem hσ, respsOf_ext_of_not_mem hσ]
  exact ⟨rfl, rfl⟩

end Ctx

end Podc.LockFreeVsWaitFree
