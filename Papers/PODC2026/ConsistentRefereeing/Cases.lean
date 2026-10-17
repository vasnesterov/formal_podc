import Papers.PODC2026.ConsistentRefereeing.Critical

/-!
# Theorem 5: the cases of the critical step

Fix a critical execution `K : Crit I ref` and competitors `i ≠ j` with `v i ≠ v j`, and a third
competitor `k`. The cases of the proof of Theorem 5 of [ACE26]:

* `Crit.invisible` — the step of `i` does not change the memory (case 3a and invocations or
  responses): `α·i·j` and `α·j` agree on the memory, `k` and the referee;
* `Crit.distinct` — case 1, distinct base objects: `α·i·j` and `α·j·i` reach the same memory;
* `Crit.interfering` — case 2, the same interfering object: the two orders commute (2a) or one
  step overwrites the other (2b).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Impl

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι]
variable {I : Impl (contestObj P) B P L} {ref : P}

/-- The hypotheses of Theorem 5 on the implementation. -/
structure Hyps (I : Impl (contestObj P) B P L) (ref : P) : Prop where
  lf : I.LockFreeOn (Adm ref)
  sl : I.StrongLinOn (Adm ref)
  allowed : ∀ p, I.allowed p (roleOp ref p)

namespace Crit

variable (K : Crit I ref)

lemma invOf_lbl {c q : P} (hc : c ≠ ref) (hq : c ≠ q) : (K.lbl c).invOf q = none :=
  Label.invOf_eq_none_of_proc_ne (by rw [K.lbl_proc hc]; exact hq)

lemma run_ext {β : List (Label P (contestObj P))} {D : Config (contestObj P) B P L}
    (h : I.runFrom K.C β = some D) : I.run (K.α ++ β) = some D := by
  rw [run_append_of_eq I K.run, h]

/-- The memory after two `tau` steps with known actions. -/
lemma two_tau {C C₁ C₂ : Config (contestObj P) B P L} {p q : P} (hpq : p ≠ q)
    (h₁ : I.step C (.tau p) = some C₁) (h₂ : I.step C₁ (.tau q) = some C₂)
    {a : ι} {oa : (B a).Op} {ka : (B a).Resp → L} (hp : I.act p (C.loc p) = .access a oa ka)
    {b : ι} {ob : (B b).Op} {kb : (B b).Resp → L} (hq : I.act q (C.loc q) = .access b ob kb) :
    C₂.mem = Function.update (Function.update C.mem a ((B a).δ (C.mem a) oa).1) b
      ((B b).δ ((Function.update C.mem a ((B a).δ (C.mem a) oa).1) b) ob).1 := by
  obtain ⟨m₁, -, -⟩ := step_tau_mem h₁ hp
  have hq' : I.act q (C₁.loc q) = .access b ob kb := by
    rw [(step_other h₁ (by simpa [Label.proc] using hpq)).1]; exact hq
  obtain ⟨m₂, -, -⟩ := step_tau_mem h₂ hq'
  rw [m₂, m₁]

variable (H : Hyps I ref)
include H

/-- Case "the step of `i` does not change the memory" (case 3a; also invocations and
responses). -/
theorem invisible {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j) {C₁ : Config (contestObj P) B P L}
    (h₁ : I.step K.C (K.lbl i) = some C₁) (hmem : C₁.mem = K.C.mem) : False := by
  obtain ⟨-, -, hA₁⟩ := K.step₁ H.allowed hi
  obtain ⟨C₁₂, h₁₂, hA₁₂⟩ := K.step₂ H.allowed hi hj hij h₁ hA₁
  obtain ⟨C₂, h₂, hA₂⟩ := K.step₁ H.allowed hj
  have hag₁ : Impl.Agree j C₁ K.C := by
    have := step_other h₁ (q := j) (by rw [K.lbl_proc hi]; exact hij)
    exact ⟨hmem, this.1, this.2⟩
  obtain ⟨D, hD, hagD⟩ := step_agree hag₁ (K.lbl_proc hj) h₁₂
  rw [h₂] at hD; cases hD
  have hr₁ : I.runFrom K.C ([K.lbl i] ++ [K.lbl j]) = some C₁₂ := by
    simp [runFrom_cons, h₁, h₁₂]
  have hr₂ : I.runFrom K.C [K.lbl j] = some C₂ := by simp [runFrom_cons, h₂]
  have hag := agreeOn_of_mem (Q := ({k, ref} : Set P)) hr₁ hr₂
    (fun ℓ hℓ => by
      simp only [List.mem_append, List.mem_singleton] at hℓ
      rcases hℓ with rfl | rfl <;> simp [K.lbl_proc hi, K.lbl_proc hj, hik, hi, hjk, hj])
    (fun ℓ hℓ => by simp only [List.mem_singleton] at hℓ; subst hℓ; simp [K.lbl_proc hj, hjk, hj])
    hagD.mem
  refine K.contra H.lf H.sl H.allowed hi hj hk hv (β₁ := [K.lbl j]) (β₂ := [])
    (by rw [List.append_assoc]; exact K.run_ext hr₁) (by simpa using K.run_ext hr₂)
    hA₁₂ (by simpa using hA₂) (by simp [K.invOf_lbl hj hj]) (by simp) ?_ hag
  simp [opsOf_append, K.invOf_lbl hi hik, K.invOf_lbl hj hjk]

/-- Case 1: the steps of `i` and `j` modify distinct base objects. -/
theorem distinct {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j)
    {a : ι} {oa : (B a).Op} {ka : (B a).Resp → L} (hli : K.lbl i = .tau i)
    (hai : I.act i (K.C.loc i) = .access a oa ka)
    {b : ι} {ob : (B b).Op} {kb : (B b).Resp → L} (hlj : K.lbl j = .tau j)
    (hbj : I.act j (K.C.loc j) = .access b ob kb) (hab : a ≠ b) : False := by
  obtain ⟨C₁, h₁, hA₁⟩ := K.step₁ H.allowed hi
  obtain ⟨C₁₂, h₁₂, hA₁₂⟩ := K.step₂ H.allowed hi hj hij h₁ hA₁
  obtain ⟨C₂, h₂, hA₂⟩ := K.step₁ H.allowed hj
  obtain ⟨C₂₁, h₂₁, hA₂₁⟩ := K.step₂ H.allowed hj hi hij.symm h₂ hA₂
  have m₁₂ := two_tau hij (hli ▸ h₁) (hlj ▸ h₁₂) hai hbj
  have m₂₁ := two_tau hij.symm (hlj ▸ h₂) (hli ▸ h₂₁) hbj hai
  rw [Function.update_of_ne hab.symm] at m₁₂
  rw [Function.update_of_ne hab] at m₂₁
  have hmem : C₁₂.mem = C₂₁.mem := by rw [m₁₂, m₂₁, Function.update_comm hab.symm]
  have hr₁ : I.runFrom K.C ([K.lbl i] ++ [K.lbl j]) = some C₁₂ := by
    simp [runFrom_cons, h₁, h₁₂]
  have hr₂ : I.runFrom K.C ([K.lbl j] ++ [K.lbl i]) = some C₂₁ := by
    simp [runFrom_cons, h₂, h₂₁]
  have hQ : ∀ ℓ ∈ [K.lbl i] ++ [K.lbl j], ℓ.proc ∉ ({k, ref} : Set P) := fun ℓ hℓ => by
    simp only [List.mem_append, List.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl <;> simp [K.lbl_proc hi, K.lbl_proc hj, hik, hi, hjk, hj]
  have hQ' : ∀ ℓ ∈ [K.lbl j] ++ [K.lbl i], ℓ.proc ∉ ({k, ref} : Set P) := fun ℓ hℓ =>
    hQ ℓ (by simp only [List.mem_append, List.mem_singleton] at hℓ ⊢; tauto)
  have hag := agreeOn_of_mem (Q := ({k, ref} : Set P)) hr₁ hr₂ hQ hQ' hmem
  refine K.contra H.lf H.sl H.allowed hi hj hk hv (β₁ := [K.lbl j]) (β₂ := [K.lbl i])
    (by rw [List.append_assoc]; exact K.run_ext hr₁) (by rw [List.append_assoc]; exact K.run_ext hr₂)
    hA₁₂ hA₂₁ (by simp [K.invOf_lbl hj hj]) (by simp [K.invOf_lbl hi hi]) ?_ hag
  simp [opsOf_append, K.invOf_lbl hi hik, K.invOf_lbl hj hjk]

/-- Case 2: the steps of `i` and `j` access the same object, on whose current state they commute
or one overwrites the other (e.g. an interfering object). -/
theorem interfering_at {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j)
    {a : ι} {oa ob : (B a).Op} {ka kb : (B a).Resp → L} (hli : K.lbl i = .tau i)
    (hai : I.act i (K.C.loc i) = .access a oa ka) (hlj : K.lbl j = .tau j)
    (hbj : I.act j (K.C.loc j) = .access a ob kb)
    (hI : (B a).CommuteAt (K.C.mem a) oa ob ∨ (B a).OverwritesAt (K.C.mem a) oa ob ∨
      (B a).OverwritesAt (K.C.mem a) ob oa) : False := by
  obtain ⟨C₁, h₁, hA₁⟩ := K.step₁ H.allowed hi
  obtain ⟨C₁₂, h₁₂, hA₁₂⟩ := K.step₂ H.allowed hi hj hij h₁ hA₁
  obtain ⟨C₂, h₂, hA₂⟩ := K.step₁ H.allowed hj
  obtain ⟨C₂₁, h₂₁, hA₂₁⟩ := K.step₂ H.allowed hj hi hij.symm h₂ hA₂
  have m₁₂ := two_tau hij (hli ▸ h₁) (hlj ▸ h₁₂) hai hbj
  have m₂₁ := two_tau hij.symm (hlj ▸ h₂) (hli ▸ h₂₁) hbj hai
  have m₁ := (step_tau_mem (hli ▸ h₁) hai).1
  have m₂ := (step_tau_mem (hlj ▸ h₂) hbj).1
  simp only [Function.update_self, Function.update_idem] at m₁₂ m₂₁
  have hQ : ∀ ℓ ∈ [K.lbl i] ++ [K.lbl j], ℓ.proc ∉ ({k, ref} : Set P) := fun ℓ hℓ => by
    simp only [List.mem_append, List.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl <;> simp [K.lbl_proc hi, K.lbl_proc hj, hik, hi, hjk, hj]
  have hQi : ∀ ℓ ∈ [K.lbl i], ℓ.proc ∉ ({k, ref} : Set P) := fun ℓ hℓ => hQ ℓ (by simp_all)
  have hQj : ∀ ℓ ∈ [K.lbl j], ℓ.proc ∉ ({k, ref} : Set P) := fun ℓ hℓ => hQ ℓ (by simp_all)
  have hQ' : ∀ ℓ ∈ [K.lbl j] ++ [K.lbl i], ℓ.proc ∉ ({k, ref} : Set P) := fun ℓ hℓ =>
    hQ ℓ (by simp only [List.mem_append, List.mem_singleton] at hℓ ⊢; tauto)
  have hr₁ : I.runFrom K.C [K.lbl i] = some C₁ := by simp [runFrom_cons, h₁]
  have hr₁₂ : I.runFrom K.C ([K.lbl i] ++ [K.lbl j]) = some C₁₂ := by
    simp [runFrom_cons, h₁, h₁₂]
  have hr₂ : I.runFrom K.C [K.lbl j] = some C₂ := by simp [runFrom_cons, h₂]
  have hr₂₁ : I.runFrom K.C ([K.lbl j] ++ [K.lbl i]) = some C₂₁ := by
    simp [runFrom_cons, h₂, h₂₁]
  have hst : ∀ ℓ ∈ [K.lbl i] ++ [K.lbl j], ∀ q, ℓ.invOf q = none → True := fun _ _ _ _ => trivial
  clear hst
  rcases hI with hc | hov | hov
  · -- 2a: the two steps commute
    have hag := agreeOn_of_mem (Q := ({k, ref} : Set P)) hr₁₂ hr₂₁ hQ hQ' (by rw [m₁₂, m₂₁, hc])
    refine K.contra H.lf H.sl H.allowed hi hj hk hv (β₁ := [K.lbl j]) (β₂ := [K.lbl i])
      (by rw [List.append_assoc]; exact K.run_ext hr₁₂)
      (by rw [List.append_assoc]; exact K.run_ext hr₂₁)
      hA₁₂ hA₂₁ (by simp [K.invOf_lbl hj hj]) (by simp [K.invOf_lbl hi hi]) ?_ hag
    simp [opsOf_append, K.invOf_lbl hi hik, K.invOf_lbl hj hjk]
  · -- 2b: the step of `i` overwrites the step of `j`: `α·j·i` and `α·i`
    have hag := agreeOn_of_mem (Q := ({k, ref} : Set P)) hr₁ hr₂₁ hQi hQ' (by rw [m₁, m₂₁, hov])
    refine K.contra H.lf H.sl H.allowed hi hj hk hv (β₁ := []) (β₂ := [K.lbl i])
      (by simpa using K.run_ext hr₁) (by rw [List.append_assoc]; exact K.run_ext hr₂₁)
      (by simpa using hA₁) hA₂₁ (by simp) (by simp [K.invOf_lbl hi hi]) ?_ hag
    simp [opsOf_append, K.invOf_lbl hi hik, K.invOf_lbl hj hjk]
  · -- 2b: the step of `j` overwrites the step of `i`: `α·i·j` and `α·j`
    have hag := agreeOn_of_mem (Q := ({k, ref} : Set P)) hr₁₂ hr₂ hQ hQj (by rw [m₁₂, m₂, hov])
    refine K.contra H.lf H.sl H.allowed hi hj hk hv (β₁ := [K.lbl j]) (β₂ := [])
      (by rw [List.append_assoc]; exact K.run_ext hr₁₂) (by simpa using K.run_ext hr₂)
      hA₁₂ (by simpa using hA₂) (by simp [K.invOf_lbl hj hj]) (by simp) ?_ hag
    simp [opsOf_append, K.invOf_lbl hi hik, K.invOf_lbl hj hjk]

/-- Case 2: the steps of `i` and `j` access the same interfering object. -/
theorem interfering {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j)
    {a : ι} {oa ob : (B a).Op} {ka kb : (B a).Resp → L} (hli : K.lbl i = .tau i)
    (hai : I.act i (K.C.loc i) = .access a oa ka) (hlj : K.lbl j = .tau j)
    (hbj : I.act j (K.C.loc j) = .access a ob kb) (hI : (B a).Interfering) : False :=
  K.interfering_at H hi hj hk hij hik hjk hv hli hai hlj hbj (hI _ _ _)

end Crit

end Referee

end Cslib.SharedMemory
