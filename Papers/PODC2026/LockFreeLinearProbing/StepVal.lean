import Papers.PODC2026.LockFreeLinearProbing.StepScan

/-!
# The invariant `Inv` is preserved: steps of owners that change no cell value
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

/-- Program counters of owners with an empty coverage (not in the duplicate scan). -/
def PC.noCov : PC → Bool
  | .l57LL | .l58SC | .dcLL76 | .dcSC78 | .dcLL79 | .dcSC80 => true
  | _ => false

lemma covers_of_noCov {l : Loc K m} (hl : l.pc.noCov) (c : Fin m) : ¬ covers h l c := by
  unfold covers; revert hl; cases l.pc <;> simp [PC.noCov]

/-- An owner step that changes no cell value and leads to an owner state with empty coverage. -/
lemma inv_val_noCov (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {c' : Cell K × List P}
    {l' : Loc K m} (hv : (C.loc p).pc.isVal) (hu : c'.1 = C.val x)
    (hlk : ∀ q, q ≠ p → (q ∈ c'.2 ↔ q ∈ C.lks x)) (hshape : LinkShape C p x c')
    (hop : l'.op = (C.loc p).op) (hj : l'.j = (C.loc p).j) (hnc : l'.pc.noCov)
    (hloc : LocInv l')
    (hlink : ∀ y w, recorded l' = some (y, w) → p ∈ (upd C p l' x c').lks y →
      (upd C p l' x c').val y = w) :
    Inv h (N + 1) ts (upd C p l' x c') := by
  have hv' : l'.pc.isVal := by revert hnc; cases l'.pc <;> simp [PC.noCov, PC.isVal]
  have hnd : ¬ (l'.pc = .docRD ∨ l'.pc = .docSC ∨ l'.pc = .docRD2) := by
    rintro (h1 | h1 | h1) <;> simp [h1, PC.noCov] at hnc
  refine inv_of_unchanged hI hp ⟨hu, hlk, hop, by rw [hv, hv'], fun _ => hj⟩ hloc hshape hlink
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ c hc; rw [hop, hj] at hc; exact hI.p3' p (Or.inr hv) c hc
  · intro J _ _ _ _ _ hc; exact absurd hc (covers_of_noCov hnc _)
  · rintro J (⟨h1 | h1, -⟩ | h1) <;> simp [h1] at hnd
  · rintro (⟨h1 | h1, -⟩ | h1) <;> simp [h1] at hnd
  · intro _ _ c hc; exact absurd hc (covers_of_noCov hnc _)
  · intro h1; simp [h1, PC.noCov] at hnc

lemma tau_l57LL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .l57LL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  refine inv_val_noCov hI hp hv rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl))
    ?_ ?_ ?_ ?_ ?_ <;> split_ifs <;> simp_all [PC.noCov, LocInv, recorded, Cfg.val, Cfg.lks]

lemma tau_dcLL76 (hI : Inv h N ts C) (hpc : (C.loc p).pc = .dcLL76)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  refine inv_val_noCov hI hp hv rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl))
    ?_ ?_ ?_ ?_ ?_ <;> split_ifs <;> simp_all [PC.noCov, LocInv, recorded, Cfg.val, Cfg.lks]

lemma tau_dcLL79 (hI : Inv h N ts C) (hpc : (C.loc p).pc = .dcLL79)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  refine inv_val_noCov hI hp hv rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl))
    ?_ ?_ ?_ ?_ ?_ <;> simp [PC.noCov, LocInv, recorded, Cfg.val, Cfg.lks]

/-- A failed `SC` of an owner leading to `del_copy` (line 76). -/
lemma inv_val_fail (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {l' : Loc K m}
    (hv : (C.loc p).pc.isVal) (hop : l'.op = (C.loc p).op) (hj : l'.j = (C.loc p).j)
    (hpc' : l'.pc = .dcLL76 ∨ l'.pc = .dcLL79) :
    Inv h (N + 1) ts (upd C p l' x (C.val x, C.lks x)) :=
  inv_val_noCov hI hp hv rfl (fun _ _ => Iff.rfl) (Or.inl rfl) hop hj
    (by rcases hpc' with h1 | h1 <;> simp [h1, PC.noCov])
    (by rcases hpc' with h1 | h1 <;> simp [h1, LocInv])
    (by rcases hpc' with h1 | h1 <;> simp [h1, recorded])

end Podc.LockFreeLinearProbing
