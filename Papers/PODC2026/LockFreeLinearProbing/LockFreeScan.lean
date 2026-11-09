import Papers.PODC2026.LockFreeLinearProbing.LockFreeStep

/-!
# Lock-freedom: the steps of scanning operations and of the free-cell search
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] [Fintype P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

lemma budL_isVal {l : Loc K m} (hl : l.pc.isVal) (c : Cell K) : budL l c = 1 + credit c := by
  unfold budL; revert hl; cases l.pc <;> simp [PC.isVal]

@[simp] lemma credit_tent (v : K) : credit (Cell.key v .tent) = 1 := rfl
@[simp] lemma credit_reval (v : K) : credit (Cell.key v .reval) = 2 := rfl

/-- The owner of a cell holding a non-final copy. -/
lemma exists_owner (hI : Inv h N ts C) {x : Fin m} {v : K} {t : Tag} (hx : C.val x = .key v t)
    (ht : t ≠ .fin) (hp : (C.loc p).pc.isVal = false) :
    ∃ o, p ≠ o ∧ (C.loc o).pc.isVal ∧ (C.loc o).j = x := by
  obtain ⟨o, h1, h2, -⟩ := hI.own2 x v t hx ht
  refine ⟨o, ?_, h1, h2⟩
  rintro rfl; rw [hp] at h1; cases h1

lemma pot_fsLL (hpc : (C.loc p).pc = .fsLL) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).i (.ll p) (fun r => fsBody h { (C.loc p) with val := r.1 }) := by
    simp only [act, hpc]
  have hso := scanOut_fsBody h { (C.loc p) with val := C.val (C.loc p).i }
  refine pot_LL hs hact (fun hd => by have := dep_of_scanOut hso (by exact hd); exact this) ?_ ?_
  · exact budL_scan hso.1 hso.2.1 (ni_fsBody _) (by simp [hpc, PC.isVal]) (by simp [hpc])
      (by simp [hpc]) _ _
  · have := loc_fsBody (h := h) { (C.loc p) with val := C.val (C.loc p).i }
    have e : locC h C p = potF h (C.loc p).op.key (C.loc p).i + 7 := by simp [locC, locL, hpc]
    simp only at this ⊢; omega

lemma pot_bsLL (hpc : (C.loc p).pc = .bsLL) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).i (.ll p) (fun r => bsBody h { (C.loc p) with val := r.1 }) := by
    simp only [act, hpc]
  have hso := scanOut_bsBody h { (C.loc p) with val := C.val (C.loc p).i }
  refine pot_LL hs hact (fun hd => by have := dep_of_scanOut hso (by exact hd); exact this) ?_ ?_
  · exact budL_scan hso.1 hso.2.1 (ni_bsBody _) (by simp [hpc, PC.isVal]) (by simp [hpc])
      (by simp [hpc]) _ _
  · have := loc_bsBody (h := h) { (C.loc p) with val := C.val (C.loc p).i }
    have e : locC h C p = potB h (C.loc p).op.key (C.loc p).i + 7 := by simp [locC, locL, hpc]
    simp only at this ⊢; omega

lemma pot_tdLL (hpc : (C.loc p).pc = .tdLL) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).i (.ll p) (fun r => tdBody h { (C.loc p) with val := r.1 }) := by
    simp only [act, hpc]
  have hso := scanOut_tdBody h { (C.loc p) with val := C.val (C.loc p).i }
  refine pot_LL hs hact (fun hd => by have := dep_of_scanOut hso (by exact hd); exact this) ?_ ?_
  · exact budL_scan hso.1 hso.2.1 (ni_tdBody _) (by simp [hpc, PC.isVal]) (by simp [hpc])
      (by simp [hpc]) _ _
  · have := loc_tdBody (h := h) { (C.loc p) with val := C.val (C.loc p).i }
    have e : locC h C p = baseL (h := h) (C.loc p) + 5 := by simp [locC, locL, hpc, baseL]
    simp only [baseL] at this e ⊢; omega

lemma pot_vcRD (hpc : (C.loc p).pc = .vcRD) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).i (.vl p) (fun r =>
      vcRet h { (C.loc p) with val := r.1 } (r.1.key? = some (C.loc p).op.key)) := by
    simp only [act, hpc]
  have hso := scanOut0_vcRet h { (C.loc p) with val := C.val (C.loc p).i } (decide ((C.val (C.loc p).i).key? = some (C.loc p).op.key))
  refine pot_VL hs hact (dep_of_scanOut0 hso) ?_ ?_
  · exact budL_scan hso.1 hso.2.1 (ni_vcRet _ _) (by simp [hpc, PC.isVal]) (by simp [hpc])
      (by simp [hpc]) _ _
  · have := loc_vcRet (h := h) { (C.loc p) with val := C.val (C.loc p).i } (decide ((C.val (C.loc p).i).key? = some (C.loc p).op.key))
    have e : locC h C p = baseL (h := h) (C.loc p) + 5 := by simp [locC, locL, hpc, baseL]
    simp only [baseL] at this e ⊢; omega

lemma pot_iLL (hpc : (C.loc p).pc = .iLL) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).j (.ll p) (fun r => iBody h { (C.loc p) with val := r.1 }) := by
    simp only [act, hpc]
  have hnd : (iBody h { (C.loc p) with val := C.val (C.loc p).j }).pc.dep = false := by
    unfold iBody iNext; split_ifs <;> simp [PC.dep, retL]
  have hnv : (iBody h { (C.loc p) with val := C.val (C.loc p).j }).pc.isVal = false := by
    unfold iBody iNext; split_ifs <;> simp [PC.isVal, retL]
  have hop : (iBody h { (C.loc p) with val := C.val (C.loc p).j }).op = (C.loc p).op := by
    unfold iBody iNext; split_ifs <;> simp [retL]
  refine pot_LL hs hact (fun h1 => by rw [hnd] at h1; cases h1) ?_ ?_
  · exact budL_scan hop hnv (ni_iBody _) (by simp [hpc, PC.isVal]) (by simp [hpc])
      (by simp [hpc]) _ _
  · have := loc_iBody (h := h) { (C.loc p) with val := C.val (C.loc p).j }
    have e : locC h C p = potS h (C.loc p).op.key (C.loc p).j + 2 := by simp [locC, locL, hpc]
    simp only at this ⊢; omega

lemma pot_vcSC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .vcSC)
    (hs : (impl h).step C (.tau p) = some C') : pot h C' < pot h C := by
  have hl0 : (C.loc p).val = .key (C.loc p).op.key .tent := by have := hI.loc p; simp only [LocInv, hpc] at this; exact this
  have hact : act h p (C.loc p) = .access (C.loc p).i (.sc p (.key (C.loc p).op.key .reval)) (fun r =>
      if r.2 then vcRet h (C.loc p) true else { (C.loc p) with pc := .vcRD }) := by
    simp only [act, hpc]
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · have hx : C.val (C.loc p).i = .key (C.loc p).op.key .tent :=
      (hI.link p (C.loc p).i (C.loc p).val (by simp [recorded, hpc]) hsc).trans hl0
    obtain ⟨o, hpo, ho, hox⟩ := exists_owner hI hx (by simp) hnv
    refine pot_SCsucc hs hact hsc (budget_lt_owner hI hpo ho hox ?_)
    simp only [ite_true]
    have e1 : budL (vcRet h (C.loc p) true) (if (vcRet h (C.loc p) true).j = (C.loc p).i then .key (C.loc p).op.key .reval
        else C.val (vcRet h (C.loc p) true).j) = 0 := by simp [budL, vcRet_true_ret]
    have eo : bud C o = 1 + credit (C.val (C.loc p).i) := by simp only [bud, budL_isVal ho, hox]
    have ep : bud C p = 3 := by simp [bud, budL, hpc]
    rw [e1, budL_isVal ho, eo, ep, hx]; simp
  · refine pot_SCfail hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1) (by simp [PC.dep])
      (by simp [budL, bud, hpc]) ?_
    simp [locL, hpc]

lemma pot_tdSCF (hI : Inv h N ts C) (hpc : (C.loc p).pc = .tdSCF)
    (hs : (impl h).step C (.tau p) = some C') : pot h C' < pot h C := by
  have hl0 : (C.loc p).val = .key (C.loc p).op.key .fin := by have := hI.loc p; simp only [LocInv, hpc] at this; exact this
  have hact : act h p (C.loc p) = .access (C.loc p).i (.sc p .tomb) (fun r =>
      tdRet h (C.loc p) (if r.2 then .tt else .ff)) := by
    simp only [act, hpc]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · have hx : C.val (C.loc p).i = .key (C.loc p).op.key .fin :=
      (hI.link p (C.loc p).i (C.loc p).val (by simp [recorded, hpc]) hsc).trans hl0
    refine pot_SCsucc hs hact hsc (budget_lt_noOwner (fun q _ h1 =>
      not_owner_of_fin hI hx h1.1 h1.2) ?_)
    simp [budL, bud, hpc, tdRet_tt_ret]
  · have hso := scanOut0_tdRet h (C.loc p) .ff
    refine pot_SCfail hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1) (dep_of_scanOut0 hso)
      (budL_scan hso.1 hso.2.1 (ni_tdRet _ _) (by simp [hpc, PC.isVal]) (by simp [hpc])
        (by simp [hpc]) _ _) ?_
    have := loc_tdRet (h := h) (C.loc p) .ff
    simp only [Bool.false_eq_true, ite_false]
    have e : locL h (C.loc p) false = baseL (h := h) (C.loc p) + 4 := by simp [locL, hpc, baseL]
    omega

lemma pot_tdSCD (hI : Inv h N ts C) (hpc : (C.loc p).pc = .tdSCD)
    (hs : (impl h).step C (.tau p) = some C') : pot h C' < pot h C := by
  have hl0 : (C.loc p).val.key? = some (C.loc p).op.key ∧ (C.loc p).val ≠ .key (C.loc p).op.key .fin := by
    have := hI.loc p; simp only [LocInv, hpc] at this; exact this
  have hact : act h p (C.loc p) = .access (C.loc p).i (.sc p .deleted) (fun r =>
      if r.2 then tdRet h (C.loc p) .tt else { (C.loc p) with pc := .tdLL }) := by
    simp only [act, hpc]
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · have hx : C.val (C.loc p).i = (C.loc p).val := hI.link p (C.loc p).i (C.loc p).val (by simp [recorded, hpc]) hsc
    obtain ⟨t, ht, hxt⟩ : ∃ t, t ≠ .fin ∧ C.val (C.loc p).i = .key (C.loc p).op.key t := by
      rcases hv : (C.loc p).val with _ | _ | _ | _ | ⟨w, t⟩ <;> rw [hv] at hl0 <;> simp [Cell.key?] at hl0
      obtain ⟨rfl, h2⟩ := hl0
      exact ⟨t, fun e => h2 rfl e, by rw [hx, hv]⟩
    obtain ⟨o, hpo, ho, hox⟩ := exists_owner hI hxt ht hnv
    refine pot_SCsucc hs hact hsc (budget_lt_owner hI hpo ho hox ?_)
    simp only [ite_true]
    have e1 : budL (tdRet h (C.loc p) .tt) (if (tdRet h (C.loc p) .tt).j = (C.loc p).i then .deleted
        else C.val (tdRet h (C.loc p) .tt).j) = 0 := by simp [budL, tdRet_tt_ret]
    have eo : bud C o = 1 + credit (C.val (C.loc p).i) := by simp only [bud, budL_isVal ho, hox]
    have ep : bud C p = 3 := by simp [bud, budL, hpc]
    rw [e1, budL_isVal ho, eo, ep, hxt]
    cases t
    · simp [credit]
    · exact absurd rfl ht
    · simp [credit]
  · refine pot_SCfail hs hact hsc (fun _ => by simp [target, hpc]) (by simp [PC.dep])
      (by simp [budL, bud, hpc]) ?_
    simp [locL, hpc]

lemma pot_iSC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .iSC)
    (hs : (impl h).step C (.tau p) = some C') : pot h C' < pot h C := by
  have hl0 : (C.loc p).val = .empty ∨ (C.loc p).val = .tomb := by
    have := hI.loc p; simp only [LocInv, hpc] at this; exact this
  have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p (.key (C.loc p).op.key .tent)) (fun r =>
      if r.2 then ds48 h (C.loc p) else iNext h (C.loc p)) := by
    simp only [act, hpc]
  by_cases hsc : p ∈ C.lks (C.loc p).j
  · have hx : C.val (C.loc p).j = (C.loc p).val := hI.link p (C.loc p).j (C.loc p).val (by simp [recorded, hpc]) hsc
    refine pot_SCsucc hs hact hsc (budget_lt_noOwner (fun q _ h1 =>
      ne_owner_cell hI h1.1 (by rw [hx]; exact hl0) h1.2) ?_)
    simp [budL, bud, hpc, PC.isVal, credit]
  · have hnd : (iNext h (C.loc p)).pc.dep = false := by unfold iNext; split_ifs <;> simp [PC.dep, retL]
    have hnv : (iNext h (C.loc p)).pc.isVal = false := by unfold iNext; split_ifs <;> simp [PC.isVal, retL]
    have hop : (iNext h (C.loc p)).op = (C.loc p).op := by unfold iNext; split_ifs <;> simp [retL]
    refine pot_SCfail hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1) (by simpa using hnd)
      ?_ ?_
    · have := budL_scan hop hnv (ni_iNext _) (by simp [hpc, PC.isVal]) (by simp [hpc])
        (by simp [hpc]) (C.val (iNext h (C.loc p)).j) (C.val (C.loc p).j)
      simpa using this
    have := loc_iNext (h := h) (C.loc p)
    simp only [Bool.false_eq_true, ite_false]
    have e : locL h (C.loc p) false = potS h (C.loc p).op.key (C.loc p).j + 1 := by simp [locL, hpc]
    omega

end Podc.LockFreeLinearProbing
