import Papers.PODC2026.LockFreeLinearProbing.LockFreeScan
import Papers.PODC2026.LockFreeLinearProbing.StepDup

/-!
# Lock-freedom: the steps of owners
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] [Fintype P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

lemma budL_own {l l' : Loc K m} (hv' : l'.pc.isVal) (hv : l.pc.isVal) (hj : l'.j = l.j)
    (c : Fin m → Cell K) : budL l' (c l'.j) ≤ budL l (c l.j) := by
  rw [budL_isVal hv', budL_isVal hv, hj]

lemma noOwner_own (hI : Inv h N ts C) (hv : (C.loc p).pc.isVal) :
    ∀ q, q ≠ p → ¬ ((C.loc q).pc.isVal ∧ (C.loc q).j = (C.loc p).j) := by
  rintro q hq ⟨h1, h2⟩; exact hq (hI.own_inj q p h1 hv h2)

lemma dsBody_props (l : Loc K m) :
    (dsBody h l).pc.isVal ∧ (dsBody h l).j = l.j ∧ (dsBody h l).pc.dep = false := by
  rcases dsBody_cases (h := h) l with ⟨-, he⟩ | ⟨-, -, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, he⟩ <;>
    rw [he]
  · simp [PC.isVal, PC.dep]
  · simp [PC.isVal, PC.dep]
  · simp [PC.isVal, PC.dep]
  · rcases dsNext_cases (h := h) l with ⟨-, he'⟩ | ⟨-, he'⟩ <;> rw [he'] <;> simp [PC.isVal, PC.dep]

lemma docRet_props (l : Loc K m) (b : Bool) :
    (docRet h l b).pc.isVal ∧ (docRet h l b).j = l.j ∧ (docRet h l b).pc.dep = false := by
  unfold docRet; split_ifs
  · rcases dsNext_cases (h := h) l with ⟨-, he'⟩ | ⟨-, he'⟩ <;> rw [he'] <;> simp [PC.isVal, PC.dep]
  · simp [PC.isVal, PC.dep]

lemma locC_eq {l : Loc K m} (hd : l.pc.dep = false) (hl : C.loc p = l) :
    locC h C p = locL h l true := by
  unfold locC; rw [hl, locL_vld hd]

lemma pot_dsLL (hpc : (C.loc p).pc = .dsLL) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).i (.ll p)
      (fun r => dsBody h { C.loc p with val := r.1 }) := by simp only [act, hpc]
  obtain ⟨a, b, c⟩ := dsBody_props (h := h) { C.loc p with val := C.val (C.loc p).i }
  refine pot_LL hs hact (fun hd => by rw [c] at hd; cases hd)
    (budL_own a (by simp [hpc, PC.isVal]) b _) ?_
  have := loc_dsBody (h := h) { C.loc p with val := C.val (C.loc p).i }
  have e : locL h (C.loc p) true = potD h (C.loc p).op.key (C.loc p).i + 15 := by simp [locL, hpc]
  rw [locC_eq (by simp [hpc, PC.dep]) rfl, e]
  exact Nat.lt_of_le_of_lt this (by simp)

lemma pot_docRD (hpc : (C.loc p).pc = .docRD) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).j (.vl p) (fun r =>
      if r.1 = .key (C.loc p).op.key .tent then { C.loc p with cur := r.1, pc := .docSC }
      else docRet h { C.loc p with cur := r.1 } false) := by simp only [act, hpc]
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  have hD := potD_ge (h := h) (C.loc p).op.key (C.loc p).i
  have e : locC h C p = potD h (C.loc p).op.key (C.loc p).i + 14 := by
    rw [locC_eq (by simp [hpc, PC.dep]) rfl]; simp [locL, hpc]
  by_cases ht : C.val (C.loc p).j = .key (C.loc p).op.key .tent
  · refine pot_VL' hs hact { C.loc p with cur := C.val (C.loc p).j, pc := .docSC }
      (by simp [ht]) (by simp [PC.dep]) (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) ?_
    rw [e]; simp [locL]
  · refine pot_VL' hs hact { C.loc p with cur := C.val (C.loc p).j, pc := .l57LL }
      (by simp [ht, docRet]) (by simp [PC.dep]) (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) ?_
    rw [e]; simp only [locL]; omega

lemma pot_docSC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .docSC)
    (hs : (impl h).step C (.tau p) = some C') : pot h C' < pot h C := by
  have hl0 : (C.loc p).val = .key (C.loc p).op.key .tent ∧ (C.loc p).i ≠ (C.loc p).j := by
    have := hI.loc p; simp only [LocInv, hpc] at this; exact this
  have hact : act h p (C.loc p) = .access (C.loc p).i (.sc p .collided) (fun r =>
      if r.2 then docRet h (C.loc p) true else { C.loc p with pc := .docRD2 }) := by
    simp only [act, hpc]
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · have hx : C.val (C.loc p).i = .key (C.loc p).op.key .tent :=
      (hI.link p (C.loc p).i (C.loc p).val (by simp [recorded, hpc]) hsc).trans hl0.1
    obtain ⟨o, h1, h2, -⟩ := hI.own2 _ _ _ hx (by simp)
    have hpo : p ≠ o := by rintro rfl; exact hl0.2 h2.symm
    refine pot_SCsucc hs hact hsc (budget_lt_owner hI hpo h1 h2 ?_)
    obtain ⟨a, b, -⟩ := docRet_props (h := h) (C.loc p) true
    simp only [ite_true]
    rw [b, if_neg (Ne.symm hl0.2), budL_isVal a, budL_isVal h1]
    have eo : bud C o = 1 + credit (C.val (C.loc p).i) := by simp only [bud, budL_isVal h1, h2]
    have ep : bud C p = 1 + credit (C.val (C.loc p).j) := by simp only [bud, budL_isVal hv]
    rw [eo, ep, hx]; simp [credit]
  · refine pot_SCfail' hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1)
      { C.loc p with pc := .docRD2 } (by simp) (by simp [PC.dep])
      (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) ?_
    simp [locL, hpc]

lemma pot_docRD2 (hpc : (C.loc p).pc = .docRD2) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  have hact : act h p (C.loc p) = .access (C.loc p).i (.vl p) (fun r =>
      docRet h (C.loc p) (decide (r.1 ≠ .key (C.loc p).op.key .fin))) := by simp only [act, hpc]
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  obtain ⟨a, b, c⟩ := docRet_props (h := h) (C.loc p)
    (decide (C.val (C.loc p).i ≠ .key (C.loc p).op.key .fin))
  refine pot_VL hs hact c (budL_own a hv b _) ?_
  have := loc_docRet (h := h) (C.loc p) (decide (C.val (C.loc p).i ≠ .key (C.loc p).op.key .fin))
  have e : locL h (C.loc p) true = potD h (C.loc p).op.key (C.loc p).i + 12 := by simp [locL, hpc]
  rw [locC_eq (by simp [hpc, PC.dep]) rfl, e]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le this) (by omega)

/-- Steps of owners with constant local potentials (lines 57–80). -/
lemma pot_tail (hI : Inv h N ts C) (hs : (impl h).step C (.tau p) = some C')
    (hpc : (C.loc p).pc = .l57LL ∨ (C.loc p).pc = .l58SC ∨ (C.loc p).pc = .l66LL ∨
      (C.loc p).pc = .l67SC ∨ (C.loc p).pc = .l69SC ∨ (C.loc p).pc = .dcLL76 ∨
      (C.loc p).pc = .dcSC78 ∨ (C.loc p).pc = .dcLL79 ∨ (C.loc p).pc = .dcSC80) :
    pot h C' < pot h C := by
  have hv : (C.loc p).pc.isVal := by
    rcases hpc with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp [h1, PC.isVal]
  have hno := noOwner_own hI hv
  have hl := hI.loc p
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc
  · -- line 57
    have hact : act h p (C.loc p) = .access (C.loc p).j (.ll p) (fun r =>
        if r.1 = .key (C.loc p).op.key .reval then { C.loc p with cur := r.1, pc := .l58SC }
        else { C.loc p with cur := r.1, pc := .dcLL76 }) := by simp only [act, hpc]
    refine pot_LL hs hact ?_ ?_ ?_ <;> simp only <;> split_ifs <;>
      simp [PC.dep, budL, bud, hpc, locC, locL, budL_isVal hv]
  · -- line 58
    simp only [LocInv, hpc] at hl
    have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p (.key (C.loc p).op.key .tent))
        (fun r => if r.2 then ds48 h (C.loc p) else { C.loc p with pc := .dcLL76 }) := by
      simp only [act, hpc]
    by_cases hsc : p ∈ C.lks (C.loc p).j
    · have hx := (hI.link p (C.loc p).j (C.loc p).cur (by simp [recorded, hpc]) hsc).trans hl
      refine pot_SCsucc hs hact hsc (budget_lt_noOwner hno ?_)
      simp [budL, bud, hpc, hx, PC.isVal, credit]
    · refine pot_SCfail' hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1)
        { C.loc p with pc := .dcLL76 } (by simp) (by simp [PC.dep])
        (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) (by simp [locL, hpc])
  · -- line 66
    have hact : act h p (C.loc p) = .access (C.loc p).j (.ll p) (fun r =>
        if r.1 = .key (C.loc p).op.key .tent then { C.loc p with cur := r.1, pc := .l67SC }
        else if r.1 = .key (C.loc p).op.key .reval then { C.loc p with cur := r.1, pc := .l69SC }
        else { C.loc p with cur := r.1, pc := .dcLL76 }) := by simp only [act, hpc]
    refine pot_LL hs hact ?_ ?_ ?_ <;> simp only <;> split_ifs <;>
      simp [PC.dep, budL, bud, hpc, locC, locL, budL_isVal hv]
  · -- line 67
    simp only [LocInv, hpc] at hl
    have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p (.key (C.loc p).op.key .fin))
        (fun r => if r.2 then retL (C.loc p) (.ok true) else { C.loc p with pc := .dcLL76 }) := by
      simp only [act, hpc]
    by_cases hsc : p ∈ C.lks (C.loc p).j
    · have hx := (hI.link p (C.loc p).j (C.loc p).cur (by simp [recorded, hpc]) hsc).trans hl
      refine pot_SCsucc hs hact hsc (budget_lt_noOwner hno ?_)
      simp [budL, bud, hpc, hx, retL, PC.isVal, credit]
    · refine pot_SCfail' hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1)
        { C.loc p with pc := .dcLL76 } (by simp) (by simp [PC.dep])
        (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) (by simp [locL, hpc])
  · -- line 69
    simp only [LocInv, hpc] at hl
    have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p (.key (C.loc p).op.key .tent))
        (fun r => if r.2 then ds48 h (C.loc p) else { C.loc p with pc := .dcLL76 }) := by
      simp only [act, hpc]
    by_cases hsc : p ∈ C.lks (C.loc p).j
    · have hx := (hI.link p (C.loc p).j (C.loc p).cur (by simp [recorded, hpc]) hsc).trans hl
      refine pot_SCsucc hs hact hsc (budget_lt_noOwner hno ?_)
      simp [budL, bud, hpc, hx, PC.isVal, credit]
    · refine pot_SCfail' hs hact hsc (fun h1 => by simp [hpc, PC.dep] at h1)
        { C.loc p with pc := .dcLL76 } (by simp) (by simp [PC.dep])
        (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) (by simp [locL, hpc])
  · -- line 76
    have hact : act h p (C.loc p) = .access (C.loc p).j (.ll p) (fun r =>
        if r.1 = .key (C.loc p).op.key .reval then { C.loc p with val := r.1, pc := .dcSC78 }
        else { C.loc p with val := r.1, pc := .dcSC80 }) := by simp only [act, hpc]
    refine pot_LL hs hact ?_ ?_ ?_ <;> simp only <;> split_ifs <;>
      simp [PC.dep, target, budL, bud, hpc, locC, locL, budL_isVal hv]
  · -- line 78
    simp only [LocInv, hpc] at hl
    have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p (.key (C.loc p).op.key .tent))
        (fun r => if r.2 then ds48 h (C.loc p) else { C.loc p with pc := .dcLL79 }) := by
      simp only [act, hpc]
    by_cases hsc : p ∈ C.lks (C.loc p).j
    · have hx := (hI.link p (C.loc p).j (C.loc p).val (by simp [recorded, hpc]) hsc).trans hl
      refine pot_SCsucc hs hact hsc (budget_lt_noOwner hno ?_)
      simp [budL, bud, hpc, hx, PC.isVal, credit]
    · refine pot_SCfail' hs hact hsc (fun _ => by simp [target, hpc])
        { C.loc p with pc := .dcLL79 } (by simp) (by simp [PC.dep])
        (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) (by simp [locL, hpc])
  · -- line 79
    have hact : act h p (C.loc p) = .access (C.loc p).j (.ll p) (fun r =>
        { C.loc p with val := r.1, pc := .dcSC80 }) := by simp only [act, hpc]
    refine pot_LL hs hact ?_ ?_ ?_ <;>
      simp [PC.dep, target, budL, bud, hpc, locC, locL, budL_isVal hv]
  · -- line 80
    have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p .tomb)
        (fun r => if r.2 then retL (C.loc p) (.ok (decide ((C.loc p).val = .deleted)))
          else { C.loc p with pc := .dcLL76 }) := by
      simp only [act, hpc]
    by_cases hsc : p ∈ C.lks (C.loc p).j
    · refine pot_SCsucc hs hact hsc (budget_lt_noOwner hno ?_)
      simp [budL, bud, hpc, retL, PC.isVal]
    · refine pot_SCfail' hs hact hsc (fun _ => by simp [target, hpc])
        { C.loc p with pc := .dcLL76 } (by simp) (by simp [PC.dep])
        (budL_own (by simp [PC.isVal]) hv (by rfl) C.val) (by simp [locL, hpc])

end Podc.LockFreeLinearProbing
