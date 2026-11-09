import Papers.PODC2026.LockFreeLinearProbing.StepWrite

/-!
# The invariant `Inv` is preserved: the `SC`s of owners on their own cell
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

/-- Lines 58, 69, 78: rewriting the own cell with `⟨v, tentative⟩`. -/
lemma tau_reTent (hI : Inv h N ts C) (hpc : (C.loc p).pc = .l58SC ∨ (C.loc p).pc = .l69SC ∨
      (C.loc p).pc = .dcSC78)
    (hs : (impl h).step C (.tau p) = some C') : ∃ ts', Inv h (N + 1) ts' C' := by
  have hv : (C.loc p).pc.isVal := by rcases hpc with h1 | h1 | h1 <;> simp [h1, PC.isVal]
  rcases hpc with hpc | hpc | hpc <;>
  · simp [Impl.step, impl, act, hpc] at hs
    obtain ⟨hp, rfl⟩ := hs
    by_cases hsc : p ∈ C.lks (C.loc p).j
    · simp only [Cfg.lks] at hsc
      simp only [hsc, ite_true]
      exact ⟨_, inv_tentWrite hI hp (Or.inr hv)⟩
    · simp only [Cfg.lks] at hsc
      simp only [hsc, ite_false]
      exact ⟨ts, inv_val_fail hI hp hv rfl rfl (by simp)⟩

lemma tau_l67SC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .l67SC)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  have hl := hI.loc p; simp only [LocInv, hpc] at hl
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  by_cases hsc : p ∈ C.lks (C.loc p).j
  · have hx : C.val (C.loc p).j = .key (C.loc p).op.key .tent :=
      (hI.link p _ _ (by simp [recorded, hpc]) hsc).trans hl
    simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true]
    exact inv_leave hI hp hv (by simp [retL, PC.isVal]) (by simp [retL, PC.isIns])
      (by simp [retL, LocInv]) (by simp [retL, recorded]) (by simp) (by simp) (by simp)
      (fun v hw => by simp only [Cell.key.injEq] at hw; exact ⟨hw.1.symm, hx, hpc⟩)
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    exact inv_val_fail hI hp hv rfl rfl (by simp)

lemma tau_dcSC80 (hI : Inv h N ts C) (hpc : (C.loc p).pc = .dcSC80)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  have hv : (C.loc p).pc.isVal := by simp [hpc, PC.isVal]
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  by_cases hsc : p ∈ C.lks (C.loc p).j
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true]
    exact inv_leave hI hp hv (by simp [retL, PC.isVal]) (by simp [retL, PC.isIns])
      (by simp [retL, LocInv]) (by simp [retL, recorded]) (by simp) (by simp) (by simp)
      (by simp)
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    exact inv_val_fail hI hp hv rfl rfl (by simp)

end Podc.LockFreeLinearProbing

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

/-- A step of a non-owner that changes no cell value and stays a non-owner. -/
lemma inv_unch_nv (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {c' : Cell K × List P}
    {l' : Loc K m} (hu : c'.1 = C.val x) (hlk : ∀ q, q ≠ p → (q ∈ c'.2 ↔ q ∈ C.lks x))
    (hshape : LinkShape C p x c') (hop : l'.op = (C.loc p).op)
    (hnv : (C.loc p).pc.isVal = false) (hnv' : l'.pc.isVal = false) (hloc : LocInv l')
    (hlink : ∀ y w, recorded l' = some (y, w) → p ∈ (upd C p l' x c').lks y →
      (upd C p l' x c').val y = w)
    (hp3 : l'.pc.isIns → ∀ c, dist h l'.op.key c < dist h l'.op.key l'.j → C.val c ≠ .empty)
    (hisc : l'.pc = .iSC → C.val l'.j = .empty → p ∈ (upd C p l' x c').lks l'.j) :
    Inv h (N + 1) ts (upd C p l' x c') := by
  have hnd : ¬ (((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2) := by
    rintro (⟨h1 | h1, -⟩ | h1) <;> simp [h1, PC.isVal] at hnv'
  refine inv_of_unchanged hI hp ⟨hu, hlk, hop, by rw [hnv, hnv'], fun h1 => by simp [hnv'] at h1⟩
    hloc hshape hlink ?_ ?_ ?_ ?_ ?_ hisc
  · rintro (h1 | h1)
    · exact hp3 h1
    · simp [hnv'] at h1
  · intro J _ _ h1; simp [hnv'] at h1
  · intro J hd; exact absurd hd hnd
  · intro hd; exact absurd hd hnd
  · intro h1; simp [hnv'] at h1

lemma iNext_cases (l : Loc K m) :
    (l.j + 1 = h l.op.key ∧ iNext h l = retL l .abort) ∨
    (l.j + 1 ≠ h l.op.key ∧ iNext h l = { l with j := l.j + 1, pc := .iLL }) := by
  unfold iNext; split_ifs with h1
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨h1, rfl⟩

/-- `p3'` for the next cell of the free-cell search. -/
lemma p3_next (hI : Inv h N ts C) (hpi : (C.loc p).pc.isIns) (hj : (C.loc p).j + 1 ≠ h (C.loc p).op.key)
    (hne : C.val (C.loc p).j ≠ .empty) :
    ∀ c, dist h (C.loc p).op.key c < dist h (C.loc p).op.key ((C.loc p).j + 1) → C.val c ≠ .empty := by
  intro c hc
  rw [dist_succ h _ _ hj] at hc
  rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
  · exact hI.p3' p (Or.inl hpi) c hc
  · rw [dist_inj h _ hc]; exact hne

lemma step_tau_access (hs : (impl h).step C (.tau p) = some C') {x : Fin m}
    {o : LLOp (Cell K) P} {k : (Cell K × Bool) → Loc K m}
    (hact : act h p (C.loc p) = .access x o k) :
    C.pend p ≠ none ∧ C' = upd C p (k ((llscObj (Cell K) P .empty).δ (C.mem x) o).2) x
      ((llscObj (Cell K) P .empty).δ (C.mem x) o).1 := by
  obtain ⟨hp, -, x', o', k', hact', h1, h2⟩ := Impl.step_tau hs
  simp only [impl] at hact'
  rw [hact] at hact'
  cases hact'
  refine ⟨hp, ?_⟩
  cases C'; simp only [upd] at h1 h2 ⊢; subst h1 h2
  have := Impl.step_tau hs
  simp_all

lemma iBody_cases (l : Loc K m) :
    ((l.val = .empty ∨ l.val = .tomb) ∧ iBody h l = { l with pc := .iSC }) ∨
    (¬(l.val = .empty ∨ l.val = .tomb) ∧ iBody h l = iNext h l) := by
  unfold iBody; split_ifs with h1
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨h1, rfl⟩

lemma tau_iLL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .iLL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  have hact : act h p (C.loc p) = .access (C.loc p).j (.ll p)
      (fun r => iBody h { C.loc p with val := r.1 }) := by
    simp only [act, hpc]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  simp only [llscObj.δ_ll]
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  have hpi : (C.loc p).pc.isIns := by simp [hpc, PC.isIns]
  rcases iBody_cases (h := h) { C.loc p with val := (C.mem (C.loc p).j).1 } with
    ⟨h1, he⟩ | ⟨h1, he⟩ <;> rw [he]
  · refine inv_unch_nv hI hp rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl)) rfl hnv
      (by simp [PC.isVal]) (by simpa [LocInv, Cfg.val] using h1) ?_ ?_ ?_
    · intro y w hr _; simp [recorded] at hr; obtain ⟨rfl, rfl⟩ := hr; simp [Cfg.val]
    · intro _ c hc; exact hI.p3' p (Or.inl hpi) c hc
    · intro _ _; simp [Cfg.lks, mem_addLink_self]
  · have hne : C.val (C.loc p).j ≠ .empty := fun h2 => h1 (Or.inl h2)
    rcases iNext_cases (h := h) { C.loc p with val := (C.mem (C.loc p).j).1 } with
      ⟨hj, he⟩ | ⟨hj, he⟩ <;> rw [he]
    · exact inv_unch_nv hI hp rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl)) rfl hnv
        (by simp [retL, PC.isVal]) (by simp [retL, LocInv]) (by simp [retL, recorded])
        (by simp [retL, PC.isIns]) (by simp [retL])
    · exact inv_unch_nv hI hp rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl)) rfl hnv
        (by simp [PC.isVal]) (by simp [LocInv]) (by simp [recorded])
        (fun _ => p3_next hI hpi hj hne) (by simp)

lemma tau_iSC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .iSC)
    (hs : (impl h).step C (.tau p) = some C') : ∃ ts', Inv h (N + 1) ts' C' := by
  have hl := hI.loc p; simp only [LocInv, hpc] at hl
  have hact : act h p (C.loc p) = .access (C.loc p).j (.sc p (.key (C.loc p).op.key .tent))
      (fun r => if r.2 then ds48 h (C.loc p) else iNext h (C.loc p)) := by
    simp only [act, hpc]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  simp only [llscObj.δ_sc]
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  have hpi : (C.loc p).pc.isIns := by simp [hpc, PC.isIns]
  by_cases hsc : p ∈ C.lks (C.loc p).j
  · have hx := hI.link p (C.loc p).j (C.loc p).val (by simp [recorded, hpc]) hsc
    simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true]
    exact ⟨_, inv_tentWrite hI hp (Or.inl ⟨hpi, by rw [hx]; exact hl⟩)⟩
  · have hne : C.val (C.loc p).j ≠ .empty := fun h2 => hsc (hI.isc p hpc h2)
    simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    refine ⟨ts, ?_⟩
    rcases iNext_cases (h := h) (C.loc p) with ⟨hj, he⟩ | ⟨hj, he⟩ <;> rw [he]
    · exact inv_unch_nv hI hp rfl (fun _ _ => Iff.rfl) (Or.inl rfl) rfl hnv
        (by simp [retL, PC.isVal]) (by simp [retL, LocInv]) (by simp [retL, recorded])
        (by simp [retL, PC.isIns]) (by simp [retL])
    · exact inv_unch_nv hI hp rfl (fun _ _ => Iff.rfl) (Or.inl rfl) rfl hnv
        (by simp [PC.isVal]) (by simp [LocInv]) (by simp [recorded])
        (fun _ => p3_next hI hpi hj hne) (by simp)

end Podc.LockFreeLinearProbing
