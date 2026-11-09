import Papers.PODC2026.LockFreeLinearProbing.Frame

/-!
# The invariant `Inv` is preserved: generic step shapes

`LL` steps and unchanged steps of non-owners, and the free-cell search.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C : Cfg K m P} {p : P}

lemma mem_addLink_iff {L : List P} {q : P} (hq : q ≠ p) :
    q ∈ (if p ∈ L then L else p :: L) ↔ q ∈ L := by
  split_ifs <;> simp [hq]

lemma mem_addLink_self (L : List P) : p ∈ (if p ∈ L then L else p :: L) := by
  split_ifs with h1
  · exact h1
  · exact List.mem_cons_self

/-- An `LL` of cell `x` by a process that is not an owner and does not become one. -/
lemma inv_LL_nonval (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {l' : Loc K m}
    (hnv : (C.loc p).pc.isVal = false) (hop : l'.op = (C.loc p).op)
    (hnv' : l'.pc.isVal = false) (hins : l'.pc.isIns = true → l'.j = h l'.op.key)
    (hloc : LocInv l') (hrec : recorded l' = none ∨ recorded l' = some (x, C.val x))
    (hnisc : l'.pc ≠ .iSC) :
    Inv h (N + 1) ts (upd C p l' x (C.val x, if p ∈ C.lks x then C.lks x else p :: C.lks x)) := by
  refine inv_of_unchanged_nonval hI hp ⟨rfl, fun q hq => mem_addLink_iff hq, hop,
    by rw [hnv, hnv'], fun h1 => by simp [hnv'] at h1⟩ hloc (Or.inr (Or.inl rfl)) ?_ hnv' hins
    (fun h1 => absurd h1 hnisc)
  intro y w hr _
  rcases hrec with hrec | hrec <;> rw [hrec] at hr
  · cases hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; simp

/-- A step of a non-owner that changes neither the memory nor its recorded value. -/
lemma inv_stay_nonval (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {l' : Loc K m}
    (hnv : (C.loc p).pc.isVal = false) (hop : l'.op = (C.loc p).op)
    (hnv' : l'.pc.isVal = false) (hins : l'.pc.isIns = true → l'.j = h l'.op.key)
    (hloc : LocInv l') (hrec : recorded l' = none) (hnisc : l'.pc ≠ .iSC) :
    Inv h (N + 1) ts (upd C p l' x (C.val x, C.lks x)) := by
  refine inv_of_unchanged_nonval hI hp ⟨rfl, fun q _ => Iff.rfl, hop,
    by rw [hnv, hnv'], fun h1 => by simp [hnv'] at h1⟩ hloc (Or.inl rfl) ?_ hnv' hins
    (fun h1 => absurd h1 hnisc)
  intro y w hr _; rw [hrec] at hr; cases hr

lemma ScanOut.nisc {l l' : Loc K m} (hs : ScanOut h l l') : l'.pc ≠ .iSC := by
  intro h1; have := (hs.2.2.1 (by simp [h1, PC.isIns])).1; rw [h1] at this; cases this

lemma ScanOut0.nisc {l l' : Loc K m} (hs : ScanOut0 h l l') : l'.pc ≠ .iSC := by
  intro h1; have := (hs.2.2.1 (by simp [h1, PC.isIns])).1; rw [h1] at this; cases this

/-- An `LL` step of a scanning operation (lines 2, 11, 16, 89). -/
lemma inv_scanLL (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {l' : Loc K m}
    (hnv : (C.loc p).pc.isVal = false) (hx : (C.loc p).i = x)
    (hs : ScanOut h { C.loc p with val := C.val x } l') :
    Inv h (N + 1) ts (upd C p l' x (C.val x, if p ∈ C.lks x then C.lks x else p :: C.lks x)) := by
  obtain ⟨hop, hnv', hins, hloc, hrec⟩ := hs
  refine inv_LL_nonval hI hp hnv hop hnv' (fun h1 => by rw [(hins h1).2, hop]) hloc ?_
    (ScanOut.nisc ⟨hop, hnv', hins, hloc, hrec⟩)
  rcases hrec with h1 | h1
  · exact Or.inl h1
  · right; rw [h1, hx]

/-- A step of a scanning operation that changes nothing in memory (a plain read or a failed
`SC`). -/
lemma inv_scanStay (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {l l' : Loc K m}
    (hnv : (C.loc p).pc.isVal = false) (hl : l.op = (C.loc p).op) (hs : ScanOut0 h l l') :
    Inv h (N + 1) ts (upd C p l' x (C.val x, C.lks x)) := by
  obtain ⟨hop, hnv', hins, hloc, hrec⟩ := hs
  exact inv_stay_nonval hI hp hnv (hop.trans hl) hnv' (fun h1 => by rw [(hins h1).2, hop])
    hloc hrec (ScanOut0.nisc ⟨hop, hnv', hins, hloc, hrec⟩)

lemma upd_same (C : Cfg K m P) (p : P) (l' : Loc K m) (x : Fin m) :
    upd C p l' x (C.val x, C.lks x) = { C with loc := update C.loc p l' } := by
  simp [upd, Cfg.val, Cfg.lks]

/-- `inv_scanStay` for a step that does not touch memory at all. -/
lemma inv_scanStay' (hI : Inv h N ts C) (hp : C.pend p ≠ none) {l l' : Loc K m}
    (hnv : (C.loc p).pc.isVal = false) (hl : l.op = (C.loc p).op) (hs : ScanOut0 h l l') :
    Inv h (N + 1) ts { C with loc := update C.loc p l' } := by
  rw [← upd_same C p l' l'.i]; exact inv_scanStay hI hp hnv hl hs

/-- A successful `SC` of a non-owner into a cell that is not its own (lines 86, 88, 93). -/
lemma inv_write_nonval (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {l l' : Loc K m}
    {w' : Cell K} (hnv : (C.loc p).pc.isVal = false) (hl : l.op = (C.loc p).op)
    (hs : ScanOut0 h l l') (hsucc : p ∈ C.lks x) (hE : w' ≠ .empty)
    (hnoTt : ∀ v, w' ≠ .key v .tent) (hnoF : ∀ v, w' ≠ .key v .fin)
    (hown : ∀ q, q ≠ p → (C.loc q).pc.isVal → (C.loc q).j = x → OwnCell (C.loc q).op.key w')
    (hkey : ∀ v t, w' = .key v t → ∃ t', C.val x = .key v t' ∧ t' ≠ .fin) :
    Inv h (N + 1) ts (upd C p l' x (w', [])) := by
  obtain ⟨hop, hnv', hins, hloc, hrec⟩ := hs
  refine inv_of_write hI hp hsucc hE hnoTt hnoF hown hkey (hop.trans hl) (by rw [hnv, hnv'])
    (fun h1 => by simp [hnv'] at h1) hloc hrec ?_ (fun J _ _ h1 => by simp [hnv'] at h1) ?_
    (fun h1 => by simp [hnv'] at h1) (ScanOut0.nisc ⟨hop, hnv', hins, hloc, hrec⟩)
  · rintro (h1 | h1) c hc
    · rw [(hins h1).2, hop, hl, dist_self] at hc; exact absurd hc (Nat.not_lt_zero _)
    · simp [hnv'] at h1
  · rintro (h1 | h1 | h1) <;> simp [h1, PC.isVal] at hnv'

/-- The owner of a cell holding a tentative copy has the key of that copy. -/
lemma owner_key (hI : Inv h N ts C) {x : Fin m} {v : K} {t : Tag} (hx : C.val x = .key v t)
    (ht : t ≠ .fin) {q : P} (hq : (C.loc q).pc.isVal) (hqx : (C.loc q).j = x) :
    (C.loc q).op.key = v := by
  obtain ⟨q', h1, h2, h3⟩ := hI.own2 x v t hx ht
  rw [hI.own_inj q q' hq h1 (hqx.trans h2.symm)]; exact h3

/-- No owner holds a final copy in its cell. -/
lemma not_owner_of_fin (hI : Inv h N ts C) {x : Fin m} {v : K} (hx : C.val x = .key v .fin)
    {q : P} (hq : (C.loc q).pc.isVal) (hqx : (C.loc q).j = x) : False := by
  rcases hI.own q hq with h1 | h1 | h1 | h1 <;> rw [hqx, hx] at h1 <;> cases h1

variable {C' : Cfg K m P}

lemma tau_fsLL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .fsLL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  exact inv_scanLL hI hp (by simp [hpc, PC.isVal]) rfl (scanOut_fsBody h _)

lemma tau_bsLL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .bsLL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  exact inv_scanLL hI hp (by simp [hpc, PC.isVal]) rfl (scanOut_bsBody h _)

lemma tau_tdLL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .tdLL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  exact inv_scanLL hI hp (by simp [hpc, PC.isVal]) rfl (scanOut_tdBody h _)

lemma tau_vcRD (hI : Inv h N ts C) (hpc : (C.loc p).pc = .vcRD)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  exact inv_scanStay' hI hp (by simp [hpc, PC.isVal]) rfl (scanOut0_vcRet h _ _)

lemma tau_vcSC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .vcSC)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  have hl := hI.loc p; simp only [LocInv, hpc] at hl
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · have hx : C.val (C.loc p).i = .key (C.loc p).op.key .tent :=
      (hI.link p _ _ (by simp [recorded, hpc]) hsc).trans hl
    simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true]
    refine inv_write_nonval hI hp hnv rfl (scanOut0_vcRet h _ _) hsc (by simp) (by simp)
      (by simp) ?_ ?_
    · intro q _ hq hqx; rw [owner_key hI hx (by simp) hq hqx]; simp [OwnCell]
    · intro v t hw; simp only [Cell.key.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact ⟨.tent, hx, by simp⟩
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    exact inv_scanStay hI hp hnv rfl (l := C.loc p)
      (by simp [ScanOut0, PC.isVal, PC.isIns, LocInv, recorded])

lemma tau_tdSCF (hI : Inv h N ts C) (hpc : (C.loc p).pc = .tdSCF)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  have hl := hI.loc p; simp only [LocInv, hpc] at hl
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · have hx : C.val (C.loc p).i = .key (C.loc p).op.key .fin :=
      (hI.link p _ _ (by simp [recorded, hpc]) hsc).trans hl
    simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true]
    refine inv_write_nonval hI hp hnv rfl (scanOut0_tdRet h _ _) hsc (by simp) (by simp)
      (by simp) ?_ (by simp)
    intro q _ hq hqx; exact (not_owner_of_fin hI hx hq hqx).elim
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    exact inv_scanStay hI hp hnv rfl (scanOut0_tdRet h _ _)

lemma tau_tdSCD (hI : Inv h N ts C) (hpc : (C.loc p).pc = .tdSCD)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  simp [Impl.step, impl, act, hpc] at hs
  obtain ⟨hp, rfl⟩ := hs
  have hnv : (C.loc p).pc.isVal = false := by simp [hpc, PC.isVal]
  by_cases hsc : p ∈ C.lks (C.loc p).i
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true]
    exact inv_write_nonval hI hp hnv rfl (scanOut0_tdRet h _ _) hsc (by simp) (by simp)
      (by simp) (fun q _ _ _ => by simp [OwnCell]) (by simp)
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    exact inv_scanStay hI hp hnv rfl (l := C.loc p)
      (by simp [ScanOut0, PC.isVal, PC.isIns, LocInv, recorded])

end Podc.LockFreeLinearProbing
